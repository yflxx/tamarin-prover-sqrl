{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

-- Export SAPIC processes to Squirrel.

module SquirrelExport
  ( prettySquirrelTheory,
  )
where

import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
import Control.Exception (IOException, evaluate, try)
import Data.ByteString.Char8 qualified as BC
import Data.Char
import Data.List as List
import Data.Map qualified as M
import Data.Maybe
import Data.Set qualified as S
import Numeric (showHex)
import RuleTranslation (ppFunSym)
import Sapic.Annotation
import Sapic.Report
import Sapic.SecretChannels
import Sapic.States
import Sapic.Typing
import System.IO.Unsafe
import System.IO.Error (ioeGetErrorString)
import Term.SubtermRule (CtxtStRule (..), StRhs (..))
import Text.PrettyPrint.Class
import Theory
import Theory.Module (ModuleType (..))
import Theory.Sapic
import Theory.Text.Pretty

translationFail :: String -> a
-- Pure renderers use this so recoverable callers can catch failures after
-- forcing the rendered output.
translationFail s = unsafePerformIO (fail s)

data SquirrelContext = SquirrelContext
  { -- Predicates from the source theory, used when conditions or lemmas need
    -- expansion before printing.
    predicates :: [Predicate],
    -- Builtins enabled by the Tamarin theory.
    squirrelTheoryBuiltins :: S.Set String,
    -- Event name to payload arity.
    squirrelEventArities :: M.Map String Int,
    -- Named process definitions and their parameter counts.
    squirrelProcessArities :: M.Map String Int,
    -- Index-typed variables that have been received or computed as messages.
    messageBoundIndexVars :: S.Set SapicLVar,
    -- Readable, collision-free names for variables in the current process.
    squirrelVarNames :: M.Map LVar String
  }

-- A rendered fragment plus the declarations and warnings it needs.
data SquirrelRender = SquirrelRender
  { -- The generated Squirrel syntax for the current fragment.
    squirrelDoc :: Doc,
    -- Warnings to print in the generated file.
    squirrelWarnings :: [String],
    -- Abstract functions needed by rendered terms, with their maximum arity.
    squirrelFunDecls :: M.Map String Int,
    -- Public constants needed by rendered terms.
    squirrelConstDecls :: S.Set String,
    -- Fresh names that need Squirrel declarations.
    squirrelNameDecls :: S.Set String,
    -- Mutable state symbols and their index arities.
    squirrelStateDecls :: M.Map String Int,
    -- Mutex symbols and their index arities.
    squirrelMutexDecls :: M.Map String Int,
    -- Whether the output needs WeakSecrecy and global lemma syntax.
    squirrelNeedsWeakSecrecy :: Bool,
    -- Whether this global formula already has its wrapper.
    squirrelGlobalNoParens :: Bool,
    -- User equations that were skipped.
    squirrelSkippedEquations :: S.Set Int,
    -- Selected lemmas that were skipped.
    squirrelSkippedLemmas :: S.Set String
  }

data SquirrelFormulaStyle
  = SquirrelLocalFormula
  | SquirrelGlobalFormula
  deriving (Eq)

emptySquirrelRender :: Doc -> SquirrelRender
emptySquirrelRender d =
  SquirrelRender
    { squirrelDoc = d,
      squirrelWarnings = [],
      squirrelFunDecls = M.empty,
      squirrelConstDecls = S.empty,
      squirrelNameDecls = S.empty,
      squirrelStateDecls = M.empty,
      squirrelMutexDecls = M.empty,
      squirrelNeedsWeakSecrecy = False,
      squirrelGlobalNoParens = False,
      squirrelSkippedEquations = S.empty,
      squirrelSkippedLemmas = S.empty
    }

mergeMaxMaps :: Ord k => [M.Map k Int] -> M.Map k Int
mergeMaxMaps = M.unionsWith max

mergeSquirrelMetadata :: [SquirrelRender] -> SquirrelRender
mergeSquirrelMetadata renders =
  SquirrelRender
    { squirrelDoc = emptyDoc,
      squirrelWarnings = concatMap squirrelWarnings renders,
      squirrelFunDecls = mergeMaxMaps (map squirrelFunDecls renders),
      squirrelConstDecls = S.unions (map squirrelConstDecls renders),
      squirrelNameDecls = S.unions (map squirrelNameDecls renders),
      squirrelStateDecls = mergeMaxMaps (map squirrelStateDecls renders),
      squirrelMutexDecls = mergeMaxMaps (map squirrelMutexDecls renders),
      squirrelNeedsWeakSecrecy = or (map squirrelNeedsWeakSecrecy renders),
      squirrelGlobalNoParens = False,
      squirrelSkippedEquations = S.unions (map squirrelSkippedEquations renders),
      squirrelSkippedLemmas = S.unions (map squirrelSkippedLemmas renders)
    }

renderFromParts :: Doc -> [SquirrelRender] -> SquirrelRender
renderFromParts d renders = (mergeSquirrelMetadata renders) {squirrelDoc = d}

withWarnings :: [String] -> SquirrelRender -> SquirrelRender
withWarnings warnings rendered =
  rendered {squirrelWarnings = warnings ++ squirrelWarnings rendered}

withFunDecl :: String -> Int -> SquirrelRender -> SquirrelRender
withFunDecl name arity rendered =
  rendered {squirrelFunDecls = M.insertWith max name arity (squirrelFunDecls rendered)}

withWeakSecrecy :: SquirrelRender -> SquirrelRender
withWeakSecrecy rendered =
  rendered {squirrelNeedsWeakSecrecy = True}

withGlobalNoParens :: SquirrelRender -> SquirrelRender
withGlobalNoParens rendered =
  rendered {squirrelGlobalNoParens = True}

withSkippedEquation :: Int -> SquirrelRender -> SquirrelRender
withSkippedEquation index rendered =
  rendered {squirrelSkippedEquations = S.insert index (squirrelSkippedEquations rendered)}

withSkippedLemma :: String -> SquirrelRender -> SquirrelRender
withSkippedLemma name rendered =
  rendered {squirrelSkippedLemmas = S.insert name (squirrelSkippedLemmas rendered)}

withStateDecl :: String -> Int -> SquirrelRender -> SquirrelRender
withStateDecl name arity rendered =
  rendered {squirrelStateDecls = M.insertWith max name arity (squirrelStateDecls rendered)}

withMutexDecl :: String -> Int -> SquirrelRender -> SquirrelRender
withMutexDecl name arity rendered =
  rendered {squirrelMutexDecls = M.insertWith max name arity (squirrelMutexDecls rendered)}

data SquirrelBuiltinStmt = SquirrelBuiltinStmt
  { -- Stable key for deduplicating builtin declarations.
    builtinStmtKey :: String,
    -- The Squirrel statement to emit.
    builtinStmtDoc :: Doc
  }

-- Squirrel and Tamarin builtins do not line up exactly, so lossy translations
-- carry warnings.
data BuiltinTranslation = BuiltinTranslation
  { -- Squirrel statements needed for this builtin.
    builtinTranslationStmts :: [SquirrelBuiltinStmt],
    -- Symbols provided by those statements.
    builtinTranslationNames :: S.Set String,
    -- Warnings to print near the top of the generated file.
    builtinTranslationWarnings :: [String]
  }

accurateBuiltin :: [SquirrelBuiltinStmt] -> [String] -> BuiltinTranslation
accurateBuiltin stmts names =
  BuiltinTranslation
    { builtinTranslationStmts = stmts,
      builtinTranslationNames = S.fromList names,
      builtinTranslationWarnings = []
    }

bestEffortBuiltin :: [SquirrelBuiltinStmt] -> [String] -> String -> BuiltinTranslation
bestEffortBuiltin stmts names warning =
  BuiltinTranslation
    { builtinTranslationStmts = stmts,
      builtinTranslationNames = S.fromList names,
      builtinTranslationWarnings = [warning]
    }

unsupportedBuiltin :: String -> BuiltinTranslation
unsupportedBuiltin warning =
  translationFail $
    "The input file cannot be exported to Squirrel: " ++ warning

builtinStmt :: String -> Doc -> SquirrelBuiltinStmt
builtinStmt = SquirrelBuiltinStmt

builtins :: String -> BuiltinTranslation
-- Map Tamarin builtins to the closest Squirrel declarations.
builtins "diffie-hellman" =
  bestEffortBuiltin
    [ builtinStmt "dh-group" (text "gdh g, (^) where group:message exponents:message.")
    ]
    ["g"]
    "Using best-effort translation for diffie-hellman in Squirrel export."
builtins "dest-pairing" =
  accurateBuiltin [] []
builtins "dest-symmetric-encryption" =
  builtins "symmetric-encryption"
builtins "dest-asymmetric-encryption" =
  builtins "asymmetric-encryption"
builtins "dest-signing" =
  builtins "signing"
builtins "locations-report" =
  accurateBuiltin
    [ builtinStmt "rep-decl" (ppSquirrelBuiltinFunDecl "rep" 2 "message"),
      builtinStmt "check-rep-decl" (ppSquirrelBuiltinFunDecl "check_rep" 2 "message"),
      builtinStmt "get-rep-decl" (ppSquirrelBuiltinFunDecl "get_rep" 1 "message"),
      builtinStmt "check-rep-ax" (ppSquirrelAnyAxiom "check_rep_rep" [("m", "message"), ("loc", "message")] (text "check_rep(rep(m, loc), loc) = m")),
      builtinStmt "get-rep-ax" (ppSquirrelAnyAxiom "get_rep_rep" [("m", "message"), ("loc", "message")] (text "get_rep(rep(m, loc)) = m"))
    ]
    ["rep", "check_rep", "get_rep"]
builtins "natural-numbers" =
  unsupportedBuiltin "natural-numbers is not supported in Squirrel export."
builtins "reliable-channel" =
  accurateBuiltin [] []
builtins "xor" =
  accurateBuiltin [] ["xor", "zero"]
builtins "hashing" =
  accurateBuiltin
    [ builtinStmt "h-decl" (text "hash hash_fn.") ]
    ["hash_fn"]
builtins "asymmetric-encryption" =
  bestEffortBuiltin
    [ builtinStmt "aenc-decl" (text "aenc asym_enc, asym_dec, asym_pk."),
      builtinStmt "aenc-rnd-decl" (text "name arnd : message.")
    ]
    ["asym_enc", "asym_dec", "asym_pk", "arnd"]
    "Asymmetric encryption uses one fixed Squirrel name for implicit Tamarin randomness."
builtins "signing" =
  accurateBuiltin
    [ builtinStmt "signature-decl" (text "signature sig_sign, sig_verify, sig_pk.") ]
    ["sig_sign", "sig_verify", "sig_pk"]
builtins "revealing-signing" =
  accurateBuiltin
    [ builtinStmt "signature-decl" (text "signature sig_sign, sig_verify, sig_pk."),
      builtinStmt "reveal-sign-decl" (ppSquirrelBuiltinFunDecl "revealSign" 2 "message"),
      builtinStmt "reveal-verify-decl" (ppSquirrelBuiltinFunDecl "revealVerify" 3 "bool"),
      builtinStmt "get-message-decl" (ppSquirrelBuiltinFunDecl "getMessage" 1 "message"),
      builtinStmt "reveal-verify-ax" (ppSquirrelAnyAxiom "reveal_verify_sign" [("m", "message"), ("sk", "message")] (text "revealVerify(revealSign(m, sk), m, sig_pk(sk)) = true")),
      builtinStmt "get-message-ax" (ppSquirrelAnyAxiom "getMessage_revealSign" [("m", "message"), ("sk", "message")] (text "getMessage(revealSign(m, sk)) = m"))
    ]
    ["sig_sign", "sig_verify", "sig_pk", "revealSign", "revealVerify", "getMessage"]
builtins "symmetric-encryption" =
  bestEffortBuiltin
    [ builtinStmt "senc-decl" (text "senc sym_enc, sym_dec."),
      builtinStmt "senc-rnd-decl" (text "name srnd : message.")
    ]
    ["sym_enc", "sym_dec", "srnd"]
    "Symmetric encryption uses one fixed Squirrel name for implicit Tamarin randomness."
builtins "multiset" =
  unsupportedBuiltin
    "Multiset is not supported in Squirrel. If you want to model natural numbers, you can use the dedicated Tamarin builtin."
builtins "bilinear-pairing" =
  unsupportedBuiltin
    "Bilinear pairings are not supported in Squirrel."
builtins x =
  unsupportedBuiltin ("unsupported builtin declaration " ++ x ++ ".")

collectBuiltinDecls :: [String] -> ([Doc], S.Set String, [String])
-- Keep builtin declarations in source order, but emit each statement once.
collectBuiltinDecls = finalize . foldl' collect (S.empty, [], S.empty, [])
  where
    collect (seenStmtKeys, declsRev, names, warns) builtinName =
      let tr = builtins builtinName
          (seenStmtKeys', declsRev') = addStmts seenStmtKeys declsRev (builtinTranslationStmts tr)
       in (seenStmtKeys', declsRev', names `S.union` builtinTranslationNames tr, warns ++ builtinTranslationWarnings tr)

    addStmts seen decls = foldl' addStmt (seen, decls)

    addStmt (seen, decls) stmt
      | builtinStmtKey stmt `S.member` seen = (seen, decls)
      | otherwise = (S.insert (builtinStmtKey stmt) seen, builtinStmtDoc stmt : decls)

    finalize (_, declsRev, names, warns) =
      ( reverse declsRev,
        names,
        warns
      )

unsupportedTheoryRules :: OpenTheory -> S.Set CtxtStRule
-- Only user equations not covered by supported builtins need exporting.
unsupportedTheoryRules thy =
  stRules thy._thySignature._sigMaudeInfo `S.difference` supportedRules
  where
    supportedRules =
      S.unions $
        stRules (minimalMaudeSig False) :
        map (maybe S.empty stRules . supportedBuiltinSig) (theoryBuiltins thy)

supportedBuiltinSig :: String -> Maybe MaudeSig
-- Maude rules already covered by builtin translations.
supportedBuiltinSig "diffie-hellman" = Just dhMaudeSig
supportedBuiltinSig "dest-pairing" = Just pairDestMaudeSig
supportedBuiltinSig "dest-symmetric-encryption" = Just symEncDestMaudeSig
supportedBuiltinSig "dest-asymmetric-encryption" = Just asymEncDestMaudeSig
supportedBuiltinSig "dest-signing" = Just signatureDestMaudeSig
supportedBuiltinSig "locations-report" = Just locationReportMaudeSig
supportedBuiltinSig "reliable-channel" = Nothing
supportedBuiltinSig "xor" = Just xorMaudeSig
supportedBuiltinSig "hashing" = Just hashMaudeSig
supportedBuiltinSig "asymmetric-encryption" = Just asymEncMaudeSig
supportedBuiltinSig "signing" = Just signatureMaudeSig
supportedBuiltinSig "revealing-signing" = Just revealSignatureMaudeSig
supportedBuiltinSig "symmetric-encryption" = Just symEncMaudeSig
supportedBuiltinSig _ = Nothing

prettySquirrelTheory ::
  Bool ->
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  (OpenTheory, TypingEnvironment) ->
  IO Doc
-- Entry point for the export frontend:
--
--   1. annotate and render processes;
--   2. render equations and selected lemmas;
--   3. collect declarations needed by the rendered fragments;
--   4. assemble the Squirrel file in declaration-before-use order.
prettySquirrelTheory noReuse lemSel (thy, typEnv) =
  case theoryProcesses thy of
    [] -> pure $ text "(* No SAPIC process found. *)"
    [pr] -> do
      let p = makeAnnotations thy pr
          processDefs = theoryProcessDefs thy
          eventArities =
            mergeEventArities $
              collectProcessEvents p
                : map (\pdef -> collectProcessEvents (makeAnnotations thy pdef._pBody)) processDefs
          processArities = squirrelProcessAritiesFromDefs processDefs
          _hasStates = hasBoundUnboundStates p
          tc =
            SquirrelContext
              { predicates = theoryPredicates thy,
                squirrelTheoryBuiltins = S.fromList (theoryBuiltins thy),
                squirrelEventArities = eventArities,
                squirrelProcessArities = processArities,
                messageBoundIndexVars = S.empty,
                squirrelVarNames = M.empty
              }
          processTc = withSquirrelProcessVarNames tc [] p
          rendered = ppSquirrel processTc p
          procDefRendered = map (ppSquirrelProcessDef tc thy) processDefs
      equationRendered <- mapM (uncurry (ppSquirrelEquationOrWarning tc)) (zip [(1 :: Int) ..] (squirrelEquationRules thy))
      lemmaRendered <- mapM (ppSquirrelLemmaOrWarning tc typEnv) (squirrelLemmas noReuse lemSel thy)
      let
          renderedAll = foldl mergeSquirrelRenders rendered (map snd procDefRendered ++ equationRendered ++ lemmaRendered)
          -- Infer declarations from rendered output, then filter builtins.
          (builtinDecls, builtinNames, builtinWarnings) = collectBuiltinDecls (theoryBuiltins thy)
          warningDocs =
            map
              (\w -> text "(* WARNING: " <> text w <> text " *)")
              (List.nub (skippedContentSummaryWarnings renderedAll ++ builtinWarnings ++ squirrelWarnings renderedAll))
          eventPayloadNames = S.fromList (map squirrelEventPayloadNameFromName (M.keys eventArities))
          eventPayloadDecls = map ppSquirrelEventPayloadDecl (M.toList eventArities)
          funDecls = map ppSquirrelFunDecl (M.toList (M.filterWithKey (\k _ -> not (isSquirrelBuiltinSymbol k) && not (k `S.member` eventPayloadNames) && not (k `S.member` squirrelConstDecls renderedAll) && not (k `S.member` builtinNames)) (squirrelFunDecls renderedAll)))
          constDecls = map ppSquirrelConstDecl (S.toList (S.filter (\k -> not (isSquirrelBuiltinSymbol k) && not (k `S.member` builtinNames)) (S.delete "pub_chan" (squirrelConstDecls renderedAll))))
          nameDecls = map ppSquirrelNameDecl (S.toList (S.filter (not . isSquirrelBuiltinSymbol) (squirrelNameDecls renderedAll)))
          stateInitDecls = map ppSquirrelStateInitDecl (M.toList (squirrelStateDecls renderedAll))
          stateDecls = map ppSquirrelStateDecl (M.toList (squirrelStateDecls renderedAll))
          statePresenceDecls = map ppSquirrelStatePresenceDecl (M.toList (squirrelStateDecls renderedAll))
          mutexDecls = map ppSquirrelMutexDecl (M.toList (squirrelMutexDecls renderedAll))
          procDefDocs = map fst procDefRendered
          equationDocs = map squirrelDoc equationRendered
          lemmaDocs = map squirrelDoc lemmaRendered
          comments = [text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy]
          preludeDocs =
            [ text "include Core."
            ]
              ++ [text "include WeakSecrecy." | squirrelNeedsWeakSecrecy renderedAll]
              ++ [text "channel pub_chan."]
          declDocs =
            builtinDecls
              ++ constDecls
              ++ eventPayloadDecls
              ++ nameDecls
              ++ funDecls
              ++ equationDocs
              ++ stateInitDecls
              ++ stateDecls
              ++ statePresenceDecls
              ++ mutexDecls
          mainProcessDocs =
            -- The top-level SAPIC process becomes the executable Squirrel system.
            [ text "",
              text "system" <-> squirrelDoc rendered <> text "."
            ]
          theoryDocs =
            warningDocs
              ++ preludeDocs
              ++ declDocs
              ++ [text ""]
              ++ procDefDocs
              ++ mainProcessDocs
              ++ lemmaDocs
              ++ comments
      pure (vcat theoryDocs)
    _ ->
      translationFail
        "The input file cannot be exported to Squirrel: multiple SAPIC processes were defined; Squirrel export currently supports exactly one top-level process."

mergeEventArities :: [M.Map String Int] -> M.Map String Int
-- Event names must have one arity across the theory.
mergeEventArities =
  M.unionsWith
    ( \l r ->
        if l == r
          then l
          else translationFail "The input file cannot be exported to Squirrel: SAPIC events with the same name and different arities are not supported."
    )

collectProcessEvents :: LProcess ann -> M.Map String Int
-- Record the payload arity of every SAPIC event in a process.
collectProcessEvents (ProcessNull _) = M.empty
collectProcessEvents (ProcessAction (Event (Fact tag _ ts)) _ p) =
  M.insertWith
    ( \l r ->
        if l == r
          then l
          else translationFail "The input file cannot be exported to Squirrel: SAPIC events with the same name and different arities are not supported."
    )
    (factTagName tag)
    (length ts)
    (collectProcessEvents p)
collectProcessEvents (ProcessAction _ _ p) = collectProcessEvents p
collectProcessEvents (ProcessComb _ _ pl pr) =
  mergeEventArities [collectProcessEvents pl, collectProcessEvents pr]

squirrelEquationRules :: OpenTheory -> [CtxtStRule]
squirrelEquationRules = S.toList . unsupportedTheoryRules

squirrelLemmas ::
  Bool ->
  (ProtoLemma LNFormula ProofSkeleton -> Bool) ->
  OpenTheory ->
  [ProtoLemma LNFormula ProofSkeleton]
-- Apply the frontend selector and keep lemmas meant for Squirrel.
squirrelLemmas noReuse lemSel thy = filter isApplicableLemma (theoryLemmas thy)
  where
    isApplicableLemma lem =
      lemSel lem
        && not (noReuse && (ReuseLemma `elem` lem._lAttributes || SourceLemma `elem` lem._lAttributes))
        && moduleCondition lem

    moduleCondition lem =
      let modules = concat [ls | LemmaModule ls <- lem._lAttributes]
       in null modules || ModuleSquirrel `elem` modules

squirrelProcessAritiesFromDefs :: [ProcessDef] -> M.Map String Int
squirrelProcessAritiesFromDefs =
  M.fromList . map (\pdef -> (pdef._pName, length (fromMaybe [] pdef._pVars)))

skippedContentSummaryWarnings :: SquirrelRender -> [String]
-- Add short summaries before the detailed per-item warnings.
skippedContentSummaryWarnings rendered =
  [ "Skipped "
      ++ show equationCount
      ++ " user-defined "
      ++ plural equationCount "equation"
      ++ " during Squirrel export; see per-equation warnings for details."
    | equationCount > 0
  ]
    ++ [ "Skipped "
           ++ show lemmaCount
           ++ " selected Tamarin "
           ++ plural lemmaCount "lemma"
           ++ " during Squirrel export; see per-lemma warnings for details."
         | lemmaCount > 0
       ]
  where
    equationCount = S.size (squirrelSkippedEquations rendered)
    lemmaCount = S.size (squirrelSkippedLemmas rendered)

plural :: Int -> String -> String
plural 1 word = word
plural _ word = word ++ "s"

ppSquirrelProcessDef :: SquirrelContext -> OpenTheory -> ProcessDef -> (Doc, SquirrelRender)
-- Print a named SAPIC process as a Squirrel `process` declaration.
ppSquirrelProcessDef tc thy pdef =
  let body = makeAnnotations thy (pdef._pBody)
      vars = fromMaybe [] (pdef._pVars)
      procTc = withSquirrelProcessVarNames tc vars body
      params = if null vars then emptyDoc else parens (fsep (punctuate comma (map (ppSquirrelProcParam procTc) vars)))
      (bodyDoc, bodyRender) =
        case ppSquirrelLeafProcess procTc body of
          Just rendered -> (squirrelDoc rendered, rendered)
          Nothing ->
            let r = ppSquirrel procTc body
             in (squirrelDoc r, r)
      doc = text "process " <> text (sanitizeSquirrelProcessName pdef._pName) <> params <> text " =" $$ nest 2 bodyDoc <> text "."
   in (doc, bodyRender)

ppSquirrelProcParam :: SquirrelContext -> SapicLVar -> Doc
ppSquirrelProcParam tc v = ppUnTypeVar tc v <> text ":" <> text (ppSquirrelVarType v)

ppSquirrelProcessCall :: SquirrelContext -> String -> [SapicTerm] -> SquirrelRender
-- Keep calls to named processes as calls, after checking their arity.
ppSquirrelProcessCall tc name args =
  case M.lookup name (squirrelProcessArities tc) of
    Nothing ->
      translationFail $
        "The input file cannot be exported to Squirrel: process call references an unknown process definition: "
          ++ name
    Just expected
      | expected /= length args ->
          translationFail $
            "The input file cannot be exported to Squirrel: process call "
              ++ name
              ++ " has "
              ++ show (length args)
              ++ " "
              ++ plural (length args) "argument"
              ++ " but the process definition expects "
              ++ show expected
              ++ "."
      | otherwise ->
          let renderedArgs = map (ppSquirrelTerm tc) args
              callArgs =
                case renderedArgs of
                  [] -> emptyDoc
                  _ -> parens (fsep (punctuate comma (map squirrelDoc renderedArgs)))
           in renderFromParts (text (sanitizeSquirrelProcessName name) <> callArgs) renderedArgs

ppSquirrelVarType :: SapicLVar -> String
-- Normalize the few SAPIC type annotations Squirrel needs here.
ppSquirrelVarType (SapicLVar _ (Just "index")) = "index"
ppSquirrelVarType (SapicLVar _ (Just "node")) = "timestamp"
ppSquirrelVarType _ = "message"

squirrelEventSuffixName :: String -> String
-- Use one sanitized suffix for all generated symbols belonging to an event.
squirrelEventSuffixName = sanitizeSquirrelSymbol 'e'

squirrelEventSuffix :: FactTag -> String
squirrelEventSuffix tag = squirrelEventSuffixName (factTagName tag)

squirrelEventLabelName :: FactTag -> String
squirrelEventLabelName tag = squirrelEventSuffix tag

squirrelEventMacroName :: FactTag -> String
squirrelEventMacroName tag = "event_payload_" ++ squirrelEventSuffix tag

squirrelEventTagNameFromName :: String -> String
squirrelEventTagNameFromName eventName = "event_tag_" ++ squirrelEventSuffixName eventName

squirrelEventPayloadNameFromName :: String -> String
squirrelEventPayloadNameFromName eventName = "event_" ++ squirrelEventSuffixName eventName

squirrelEventPayloadName :: FactTag -> String
squirrelEventPayloadName tag = squirrelEventPayloadNameFromName (factTagName tag)

ppSquirrelApply :: String -> [Doc] -> Doc
ppSquirrelApply name [] = text name
ppSquirrelApply name args = text name <> parens (fsep (punctuate comma args))

ppSquirrelMacroAt :: String -> Doc -> Doc
ppSquirrelMacroAt name timestamp = text name <> text "@" <> opParens timestamp

ppSquirrelMacroAtWithStyle :: SquirrelFormulaStyle -> String -> Doc -> Doc
-- Local and global formulas spell timestamped macro access differently.
ppSquirrelMacroAtWithStyle SquirrelGlobalFormula name timestamp =
  text name <> text "@" <> timestamp
ppSquirrelMacroAtWithStyle SquirrelLocalFormula name timestamp =
  ppSquirrelMacroAt name timestamp

ppSquirrelEventPayload :: FactTag -> [SquirrelRender] -> SquirrelRender
-- Build the transparent payload term used by process events and lemmas.
ppSquirrelEventPayload tag args =
  withFunDecl (squirrelEventPayloadName tag) (length args) $
    renderFromParts
      (ppSquirrelApply (squirrelEventPayloadName tag) (map squirrelDoc args))
      args

eventPayloadLetWarning :: String
eventPayloadLetWarning =
  "SAPIC events are translated to let-bound payloads in the Squirrel export; no event payload is output on pub_chan."

ppSquirrelLeafProcess :: SquirrelContext -> LProcess (ProcessAnnotation LVar) -> Maybe SquirrelRender
-- A process definition may be a single `out` without an explicit `null`.
ppSquirrelLeafProcess tc (ProcessAction (ChOut ch msg) an (ProcessNull _)) =
  let chRender = ppSquirrelChan an ch
      rendered = ppSquirrelTerm tc msg
   in Just $
        renderFromParts
          (text "out(" <> squirrelDoc chRender <> text ", " <> squirrelDoc rendered <> text ")")
          [chRender, rendered]
ppSquirrelLeafProcess _ _ = Nothing

makeAnnotations :: OpenTheory -> PlainProcess -> LProcess (ProcessAnnotation LVar)
-- Normalize a SAPIC process before Squirrel-specific rendering.
makeAnnotations thy p = res
  where
    -- Keep report rewriting before pure-state annotation; it may change terms.
    p' = report $ annotateSecretChannels $ toAnProcess p
    res = annotatePureStates p'
    report pr =
      if isNothing (List.find (== "locations-report") (theoryBuiltins thy))
        then pr
        else translateTermsReport pr

ppSquirrelTypeArrow :: Int -> String -> String
-- Squirrel uses curried unary functions and tupled domains for larger arities.
ppSquirrelTypeArrow 0 resultTy = resultTy
ppSquirrelTypeArrow 1 resultTy = "message -> " ++ resultTy
ppSquirrelTypeArrow arity resultTy = intercalate " * " (replicate arity "message") ++ " -> " ++ resultTy

ppSquirrelBuiltinFunDecl :: String -> Int -> String -> Doc
ppSquirrelBuiltinFunDecl n arity resultTy =
  text "abstract "
    <> text n
    <> text " : "
    <> text (ppSquirrelTypeArrow arity resultTy)
    <> text "."

ppSquirrelAnyAxiom :: String -> [(String, String)] -> Doc -> Doc
ppSquirrelAnyAxiom name binders body =
  text "axiom [any] "
    <> text name
    <> text " "
    <> parens (fsep (punctuate comma [text v <> text ":" <> text ty | (v, ty) <- binders]))
    <> text ": "
    <> body
    <> text "."

ppSquirrelConstDecl :: String -> Doc
ppSquirrelConstDecl n = text "abstract " <> text n <> text " : message."

ppSquirrelNameDecl :: String -> Doc
ppSquirrelNameDecl n = text "name " <> text n <> text " : message."

ppSquirrelFunDecl :: (String, Int) -> Doc
ppSquirrelFunDecl (n, arity) =
  text "abstract "
    <> text n
    <> text " : "
    <> text
      ( if arity <= 1
          then intercalate " -> " (replicate (arity + 1) "message")
          else intercalate " * " (replicate arity "message") ++ " -> message"
      )
    <> text "."

ppSquirrelEventPayloadDecl :: (String, Int) -> Doc
-- Declare the tagged payload function used for a SAPIC event.
ppSquirrelEventPayloadDecl (eventName, arity) =
  tagDecl $$ payloadDecl
  where
    tagName = squirrelEventTagNameFromName eventName
    payloadName = squirrelEventPayloadNameFromName eventName
    tagDecl = text "abstract " <> text tagName <> text " : message."
    payloadDecl
      | arity == 0 =
          text "op "
            <> text payloadName
            <> text " : message = "
            <> text tagName
            <> text "."
      | otherwise =
          text "op "
            <> text payloadName
            <> text " : "
            <> text (ppSquirrelTypeArrow arity "message")
            <-> text "="
            $$ nest
              2
              ( text "fun "
                  <> ppSquirrelEventPayloadBinder arity
                  <-> text "=>"
                  $$ nest 2 (ppSquirrelTransparentEventPayload tagName arity <> text ".")
              )

ppSquirrelEventPayloadBinder :: Int -> Doc
ppSquirrelEventPayloadBinder 1 = text "(x1 : message)"
ppSquirrelEventPayloadBinder arity =
  text "(("
    <> fsep (punctuate comma (ppSquirrelEventPayloadVars arity))
    <> text ") : "
    <> text (intercalate " * " (replicate arity "message"))
    <> text ")"

ppSquirrelTransparentEventPayload :: String -> Int -> Doc
-- Encode event payloads as a tag paired with nested arguments.
ppSquirrelTransparentEventPayload tagName arity =
  case ppSquirrelEventPayloadVars arity of
    [] -> text tagName
    vars -> text "<" <> text tagName <> text ", " <> ppSquirrelNestedPair vars <> text ">"

ppSquirrelEventPayloadVars :: Int -> [Doc]
ppSquirrelEventPayloadVars arity = [text ("x" ++ show i) | i <- [1 .. arity]]

ppSquirrelNestedPair :: [Doc] -> Doc
ppSquirrelNestedPair [] = text "empty"
ppSquirrelNestedPair [x] = x
ppSquirrelNestedPair (x : xs) = text "<" <> x <> text ", " <> ppSquirrelNestedPair xs <> text ">"

ppSquirrelStateInitDecl :: (String, Int) -> Doc
-- Give each SAPIC state cell an initial message for its Squirrel mutable.
ppSquirrelStateInitDecl (n, arity) =
  text "name " <> text (squirrelStateInitName n) <> text " : " <> text (ppSquirrelIndexArrow arity) <> text "."

ppSquirrelStateDecl :: (String, Int) -> Doc
ppSquirrelStateDecl (n, arity) =
  text "mutable "
    <> text n
    <> ppSquirrelIndexBinders arity
    <> text " : message = "
    <> text (squirrelStateInitName n)
    <> ppSquirrelIndexArgs arity
    <> text "."

ppSquirrelStatePresenceDecl :: (String, Int) -> Doc
-- Track whether a state cell is present, since mutables always have a value.
ppSquirrelStatePresenceDecl (n, arity) =
  text "mutable "
    <> text (squirrelStatePresentName n)
    <> ppSquirrelIndexBinders arity
    <> text " : bool = false."

ppSquirrelMutexDecl :: (String, Int) -> Doc
ppSquirrelMutexDecl (n, arity) = text "mutex " <> text n <> text ":" <> text (show arity) <> text "."

squirrelStateInitName :: String -> String
squirrelStateInitName n = "stinit_" ++ n

squirrelStatePresentName :: String -> String
squirrelStatePresentName n = "stp_" ++ n

ppSquirrelIndexArrow :: Int -> String
ppSquirrelIndexArrow 0 = "message"
ppSquirrelIndexArrow 1 = "index -> message"
ppSquirrelIndexArrow arity = intercalate " * " (replicate arity "index") ++ " -> message"

ppSquirrelIndexBinders :: Int -> Doc
ppSquirrelIndexBinders 0 = emptyDoc
ppSquirrelIndexBinders arity =
  parens . fsep . punctuate comma $ [text ("i" ++ show i) <> text ":index" | i <- [1 .. arity]]

ppSquirrelIndexArgs :: Int -> Doc
ppSquirrelIndexArgs 0 = emptyDoc
ppSquirrelIndexArgs arity =
  parens . fsep . punctuate comma $ [text ("i" ++ show i) | i <- [1 .. arity]]

isSquirrelBuiltinSymbol :: String -> Bool
-- Names provided by Squirrel or always-included libraries.
isSquirrelBuiltinSymbol n = n `elem` ["fst", "snd", "diff", "true", "false", "zero", "empty", "witness", "exec", "output", "input", "frame", "att"]

hasAnyBuiltin :: SquirrelContext -> [String] -> Bool
hasAnyBuiltin tc names = any (`S.member` squirrelTheoryBuiltins tc) names

hasSignatureBuiltin :: SquirrelContext -> Bool
hasSignatureBuiltin tc = hasAnyBuiltin tc ["signing", "dest-signing", "revealing-signing"]

hasRevealingSignatureBuiltin :: SquirrelContext -> Bool
hasRevealingSignatureBuiltin tc = hasAnyBuiltin tc ["revealing-signing"]

hasAsymmetricBuiltin :: SquirrelContext -> Bool
hasAsymmetricBuiltin tc = hasAnyBuiltin tc ["asymmetric-encryption", "dest-asymmetric-encryption"]

hasSymmetricBuiltin :: SquirrelContext -> Bool
hasSymmetricBuiltin tc = hasAnyBuiltin tc ["symmetric-encryption", "dest-symmetric-encryption"]

hasHashingBuiltin :: SquirrelContext -> Bool
hasHashingBuiltin tc = hasAnyBuiltin tc ["hashing"]

hasXorBuiltin :: SquirrelContext -> Bool
hasXorBuiltin tc = hasAnyBuiltin tc ["xor"]

hasLocationsReportBuiltin :: SquirrelContext -> Bool
hasLocationsReportBuiltin tc = hasAnyBuiltin tc ["locations-report"]

renderSquirrelFunName :: SquirrelContext -> String -> String
-- Translate active Tamarin builtin symbols to their Squirrel names.
renderSquirrelFunName tc n
  | n == "h" && hasHashingBuiltin tc = "hash_fn"
  | n == "senc" && hasSymmetricBuiltin tc = "sym_enc"
  | n == "sdec" && hasSymmetricBuiltin tc = "sym_dec"
  | n == "aenc" && hasAsymmetricBuiltin tc = "asym_enc"
  | n == "adec" && hasAsymmetricBuiltin tc = "asym_dec"
  | n == "pk" && (hasSignatureBuiltin tc || hasAsymmetricBuiltin tc) = renderSquirrelPkName tc
  | n == "sign" && hasSignatureBuiltin tc = "sig_sign"
  | n == "verify" && hasSignatureBuiltin tc = "sig_verify"
  | n == "revealSign" && hasRevealingSignatureBuiltin tc = "revealSign"
  | n == "revealVerify" && hasRevealingSignatureBuiltin tc = "revealVerify"
  | n == "getMessage" && hasRevealingSignatureBuiltin tc = "getMessage"
  | n == "rep" && hasLocationsReportBuiltin tc = "rep"
  | n == "check_rep" && hasLocationsReportBuiltin tc = "check_rep"
  | n == "get_rep" && hasLocationsReportBuiltin tc = "get_rep"
  | otherwise = sanitizeSquirrelFunName n

renderSquirrelPkName :: SquirrelContext -> String
-- Tamarin overloads `pk`; Squirrel needs the signing or encryption version.
renderSquirrelPkName tc
  | hasSignatureBuiltin tc && hasAsymmetricBuiltin tc =
      translationFail
        "The input file cannot be exported to Squirrel: ambiguous pk term in a theory with both signing and asymmetric encryption. Use pk only in a context where the exporter can infer sig_pk or asym_pk."
  | hasSignatureBuiltin tc = "sig_pk"
  | hasAsymmetricBuiltin tc = "asym_pk"
  | otherwise = "asym_pk"

sanitizeSquirrelSymbol :: Char -> String -> String
-- Convert a source name into a legal Squirrel identifier.
sanitizeSquirrelSymbol pre s = avoidBlockedName base
  where
    encoded = concatMap encodeSquirrelIdentChar s
    base
      | null encoded = [pre, '_']
      | isSquirrelIdentStart (head encoded) = encoded
      | otherwise = pre : "_" ++ encoded
    avoidBlockedName name
      | isSquirrelBlockedSymbol name = avoidBlockedName (pre : "_" ++ name)
      | otherwise = name

sanitizeSquirrelFunName :: String -> String
sanitizeSquirrelFunName = sanitizeSquirrelSymbol 'a'

sanitizeSquirrelProcessName :: String -> String
sanitizeSquirrelProcessName n = "proc_" ++ sanitizeSquirrelSymbol 'p' n

encodeSquirrelIdentChar :: Char -> String
encodeSquirrelIdentChar c
  | isSquirrelIdentContinue c = [c]
  | otherwise = "_x" ++ showHex (ord c) "_"

isSquirrelIdentStart :: Char -> Bool
isSquirrelIdentStart c = isAscii c && isAlpha c

isSquirrelIdentContinue :: Char -> Bool
isSquirrelIdentContinue c = isAscii c && (isAlphaNum c || c == '_' || c == '\'')

isSquirrelBlockedSymbol :: String -> Bool
isSquirrelBlockedSymbol n = n `elem` squirrelReservedSymbols || isSquirrelBuiltinSymbol n

squirrelReservedSymbols :: [String]
squirrelReservedSymbols =
  [ "abstract",
    "action",
    "aenc",
    "as",
    "assert",
    "axiom",
    "bool",
    "boolean",
    "by",
    "case",
    "channel",
    "clear",
    "const",
    "crypto",
    "cycle",
    "ddh",
    "deduce",
    "dependent",
    "diff",
    "else",
    "end",
    "equiv",
    "exact",
    "exists",
    "fa",
    "false",
    "find",
    "forall",
    "fresh",
    "fun",
    "game",
    "gdh",
    "generalize",
    "global",
    "hash",
    "have",
    "help",
    "if",
    "include",
    "index",
    "induction",
    "in",
    "intro",
    "lemma",
    "let",
    "like",
    "local",
    "localize",
    "lock",
    "message",
    "mutable",
    "mutex",
    "name",
    "namespace",
    "new",
    "nosimpl",
    "not",
    "null",
    "op",
    "open",
    "oracle",
    "out",
    "predicate",
    "print",
    "process",
    "prof",
    "rec",
    "remember",
    "repeat",
    "return",
    "revert",
    "rewrite",
    "rnd",
    "search",
    "senc",
    "seq",
    "set",
    "signature",
    "simpl",
    "splitseq",
    "system",
    "tactic",
    "then",
    "theorem",
    "timestamp",
    "time",
    "trans",
    "true",
    "try",
    "type",
    "undo",
    "unlock",
    "use",
    "var",
    "weak",
    "where",
    "when",
    "with",
    "XOR",
    "enc",
    "dec",
    "pub"
  ]

ppSquirrelPubName :: NameId -> String
ppSquirrelPubName (NameId n) = sanitizeSquirrelSymbol 'a' ("s" ++ n)

ppLVarName :: LVar -> String
-- Fallback variable rendering outside a process-specific naming context.
ppLVarName (LVar n _ 0) = sanitizeSquirrelSymbol 'a' n
ppLVarName (LVar n _ i) = sanitizeSquirrelSymbol 'a' $ n <> "_" <> show i

ppLVar :: LVar -> Doc
ppLVar = text . ppLVarName

withSquirrelProcessVarNames :: SquirrelContext -> [SapicLVar] -> LProcess ann -> SquirrelContext
-- Allocate readable, non-conflicting names for variables in this process.
withSquirrelProcessVarNames tc params process =
  tc
    { squirrelVarNames =
        allocateSquirrelVarNames
          (processReservedNames tc process)
          (processLVars params process)
    }

processLVars :: [SapicLVar] -> LProcess ann -> S.Set LVar
-- Gather explicit parameters and variables found in the process tree.
processLVars params process =
  S.map sapicLVar (S.fromList params `S.union` foldMap S.singleton process)

sapicLVar :: SapicLVar -> LVar
sapicLVar (SapicLVar lvar _) = lvar

allocateSquirrelVarNames :: S.Set String -> S.Set LVar -> M.Map LVar String
-- Deterministic allocation keeps generated files stable across runs.
allocateSquirrelVarNames reservedNames vars = fst (List.foldl' allocate (M.empty, reservedNames) ordered)
  where
    ordered = List.sortOn lvarOrderKey (S.toList vars)

    allocate (env, used) lvar =
      let name = freshReadableName (sanitizeSquirrelSymbol 'a' (readableLVarBase lvar)) used
       in (M.insert lvar name env, S.insert name used)

lvarOrderKey :: LVar -> (String, String, Integer)
lvarOrderKey lvar = (readableLVarBase lvar, lvarName lvar, lvarIdx lvar)

readableLVarBase :: LVar -> String
-- Drop numeric location prefixes such as `12_ClientKey` when possible.
readableLVarBase (LVar name _ _) =
  case stripLocationPrefix name of
    Just readable -> map toLower readable
    Nothing -> name

stripLocationPrefix :: String -> Maybe String
stripLocationPrefix name =
  case span isDigit name of
    ([], _) -> Nothing
    (_, '_' : readable) | not (null readable) -> Just readable
    _ -> Nothing

freshReadableName :: String -> S.Set String -> String
-- Pick the first unused `base`, `base_1`, ... name.
freshReadableName base used =
  head
    [ candidate
      | i <- [0 :: Int ..],
        let candidate = suffix i,
        candidate `S.notMember` used,
        not (isSquirrelBlockedSymbol candidate)
    ]
  where
    suffix 0 = base
    suffix i = base ++ "_" ++ show i

ppLVarNameWith :: SquirrelContext -> LVar -> String
ppLVarNameWith tc lvar = fromMaybe (ppLVarName lvar) (M.lookup lvar (squirrelVarNames tc))

ppLVarWith :: SquirrelContext -> LVar -> Doc
ppLVarWith tc = text . ppLVarNameWith tc

ppSapicLVarNameWith :: SquirrelContext -> SapicLVar -> String
ppSapicLVarNameWith tc (SapicLVar lvar _) = ppLVarNameWith tc lvar

ppUnTypeVar :: SquirrelContext -> SapicLVar -> Doc
ppUnTypeVar tc (SapicLVar lvar _) = ppLVarWith tc lvar

processReservedNames :: SquirrelContext -> LProcess ann -> S.Set String
-- Generated names that process variables must not shadow.
processReservedNames tc = \case
  ProcessNull _ -> S.empty
  ProcessAction action _ continuation ->
    actionReservedNames tc action `S.union` processReservedNames tc continuation
  ProcessComb comb _ left right ->
    combReservedNames tc comb
      `S.union` processReservedNames tc left
      `S.union` processReservedNames tc right

actionReservedNames :: SquirrelContext -> LSapicAction -> S.Set String
actionReservedNames tc action =
  termDeclNames tc (actionTerms action)
    `S.union` eventActionReservedNames action

actionTerms :: LSapicAction -> [SapicTerm]
actionTerms = \case
  Rep -> []
  New _ -> []
  ChIn _ msg _ -> [msg]
  ChOut _ msg -> [msg]
  Event (Fact _ _ args) -> args
  Insert cell msg -> [cell, msg]
  Delete cell -> [cell]
  Lock term -> [term]
  Unlock term -> [term]
  ProcessCall _ args -> args
  MSR {} -> []

eventActionReservedNames :: LSapicAction -> S.Set String
eventActionReservedNames (Event (Fact tag _ _)) =
  S.fromList
    [ squirrelEventLabelName tag,
      squirrelEventMacroName tag,
      squirrelEventPayloadName tag,
      squirrelEventTagNameFromName (factTagName tag)
    ]
eventActionReservedNames _ = S.empty

combReservedNames :: SquirrelContext -> ProcessCombinator SapicLVar -> S.Set String
combReservedNames tc = \case
  Parallel -> S.empty
  NDC -> S.empty
  Let patternTerm valueTerm _ -> termDeclNames tc [patternTerm, valueTerm]
  Cond _ -> S.empty
  CondEq left right -> termDeclNames tc [left, right]
  Lookup stateTerm _ -> termDeclNames tc [stateTerm]

termDeclNames :: SquirrelContext -> [SapicTerm] -> S.Set String
-- Use term-render metadata to find declaration names a term would need.
termDeclNames tc terms =
  S.unions
    [ M.keysSet (squirrelFunDecls rendered),
      squirrelConstDecls rendered,
      squirrelNameDecls rendered
    ]
  where
    rendered = mergeSquirrelMetadata (map (ppSquirrelTerm tc) terms)

isSyntheticStateChannelVar :: SapicLVar -> Bool
-- Internal pure-state channels should not appear in Squirrel output.
isSyntheticStateChannelVar (SapicLVar lvar _) = "StateChannel" `List.isPrefixOf` lvarName lvar

data SquirrelCellRef = SquirrelCellRef
  { -- Mutable name for the SAPIC state cell.
    squirrelCellName :: String,
    -- Index arguments from the cell term.
    squirrelCellArgs :: [SapicTerm]
  }

data SquirrelMutexRef = SquirrelMutexRef
  { -- Squirrel mutex name.
    squirrelMutexName :: String,
    -- Index arguments from the lock term.
    squirrelMutexArgs :: [SapicTerm]
  }
  deriving (Eq)

ppSquirrelTerm :: SquirrelContext -> SapicTerm -> SquirrelRender
ppSquirrelTerm tc = ppSquirrelTermWith tc (const True) False

ppSquirrelFormulaTerm :: SquirrelContext -> S.Set LVar -> SapicTerm -> SquirrelRender
-- In formulas, free public variables are printed as public constants.
ppSquirrelFormulaTerm tc boundVars = ppSquirrelTermWith tc renderPublicVarAsConstant True
  where
    renderPublicVarAsConstant (SapicLVar lvar _) =
      lvarSort lvar == LSortPub && lvar `S.notMember` boundVars

ppSquirrelEquationTerm :: SquirrelContext -> LNTerm -> SquirrelRender
-- Equations use plain variables, not formula-style public constants.
ppSquirrelEquationTerm tc =
  ppSquirrelTermWith tc (const False) False . mapLits (fmap (`SapicLVar` Nothing))

-- Boolean formula contexts print true/false as Squirrel booleans.
ppSquirrelTermWith :: SquirrelContext -> (SapicLVar -> Bool) -> Bool -> SapicTerm -> SquirrelRender
-- Render a SAPIC term and collect the declarations it needs.
ppSquirrelTermWith tc renderPublicVarAsConstant renderBoolConstants t =
  SquirrelRender
    { squirrelDoc = doc,
      squirrelWarnings = [],
      squirrelFunDecls = funs,
      squirrelConstDecls = consts,
      squirrelNameDecls = names,
      squirrelStateDecls = M.empty,
      squirrelMutexDecls = M.empty,
      squirrelNeedsWeakSecrecy = False,
      squirrelGlobalNoParens = False,
      squirrelSkippedEquations = S.empty,
      squirrelSkippedLemmas = S.empty
    }
  where
    (doc, funs, consts, names) = go t

    partDoc (d, _, _, _) = d
    partFuns (_, f, _, _) = f
    partConsts (_, _, c, _) = c
    partNames (_, _, _, n) = n
    partsConstDecls = S.unions . map partConsts
    partsNameDecls = S.unions . map partNames
    fromParts d parts = (d, mergeMaxMaps (map partFuns parts), partsConstDecls parts, partsNameDecls parts)
    fromPartsWithFun d f arity parts =
      (d, mergeMaxMaps (M.singleton f arity : map partFuns parts), partsConstDecls parts, partsNameDecls parts)
    withPartConst c (d, f, constDecls, nameDecls) = (d, f, S.insert c constDecls, nameDecls)

    go tm = case viewTerm tm of
      Lit (Var svar@(SapicLVar lvar@(LVar _ LSortPub _) _))
        | renderPublicVarAsConstant svar ->
            let c = "s" ++ sanitizeSquirrelSymbol 'a' (lvarName lvar) ++ "_" ++ show (lvarIdx lvar)
             in (text c, M.empty, S.singleton c, S.empty)
      Lit (Var (SapicLVar lvar _)) -> (ppLVarWith tc lvar, M.empty, S.empty, S.empty)
      Lit (Con (Name PubName n)) ->
        let c = ppSquirrelPubName n
         in (text c, M.empty, S.singleton c, S.empty)
      Lit (Con (Name FreshName n)) ->
        let c = sanitizeSquirrelSymbol 'a' (show n)
         in (text c, M.empty, S.empty, S.singleton c)
      Lit (Con c) ->
        let c' = sanitizeSquirrelSymbol 'a' (show c)
         in (text c', M.empty, S.singleton c', S.empty)
      FApp (NoEq s) [t1, t2] | s == diffSym ->
        let r1 = go t1
            r2 = go t2
         in fromPartsWithFun (text "diff(" <> partDoc r1 <> text ", " <> partDoc r2 <> text ")") "diff" 2 [r1, r2]
      FApp (NoEq s) [t1, t2] | s == expSym ->
        let r1 = go t1
            r2 = go t2
         in fromParts (parens (partDoc r1 <> text " ^ " <> partDoc r2)) [r1, r2]
      FApp (NoEq _) [t1, t2] | isPair tm ->
        let r1 = go t1
            r2 = go t2
         in fromParts (text "<" <> partDoc r1 <> text ", " <> partDoc r2 <> text ">") [r1, r2]
      FApp (AC Xor) ts ->
        goXor ts
      FApp (AC op) ts ->
        let f = sanitizeSquirrelSymbol 'a' ("ac_" ++ show op)
         in goACNested f ts
      FApp (NoEq (f, (_, Private, _))) ts
        -- locations-report exposes `rep` as an abstract Squirrel function.
        | ppFunSym f == "rep" && hasLocationsReportBuiltin tc ->
            ppFunLike "rep" ts
        | otherwise ->
            translationFail $
              "The input file cannot be exported to Squirrel: private function symbols are not supported in Squirrel export: "
                ++ BC.unpack f
      FApp (NoEq (f, _)) [] | renderBoolConstants && squirrelBoolNoEqFunName f == Just True -> (text "true", M.empty, S.empty, S.empty)
      FApp (NoEq (f, _)) [] | renderBoolConstants && squirrelBoolNoEqFunName f == Just False -> (text "false", M.empty, S.empty, S.empty)
      FApp (NoEq (f, _)) [] | ppFunSym f == "zero" && hasXorBuiltin tc -> (text "zero", M.empty, S.singleton "zero", S.empty)
      FApp (NoEq s) [] | s == natOneSym -> (text "one", M.empty, S.singleton "one", S.empty)
      FApp (NoEq (f, _)) [t1] | ppFunSym f == "h" && hasHashingBuiltin tc ->
        let r1 = go t1
            key = text "hkey"
         in withPartConst "hkey" $
              fromPartsWithFun (text "hash_fn(" <> partDoc r1 <> text ", " <> key <> text ")") "hash_fn" 2 [r1]
      FApp (NoEq (f, _)) [t1, t2] | ppFunSym f == "h" && hasHashingBuiltin tc ->
        let r1 = go t1
            r2 = go t2
         in fromPartsWithFun (text "hash_fn(" <> partDoc r1 <> text ", " <> partDoc r2 <> text ")") "hash_fn" 2 [r1, r2]
      FApp (NoEq (f, _)) [t1, t2] | ppFunSym f == "senc" && hasSymmetricBuiltin tc ->
        let r1 = go t1
            r2 = go t2
            rnd = text "srnd"
         in withPartConst "srnd" $
              fromPartsWithFun (text "sym_enc(" <> partDoc r1 <> text ", " <> rnd <> text ", " <> partDoc r2 <> text ")") "sym_enc" 3 [r1, r2]
      FApp (NoEq (f, _)) [t1, t2] | ppFunSym f == "aenc" && hasAsymmetricBuiltin tc ->
        let r1 = go t1
            r2 = goWithPk "asym_pk" t2
            rnd = text "arnd"
         in withPartConst "arnd" $
              fromPartsWithFun (text "asym_enc(" <> partDoc r1 <> text ", " <> rnd <> text ", " <> partDoc r2 <> text ")") "asym_enc" 3 [r1, r2]
      FApp (NoEq (f, _)) [sigTerm, msgTerm, pkTerm] | ppFunSym f == "verify" && hasSignatureBuiltin tc ->
        let sig = go sigTerm
            msg = go msgTerm
            pk = goWithPk "sig_pk" pkTerm
         in fromPartsWithFun (text "sig_verify(" <> partDoc msg <> text ", " <> partDoc sig <> text ", " <> partDoc pk <> text ")") "sig_verify" 3 [sig, msg, pk]
      FApp (NoEq (f, _)) [sigTerm, msgTerm, pkTerm] | ppFunSym f == "revealVerify" && hasRevealingSignatureBuiltin tc ->
        let sig = go sigTerm
            msg = go msgTerm
            pk = goWithPk "sig_pk" pkTerm
         in fromPartsWithFun (text "revealVerify(" <> partDoc sig <> text ", " <> partDoc msg <> text ", " <> partDoc pk <> text ")") "revealVerify" 3 [sig, msg, pk]
      FApp (NoEq (f, _)) ts -> ppFunLike (renderSquirrelFunName tc (ppFunSym f)) ts
      FApp (C EMap) ts -> ppFunLike (BC.unpack emapSymString) ts
      FApp List ts -> ppFunLike "list" ts

    goWithPk pkName tm =
      -- Rewrite `pk(sk)` when the surrounding builtin tells us which key kind
      -- Squirrel needs.
      case viewTerm tm of
        FApp (NoEq (f, _)) [skTerm] | ppFunSym f == "pk" ->
          let sk = go skTerm
           in fromPartsWithFun (text pkName <> text "(" <> partDoc sk <> text ")") pkName 1 [sk]
        _ -> go tm

    ppFunLike f [] =
      (text f, M.singleton f 0, S.empty, S.empty)
    ppFunLike f ts =
      let rendered = map go ts
          docs = map partDoc rendered
       in fromPartsWithFun (text f <> text "(" <> fsep (punctuate comma docs) <> text ")") f (length ts) rendered

    goACNested _ [] = (text "empty", M.empty, S.singleton "empty", S.empty)
    -- Encode unknown AC operators as deterministic binary trees.
    goACNested _ [t1] = go t1
    goACNested f [t1, t2] = ppFunLike f [t1, t2]
    goACNested f (t1 : ts) =
      let r1 = go t1
          rest = goACNested f ts
       in fromPartsWithFun (text f <> text "(" <> partDoc r1 <> text ", " <> partDoc rest <> text ")") f 2 [r1, rest]

    goXor [] = (text "zero", M.empty, S.singleton "zero", S.empty)
    -- Keep the `xor` dependency even though Squirrel has native XOR syntax.
    goXor [t1] = go t1
    goXor [t1, t2] =
      let r1 = go t1
          r2 = go t2
       in fromPartsWithFun (parens (partDoc r1 <> text " XOR " <> partDoc r2)) "xor" 2 [r1, r2]
    goXor (t1 : ts) =
      let r1 = go t1
          rest = goXor ts
       in fromPartsWithFun (parens (partDoc r1 <> text " XOR " <> partDoc rest)) "xor" 2 [r1, rest]

ppSquirrelStateAccess :: SquirrelContext -> SapicTerm -> Maybe SquirrelRender
-- Try to turn a SAPIC state-cell term into a Squirrel mutable access.
ppSquirrelStateAccess tc t = do
  cell <- squirrelStateRef tc t
  pure $
    withStateDecl
      (squirrelCellName cell)
      (length (squirrelCellArgs cell))
      (ppSquirrelRefRender tc (squirrelCellName cell) (squirrelCellArgs cell))

ppSquirrelStatePresenceAccess :: SquirrelContext -> SquirrelCellRef -> SquirrelRender
-- Access the presence flag paired with a state mutable.
ppSquirrelStatePresenceAccess tc cell =
  withStateDecl
    (squirrelCellName cell)
    (length (squirrelCellArgs cell))
    (ppSquirrelRefRender tc (squirrelStatePresentName (squirrelCellName cell)) (squirrelCellArgs cell))

ppSquirrelMutexAccess :: SquirrelContext -> SapicTerm -> Maybe SquirrelRender
-- Try to turn a SAPIC lock term into a Squirrel mutex access.
ppSquirrelMutexAccess tc t = do
  mutex <- squirrelMutexRef tc t
  pure $
    withMutexDecl
      (squirrelMutexName mutex)
      (length (squirrelMutexArgs mutex))
      (ppSquirrelRefRender tc (squirrelMutexName mutex) (squirrelMutexArgs mutex))

ppSquirrelRefRender :: SquirrelContext -> String -> [SapicTerm] -> SquirrelRender
ppSquirrelRefRender tc name args =
  let renderedArgs = map (ppSquirrelTerm tc) args
   in renderFromParts (ppSquirrelRefDoc name renderedArgs) renderedArgs

ppSquirrelRefDoc :: String -> [SquirrelRender] -> Doc
ppSquirrelRefDoc n [] = text n
ppSquirrelRefDoc n args = text n <> parens (fsep (punctuate comma (map squirrelDoc args)))

-- Only stable, structural terms can become indexed state or mutex references.
squirrelStateRef :: SquirrelContext -> SapicTerm -> Maybe SquirrelCellRef
squirrelStateRef tc t = do
  (tag, args) <- squirrelStructuredArgs tc t
  pure $ SquirrelCellRef ("st_" ++ sanitizeSquirrelSymbol 's' tag) args

squirrelMutexRef :: SquirrelContext -> SapicTerm -> Maybe SquirrelMutexRef
squirrelMutexRef tc t = do
  (tag, args) <- squirrelStructuredArgs tc t
  pure $ SquirrelMutexRef ("mtx_" ++ sanitizeSquirrelSymbol 'm' tag) args

squirrelStructuredArgs :: SquirrelContext -> SapicTerm -> Maybe (String, [SapicTerm])
-- Extract the generated name and index arguments for a state or mutex term.
squirrelStructuredArgs tc tm =
  case viewTerm tm of
    Lit (Var v@(SapicLVar _ (Just "index")))
      | v `S.member` messageBoundIndexVars tc -> Nothing
      | otherwise -> Just ("idx", [tm])
    Lit (Var _) -> Nothing
    Lit (Con (Name PubName n)) -> Just ("pub_" ++ sanitizeSquirrelSymbol 'p' (show n), [])
    Lit (Con (Name FreshName n)) -> Just ("fresh_" ++ sanitizeSquirrelSymbol 'f' (show n), [])
    Lit (Con c) -> Just ("con_" ++ sanitizeSquirrelSymbol 'c' (show c), [])
    FApp (NoEq _) [t1, t2] | isPair tm ->
      do
        (n1, a1) <- squirrelStructuredArgs tc t1
        (n2, a2) <- squirrelStructuredArgs tc t2
        pure ("pair_" ++ n1 ++ "_" ++ n2, a1 ++ a2)
    FApp (NoEq (f, _)) [] | ppFunSym f == "zero" && hasXorBuiltin tc -> Just ("zero", [])
    FApp (AC Xor) ts ->
      do
        parts <- canonicalXorStructuredParts tc <$> mapM (squirrelStructuredArgs tc) ts
        case parts of
          [] -> pure ("zero", [])
          [part] -> pure part
          _ -> pure ("ac_Xor" ++ concatMap (("_" ++) . fst) parts, concatMap snd parts)
    FApp (AC op) ts ->
      do
        parts <- canonicalStructuredParts tc <$> mapM (squirrelStructuredArgs tc) ts
        pure ("ac_" ++ sanitizeSquirrelSymbol 'a' (show op) ++ concatMap (("_" ++) . fst) parts, concatMap snd parts)
    FApp (NoEq (f, _)) ts ->
      do
        parts <- mapM (squirrelStructuredArgs tc) ts
        pure (renderSquirrelFunName tc (ppFunSym f) ++ concatMap (("_" ++) . fst) parts, concatMap snd parts)
    FApp (C EMap) ts ->
      do
        parts <- mapM (squirrelStructuredArgs tc) ts
        pure ("emap" ++ concatMap (("_" ++) . fst) parts, concatMap snd parts)
    FApp List ts ->
      do
        parts <- mapM (squirrelStructuredArgs tc) ts
        pure ("list" ++ concatMap (("_" ++) . fst) parts, concatMap snd parts)

canonicalStructuredParts :: SquirrelContext -> [(String, [SapicTerm])] -> [(String, [SapicTerm])]
-- Keep AC state-cell names independent of source argument order.
canonicalStructuredParts tc =
  List.sortBy (compareStructuredParts tc)

canonicalXorStructuredParts :: SquirrelContext -> [(String, [SapicTerm])] -> [(String, [SapicTerm])]
-- Canonicalize XOR parts with cancellation, matching Tamarin's normal form.
canonicalXorStructuredParts tc =
  mapMaybe keepOdd
    . List.groupBy samePart
    . canonicalStructuredParts tc
    . filter (not . isXorZeroPart)
  where
    samePart left right = structuredPartKey tc left == structuredPartKey tc right
    keepOdd parts
      | odd (length parts) = Just (head parts)
      | otherwise = Nothing

isXorZeroPart :: (String, [SapicTerm]) -> Bool
isXorZeroPart ("zero", []) = True
isXorZeroPart _ = False

compareStructuredParts :: SquirrelContext -> (String, [SapicTerm]) -> (String, [SapicTerm]) -> Ordering
compareStructuredParts tc left right = compare (structuredPartKey tc left) (structuredPartKey tc right)

structuredPartKey :: SquirrelContext -> (String, [SapicTerm]) -> (String, [String])
-- Rendered argument strings are only used as a stable ordering key.
structuredPartKey tc (tag, args) = (tag, map (render . squirrelDoc . ppSquirrelTerm tc) args)

ppSquirrelEventAction :: SquirrelContext -> SapicNFact SapicLVar -> Doc -> SquirrelRender
-- Represent a SAPIC event as a local payload binding.
ppSquirrelEventAction tc (Fact tag _ ts) continuationDoc
  | factTagArity tag /= length ts =
      translationFail $ "MALFORMED event fact " ++ show tag
  | otherwise =
      withWarnings [eventPayloadLetWarning] $
        renderFromParts eventDoc [payload]
  where
    renderedArgs = map (ppSquirrelTerm tc) ts
    payload = ppSquirrelEventPayload tag renderedArgs
    eventDoc =
      text "let "
        <> text (squirrelEventMacroName tag)
        <> text " = "
        <> squirrelDoc payload
        <> text " in"
        $$ continuationDoc

ppSquirrelActionWithInputBinder :: SquirrelContext -> Maybe Doc -> ProcessAnnotation LVar -> LSapicAction -> SquirrelRender
-- Render one SAPIC action; sequencing is handled by the recursive renderer.
ppSquirrelActionWithInputBinder tc inputBinder an = \case
  Rep ->
    SquirrelRender
      { squirrelDoc = text "out(pub_chan, srep_drop)",
        squirrelWarnings = ["Replication inside process bodies is not supported in Squirrel v1 export; replaced by null."],
        squirrelFunDecls = M.empty,
        squirrelConstDecls = S.singleton "srep_drop",
        squirrelNameDecls = S.empty,
        squirrelStateDecls = M.empty,
        squirrelMutexDecls = M.empty,
        squirrelNeedsWeakSecrecy = False,
        squirrelGlobalNoParens = False,
        squirrelSkippedEquations = S.empty,
        squirrelSkippedLemmas = S.empty
      }
  New v
    | isSyntheticStateChannelVar v -> emptySquirrelRender (text "null")
    | otherwise -> emptySquirrelRender (text "new " <> ppUnTypeVar tc v)
  ChIn ch msg mvars ->
    let chRender = ppSquirrelChan an ch
        binder = fromMaybe (ppSquirrelInputBinder tc (text "sq_in") msg mvars) inputBinder
     in chRender
          { squirrelDoc = text "in(" <> squirrelDoc chRender <> text ", " <> binder <> text ")"
          }
  ChOut ch msg ->
    let chRender = ppSquirrelChan an ch
        tmsg = ppSquirrelTerm tc msg
     in renderFromParts
          (text "out(" <> squirrelDoc chRender <> text ", " <> squirrelDoc tmsg <> text ")")
          [tmsg, chRender]
  Event _ ->
    translationFail "The input file cannot be exported to Squirrel: SAPIC events are not supported in Squirrel process bodies."
  Insert cell msg ->
    case squirrelStateRef tc cell of
      Just cellRef ->
        let rc = ppSquirrelStateAccess tc cell
            rp = ppSquirrelStatePresenceAccess tc cellRef
            rm = ppSquirrelTerm tc msg
         in case rc of
              Just rc' ->
                renderFromParts
                  ( squirrelDoc rc'
                      <> text " := "
                      <> squirrelDoc rm
                      <> text ";"
                      $$ squirrelDoc rp
                      <> text " := true"
                  )
                  [rc', rp, rm]
              Nothing -> unsupported "Insert on non-indexed state cells"
      Nothing -> unsupported "Insert on non-indexed state cells"
  Delete cell ->
    case squirrelStateRef tc cell of
      Just cellRef ->
        let rp = ppSquirrelStatePresenceAccess tc cellRef
         in rp {squirrelDoc = squirrelDoc rp <> text " := false"}
      Nothing -> unsupported "Delete on non-indexed state cells"
  Lock t ->
    case ppSquirrelMutexAccess tc t of
      Just rm -> rm {squirrelDoc = text "lock " <> squirrelDoc rm}
      Nothing -> unsupported "Lock on non-indexed mutexes"
  Unlock t ->
    case ppSquirrelMutexAccess tc t of
      Just rm -> rm {squirrelDoc = text "unlock " <> squirrelDoc rm}
      Nothing -> unsupported "Unlock on non-indexed mutexes"
  ProcessCall _ _ ->
    translationFail "The input file cannot be exported to Squirrel: internal error: unhandled process call action."
  MSR {} -> unsupported "MSR"
  where
    unsupported k =
      translationFail $
        "The input file cannot be exported to Squirrel: unsupported SAPIC action in Squirrel v1 export: " ++ k

mergeSquirrelRenders :: SquirrelRender -> SquirrelRender -> SquirrelRender
-- Merge metadata while keeping the first document.
mergeSquirrelRenders l r =
  (mergeSquirrelMetadata [l, r]) {squirrelDoc = squirrelDoc l}

ppSquirrelChan :: ProcessAnnotation LVar -> Maybe SapicTerm -> SquirrelRender
-- This exporter collapses supported SAPIC channels to one public channel.
ppSquirrelChan an ch =
  case ch of
    Just _
      | isJust an.secretChannel ->
          translationFail
            "The input file cannot be exported to Squirrel: always-secret SAPIC channels are not supported."
      | otherwise ->
          withWarnings
            ["Explicit SAPIC channels are mapped to pub_chan in Squirrel export."]
            (emptySquirrelRender (text "pub_chan"))
    Nothing ->
      withWarnings
        ["Implicit SAPIC channel mapped to pub_chan in Squirrel export."]
        (emptySquirrelRender (text "pub_chan"))

patternVariables :: SapicTerm -> S.Set SapicLVar
-- Variables that appear syntactically in a pattern.
patternVariables t =
  case viewTerm t of
    Lit (Var v) -> S.singleton v
    Lit _ -> S.empty
    FApp _ ts -> S.unions (map patternVariables ts)

ppSquirrelPatternGuard :: SquirrelContext -> Doc -> SapicTerm -> SquirrelRender
-- Turn a non-binding pattern fragment into an equality guard.
ppSquirrelPatternGuard tc actual expected =
  let rendered = ppSquirrelTerm tc expected
   in rendered {squirrelDoc = actual <-> text "=" <-> squirrelDoc rendered}

ppSquirrelPatternConstraints ::
  SquirrelContext ->
  S.Set SapicLVar ->
  Doc ->
  SapicTerm ->
  ([(Doc, Doc)], [SquirrelRender])
-- Convert a SAPIC input or let pattern around an already-bound message:
--
-- * nested pairs become `fst`/`snd` projections that bind fresh variables;
-- * repeated variables and variables from `mvars` become equality guards;
-- * non-pair patterns may only be checked if all variables are already known.
ppSquirrelPatternConstraints tc mvars base t =
  let (_, projections, guards) = go S.empty base t
   in (projections, guards)
  where
    -- Squirrel can project pairs, but cannot bind inside arbitrary terms here.
    go bound actual term
      | isPair term = case viewTerm term of
          FApp _ [t1, t2] ->
            let (boundLeft, leftProjections, leftGuards) =
                  go bound (text "fst(" <> actual <> text ")") t1
                (boundRight, rightProjections, rightGuards) =
                  go boundLeft (text "snd(" <> actual <> text ")") t2
             in (boundRight, leftProjections ++ rightProjections, leftGuards ++ rightGuards)
          _ -> (bound, [], [])
      | otherwise = case viewTerm term of
          Lit (Var v@(SapicLVar lvar _))
            | v `S.member` mvars -> (bound, [], [emptySquirrelRender (actual <-> text "=" <-> ppLVarWith tc lvar)])
            | v `S.member` bound -> (bound, [], [emptySquirrelRender (actual <-> text "=" <-> ppLVarWith tc lvar)])
            | otherwise -> (S.insert v bound, [(ppLVarWith tc lvar, actual)], [])
          Lit _ -> (bound, [], [ppSquirrelPatternGuard tc actual term])
          FApp _ _
            | patternVariables term `S.isSubsetOf` (mvars `S.union` bound) ->
                (bound, [], [ppSquirrelPatternGuard tc actual term])
            | otherwise ->
                translationFail
                  "The input file cannot be exported to Squirrel: non-pair patterns with newly bound variables are not supported."

wrapWithProjections :: [(Doc, Doc)] -> Doc -> Doc
-- Wrap a body in projection lets.
wrapWithProjections [] body = body
wrapWithProjections ((var, proj) : rest) body =
  text "let " <> var <> text " = " <> proj <> text " in"
    $$ wrapWithProjections rest body

wrapWithPatternGuards :: [SquirrelRender] -> Doc -> Doc
-- Wrap a branch in pattern equality guards.
wrapWithPatternGuards [] body = body
wrapWithPatternGuards (condition : rest) body =
  text "if " <> squirrelDoc condition <> text " then"
    $$ wrapBranchDoc (wrapWithPatternGuards rest body)

ppSquirrelInputBinder :: SquirrelContext -> Doc -> SapicTerm -> S.Set SapicLVar -> Doc
-- Bind simple input variables directly; use a temporary for patterns.
ppSquirrelInputBinder tc fallback msg mvars =
  case viewTerm msg of
    Lit (Var v@(SapicLVar lvar _))
      | v `S.member` mvars -> fallback
      | otherwise -> ppLVarWith tc lvar
    _ -> fallback

ppSquirrelInputPatternConstraints ::
  SquirrelContext ->
  Doc ->
  SapicTerm ->
  S.Set SapicLVar ->
  ([(Doc, Doc)], [SquirrelRender])
ppSquirrelInputPatternConstraints tc binder msg mvars =
  case viewTerm msg of
    Lit (Var v)
      | v `S.notMember` mvars -> ([], [])
    _ -> ppSquirrelPatternConstraints tc mvars binder msg

termVarNames :: SquirrelContext -> SapicTerm -> S.Set String
termVarNames tc t =
  case viewTerm t of
    Lit (Var v) -> S.singleton (ppSapicLVarNameWith tc v)
    Lit _ -> S.empty
    FApp _ ts -> S.unions (map (termVarNames tc) ts)

processVarNames :: SquirrelContext -> LProcess ann -> S.Set String
processVarNames tc = S.map (ppSapicLVarNameWith tc) . foldMap S.singleton

freshTempName :: String -> S.Set String -> Doc
freshTempName base used = text $ head [candidate | i <- [0 :: Int ..], let candidate = suffix i, candidate `S.notMember` used]
  where
    suffix 0 = base
    suffix i = base ++ "_" ++ show i

freshInputBinder :: SquirrelContext -> SapicTerm -> S.Set SapicLVar -> LProcess ann -> Doc
-- Pick a temporary input name that cannot collide with nearby variables.
freshInputBinder tc msg mvars continuation =
  ppSquirrelInputBinder tc fallback msg mvars
  where
    fallback =
      freshTempName
        "sq_in"
        (termVarNames tc msg `S.union` S.map (ppSapicLVarNameWith tc) mvars `S.union` processVarNames tc continuation)

updateContextAfterAction :: SquirrelContext -> LSapicAction -> SquirrelContext
-- Track index-typed variables that were obtained as messages.
updateContextAfterAction tc (ChIn _ msg mvars) =
  tc
    { messageBoundIndexVars =
        messageBoundIndexVars tc `S.union` inputBoundIndexVars msg mvars
    }
updateContextAfterAction tc _ = tc

updateContextAfterLet :: SquirrelContext -> SapicTerm -> S.Set SapicLVar -> SquirrelContext
updateContextAfterLet tc patternTerm mvars =
  tc
    { messageBoundIndexVars =
        messageBoundIndexVars tc `S.union` inputBoundIndexVars patternTerm mvars
    }

updateContextAfterLookup :: SquirrelContext -> SapicLVar -> SquirrelContext
-- A lookup result is a message, even if the target variable is typed as index.
updateContextAfterLookup tc v@(SapicLVar _ (Just "index")) =
  tc {messageBoundIndexVars = S.insert v (messageBoundIndexVars tc)}
updateContextAfterLookup tc _ = tc

inputBoundIndexVars :: SapicTerm -> S.Set SapicLVar -> S.Set SapicLVar
inputBoundIndexVars msg mvars = indexVarsInTerm msg `S.difference` mvars

-- Index variables received as messages cannot be used as Squirrel indices.
indexVarsInTerm :: SapicTerm -> S.Set SapicLVar
indexVarsInTerm tm =
  case viewTerm tm of
    Lit (Var v@(SapicLVar _ (Just "index"))) -> S.singleton v
    Lit _ -> S.empty
    FApp _ ts -> S.unions (map indexVarsInTerm ts)

ppSquirrel :: SquirrelContext -> LProcess (ProcessAnnotation LVar) -> SquirrelRender
-- Render a complete process and reject paths that exit while holding a mutex.
ppSquirrel tc p =
  let rendered = ppSquirrelWithDepth 0 tc p
      heldAfter = heldDefinitelyAfterProcess tc [] p
   in if null heldAfter
        then rendered
        else
          translationFail
            "The input file cannot be exported to Squirrel: process terminates while holding a lock."

ppSquirrelWithDepth :: Int -> SquirrelContext -> LProcess (ProcessAnnotation LVar) -> SquirrelRender
-- Start recursive process rendering with no held mutexes.
ppSquirrelWithDepth depth tc = ppSquirrelWithDepthHeld depth tc S.empty []

data BranchRenders = BranchRenders
  { -- Rendered then/left branch.
    branchThenRender :: SquirrelRender,
    -- Rendered else/right branch.
    branchElseRender :: SquirrelRender,
    -- Whether to print the else/right branch.
    branchHasElse :: Bool,
    -- Warnings from branch handling.
    branchWarnings :: [String]
  }

ppSquirrelBranchRenders ::
  SquirrelContext ->
  SquirrelContext ->
  String ->
  String ->
  [SquirrelMutexRef] ->
  LProcess (ProcessAnnotation LVar) ->
  SquirrelRender ->
  LProcess (ProcessAnnotation LVar) ->
  SquirrelRender ->
  BranchRenders
-- Shared branch checks for conditionals and lookups.
ppSquirrelBranchRenders thenTc elseTc thenName elseName heldMutexes pl rl pr rr =
  -- Both branches must return with the same locks they started with.
  if heldAfterThen /= heldMutexes || heldAfterElse /= heldMutexes
    then
      translationFail $
        "The input file cannot be exported to Squirrel: lock state must not change across "
          ++ thenName
          ++ "/"
          ++ elseName
          ++ "."
    else
      BranchRenders
        { branchThenRender = rl,
          branchElseRender = elseRender,
          branchHasElse = hasElse,
          branchWarnings = []
        }
  where
    heldAfterThen = heldDefinitelyAfterProcess thenTc heldMutexes pl
    heldAfterElse =
      if isProcessNull pr
        then heldMutexes
        else heldDefinitelyAfterProcess elseTc heldMutexes pr
    elseBaseRender = if isProcessNull pr then emptySquirrelRender (text "null") else rr
    elseRender = elseBaseRender
    hasElse = not (docIsNull (squirrelDoc elseRender))

ppSquirrelWithDepthHeld ::
  Int ->
  SquirrelContext ->
  S.Set String ->
  [SquirrelMutexRef] ->
  LProcess (ProcessAnnotation LVar) ->
  SquirrelRender
-- Recursive process renderer.  It also threads:
--
-- * names reserved for replication indices;
-- * currently held mutexes.
ppSquirrelWithDepthHeld _ _ _ _ (ProcessNull _) = emptySquirrelRender (text "null")
ppSquirrelWithDepthHeld _ tc _ _ (ProcessAction (ProcessCall name ts) _ _) =
  -- Ignore the parser's expanded continuation; Squirrel can call the process.
  ppSquirrelProcessCall tc name ts
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessAction Rep _ p) =
  -- Tamarin replication becomes Squirrel indexed replication.
  let idxName = ppSquirrelRepIndex depth (usedRepIndexes `S.union` processVarNames tc p)
      rp = ppSquirrelWithDepthHeld (depth + 1) tc (S.insert idxName usedRepIndexes) heldMutexes p
      d
        | isProcessNull p || docIsNull (squirrelDoc rp) = text "null"
        | otherwise = repDocs (text idxName) (squirrelDoc rp)
   in rp {squirrelDoc = d}
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessAction a@(Event fact) _ p) =
  -- Events wrap the continuation as local payload lets.
  let tcForContinuation = updateContextAfterAction tc a
      heldForContinuation = updateHeldMutexes tc heldMutexes a
      rp = ppSquirrelWithDepthHeld depth tcForContinuation usedRepIndexes heldForContinuation p
      rpDoc = if isProcessNull p then text "null" else squirrelDoc rp
      eventRender = ppSquirrelEventAction tc fact rpDoc
   in renderFromParts (squirrelDoc eventRender) [eventRender, rp]
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessAction a an p) =
  -- Inputs may need a temporary binder plus pattern projections and guards.
  let inputBinder =
        case a of
          ChIn _ msg mvars -> Just (freshInputBinder tc msg mvars p)
          _ -> Nothing
      ra = ppSquirrelActionWithInputBinder tc inputBinder an a
      tcForContinuation = updateContextAfterAction tc a
      heldForContinuation = updateHeldMutexes tc heldMutexes a
      rp = ppSquirrelWithDepthHeld depth tcForContinuation usedRepIndexes heldForContinuation p
      (rpDoc, patternRenders) =
        case a of
          ChIn _ msg mvars ->
            let binder = fromMaybe (freshInputBinder tc msg mvars p) inputBinder
                (projections, guards) = ppSquirrelInputPatternConstraints tc binder msg mvars
                baseBody = if isProcessNull p then text "null" else squirrelDoc rp
                checkedBody = wrapWithProjections projections (wrapWithPatternGuards guards baseBody)
             in (checkedBody, guards)
          _ -> (if isProcessNull p then text "null" else squirrelDoc rp, [])
      d = case a of
        New _
          | docIsNull (squirrelDoc ra) -> rpDoc
          | docIsNull rpDoc -> squirrelDoc ra <> text ";" $$ text "null"
        _ -> seqDocs (squirrelDoc ra) rpDoc
   in renderFromParts d (ra : rp : patternRenders)
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessComb Parallel _ pl pr) =
  -- Parallel branches must end with the same locks they inherited.
  let rl = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pl
      rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
      heldAfterLeft = heldDefinitelyAfterProcess tc heldMutexes pl
      heldAfterRight = heldDefinitelyAfterProcess tc heldMutexes pr
      d
        | isProcessNull pl = squirrelDoc rr
        | isProcessNull pr = squirrelDoc rl
        | otherwise = parDocs (squirrelDoc rl) (squirrelDoc rr)
   in if heldAfterLeft /= heldMutexes || heldAfterRight /= heldMutexes
        then
          translationFail
            "The input file cannot be exported to Squirrel: lock state must not change across parallel branches."
        else renderFromParts d [rl, rr]
ppSquirrelWithDepthHeld _ _ _ _ (ProcessComb NDC _ _ _) =
  translationFail "The input file cannot be exported to Squirrel: non-deterministic choice is not supported in Squirrel process bodies."
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessComb (Let t1 t2 mvars) _ pl pr) =
  -- Squirrel has no direct `let pattern = term else branch` construct.
  if not (isProcessNull pr)
    then
      translationFail
        "The input file cannot be exported to Squirrel: let ... else ... is not supported."
    else
      let tcForThen = updateContextAfterLet tc t1 mvars
          rl = ppSquirrelWithDepthHeld depth tcForThen usedRepIndexes heldMutexes pl
          rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
          rt2 = ppSquirrelTerm tc t2
          lhs =
            case viewTerm t1 of
              Lit (Var v@(SapicLVar lvar _))
                | v `S.notMember` mvars -> ppLVarWith tc lvar
              _ ->
                freshTempName
                  "sq_let"
                  (termVarNames tc t1 `S.union` termVarNames tc t2 `S.union` processVarNames tc pl `S.union` processVarNames tc pr)
          (projections, guards) =
            case viewTerm t1 of
              Lit (Var v)
                | v `S.notMember` mvars -> ([], [])
              _ -> ppSquirrelPatternConstraints tc mvars lhs t1
          thenBody = if isProcessNull pl then text "null" else squirrelDoc rl
          d
            | isProcessNull pl = text "null"
            | otherwise =
                let wrappedThen = wrapWithProjections projections (wrapWithPatternGuards guards thenBody)
                 in text "let "
                      <> lhs
                      <> text " = "
                      <> squirrelDoc rt2
                      <> text " in"
                      $$ wrappedThen
       in renderFromParts d (rt2 : rl : rr : guards)
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessComb (Cond c) _ pl pr) =
  -- Expand predicate-based SAPIC conditions before rendering the guard.
  let rl = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pl
      rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
      branches = ppSquirrelBranchRenders tc tc "then-branch" "else-branch" heldMutexes pl rl pr rr
      thenRender = branchThenRender branches
      elseRender = branchElseRender branches
      hasElse = branchHasElse branches
      condRender =
        case expandFormula (predicates tc) (toLFormula c) of
          Left _ ->
            translationFail
              "The input file cannot be exported to Squirrel: conditional formula could not be expanded from SAPIC predicates."
          Right form ->
            fst . snd $ Precise.evalFresh (ppSquirrelLFormula tc emptyTypeEnv form) (avoidPrecise form)
      d =
        text "if "
          <> squirrelDoc condRender
          <> text " then"
          $$ wrapBranchDoc (squirrelDoc thenRender)
          $$ if hasElse then text "else" $$ wrapBranchDoc (squirrelDoc elseRender) else emptyDoc
   in withWarnings
        (branchWarnings branches)
        (renderFromParts d [condRender, thenRender, rr, elseRender])
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessComb (CondEq t1 t2) _ pl pr) =
  -- Some Tamarin boolean checks appear as message-term equalities.
  let rl = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pl
      rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
      branches = ppSquirrelBranchRenders tc tc "then-branch" "else-branch" heldMutexes pl rl pr rr
      thenRender = branchThenRender branches
      elseRender = branchElseRender branches
      hasElse = branchHasElse branches
      rt1 = ppSquirrelTerm tc t1
      rt2 = ppSquirrelTerm tc t2
      (condDoc, condRenders) = ppSquirrelCondEq tc t1 rt1 t2 rt2
      d =
        text "if "
          <> condDoc
          <> text " then"
          $$ wrapBranchDoc (squirrelDoc thenRender)
          $$ if hasElse then text "else" $$ wrapBranchDoc (squirrelDoc elseRender) else emptyDoc
   in withWarnings
        (branchWarnings branches)
        (renderFromParts d (thenRender : rr : elseRender : condRenders))

ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessComb (Lookup t c) _ pl pr) =
  -- Lookups read the value mutable and check the companion presence flag.
  let tcForThen = updateContextAfterLookup tc c
      rl = ppSquirrelWithDepthHeld depth tcForThen usedRepIndexes heldMutexes pl
      rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
   in case (squirrelStateRef tc t, ppSquirrelStateAccess tc t) of
        (Just cellRef, Just rs) ->
          let cVar = ppUnTypeVar tc c
              rp = ppSquirrelStatePresenceAccess tc cellRef
              branches = ppSquirrelBranchRenders tcForThen tc "lookup-then branch" "lookup-else branch" heldMutexes pl rl pr rr
              thenRender = branchThenRender branches
              elseRender = branchElseRender branches
              hasElse = branchHasElse branches
              body
                | hasElse =
                    checkedLookup (squirrelDoc elseRender)
                | otherwise =
                    checkedLookup (text "null")
              checkedLookup elseDoc =
                text "let " <> cVar <> text " = " <> squirrelDoc rs <> text " in"
                  $$ text "if " <> squirrelDoc rp <> text " then"
                  $$ wrapBranchDoc (squirrelDoc thenRender)
                  $$ text "else"
                  $$ wrapBranchDoc elseDoc
              rendered = withWarnings (branchWarnings branches) $
                renderFromParts body [rs, rp, thenRender, rr, elseRender]
           in rendered
        _ ->
          translationFail
            "The input file cannot be exported to Squirrel: lookup on non-indexed state cells is not supported."
updateHeldMutexes :: SquirrelContext -> [SquirrelMutexRef] -> LSapicAction -> [SquirrelMutexRef]
-- Track lock ownership through straight-line actions.
updateHeldMutexes tc held = \case
  Lock t ->
    case squirrelMutexRef tc t of
      Just mtx -> addHeldMutex held mtx
      Nothing -> held
  Unlock t ->
    case squirrelMutexRef tc t of
      Just mtx -> removeHeldMutex held mtx
      Nothing -> held
  _ -> held

addHeldMutex :: [SquirrelMutexRef] -> SquirrelMutexRef -> [SquirrelMutexRef]
-- Reject double-locking on one path.
addHeldMutex held mtx
  | mtx `elem` held =
      translationFail "The input file cannot be exported to Squirrel: process locks a mutex that is already held."
  | otherwise = mtx : held

removeHeldMutex :: [SquirrelMutexRef] -> SquirrelMutexRef -> [SquirrelMutexRef]
-- Reject unlocking a mutex that is not definitely held.
removeHeldMutex held mtx
  | mtx `elem` held = filter (/= mtx) held
  | otherwise =
      translationFail "The input file cannot be exported to Squirrel: process unlocks a mutex that is not held."

-- Conservative lock-flow analysis for branches and process exit.
heldDefinitelyAfterProcess :: SquirrelContext -> [SquirrelMutexRef] -> LProcess (ProcessAnnotation LVar) -> [SquirrelMutexRef]
heldDefinitelyAfterProcess _ held (ProcessNull _) = held
heldDefinitelyAfterProcess tc held (ProcessAction (ProcessCall _ _) _ p)
  | not (isProcessNull p) = heldDefinitelyAfterProcess tc held p
  | otherwise = held
heldDefinitelyAfterProcess tc held (ProcessAction a _ p) =
  let tcForContinuation = updateContextAfterAction tc a
   in heldDefinitelyAfterProcess tcForContinuation (updateHeldMutexes tc held a) p
heldDefinitelyAfterProcess tc held (ProcessComb Parallel _ pl pr)
  | heldAfterLeft == held && heldAfterRight == held = held
  | otherwise =
      translationFail
        "The input file cannot be exported to Squirrel: lock state must not change across parallel branches."
  where
    heldAfterLeft = heldDefinitelyAfterProcess tc held pl
    heldAfterRight = heldDefinitelyAfterProcess tc held pr
heldDefinitelyAfterProcess tc held (ProcessComb NDC _ pl pr) =
  heldDefinitelyAfterProcess tc held pl `List.intersect` heldDefinitelyAfterProcess tc held pr
heldDefinitelyAfterProcess tc held (ProcessComb (Let t1 _ mvars) _ pl pr)
  | isProcessNull pr = heldDefinitelyAfterProcess (updateContextAfterLet tc t1 mvars) held pl
  | otherwise =
      heldDefinitelyAfterProcess (updateContextAfterLet tc t1 mvars) held pl
        `List.intersect` heldDefinitelyAfterProcess tc held pr
heldDefinitelyAfterProcess tc held (ProcessComb (Cond _) _ pl pr) =
  heldDefinitelyAfterProcess tc held pl `List.intersect` heldDefinitelyAfterProcess tc held pr
heldDefinitelyAfterProcess tc held (ProcessComb (CondEq _ _) _ pl pr) =
  heldDefinitelyAfterProcess tc held pl `List.intersect` heldDefinitelyAfterProcess tc held pr
heldDefinitelyAfterProcess tc held (ProcessComb (Lookup _ c) _ pl pr) =
  heldDefinitelyAfterProcess (updateContextAfterLookup tc c) held pl
    `List.intersect` heldDefinitelyAfterProcess tc held pr

-- Render boolean-looking CondEq terms as boolean conditions.
ppSquirrelCondEq :: SquirrelContext -> SapicTerm -> SquirrelRender -> SapicTerm -> SquirrelRender -> (Doc, [SquirrelRender])
ppSquirrelCondEq tc t1 r1 t2 r2
  | Just b1 <- boolLiteralValue t1,
    Just b2 <- boolLiteralValue t2 =
      (text (if b1 == b2 then "true" else "false"), [])
  | isBoolLiteral True t1 && isBoolLikeTerm tc t2 = (squirrelDoc r2, [r2])
  | isBoolLikeTerm tc t1 && isBoolLiteral True t2 = (squirrelDoc r1, [r1])
  | isBoolLiteral False t1 && isBoolLikeTerm tc t2 = (operator_ "not" <> opParens (squirrelDoc r2), [r2])
  | isBoolLikeTerm tc t1 && isBoolLiteral False t2 = (operator_ "not" <> opParens (squirrelDoc r1), [r1])
  | otherwise = (squirrelDoc r1 <> text " = " <> squirrelDoc r2, [r1, r2])

isBoolLikeTerm :: SquirrelContext -> SapicTerm -> Bool
isBoolLikeTerm tc tm =
  case viewTerm tm of
    FApp (NoEq (f, _)) [] | isJust (squirrelBoolNoEqFunName f) -> True
    FApp (NoEq (f, _)) _ ->
      let n = ppFunSym f
       in (n == "verify" && hasSignatureBuiltin tc)
            || (n == "revealVerify" && hasRevealingSignatureBuiltin tc)
    Lit (Con c) ->
      let n = map toLower (show c)
       in n == "true" || n == "false"
    _ -> False

isBoolLiteral :: Bool -> SapicTerm -> Bool
isBoolLiteral expected tm = boolLiteralValue tm == Just expected

boolLiteralValue :: SapicTerm -> Maybe Bool
boolLiteralValue tm =
  case viewTerm tm of
    FApp (NoEq (f, _)) [] -> squirrelBoolNoEqFunName f
    Lit (Con c) ->
      case map toLower (show c) of
        "true" -> Just True
        "false" -> Just False
        _ -> Nothing
    _ -> Nothing

squirrelBoolNoEqFunName :: BC.ByteString -> Maybe Bool
squirrelBoolNoEqFunName f =
  case map toLower (BC.unpack f) of
    "true" -> Just True
    "false" -> Just False
    _ -> Nothing

isProcessNull :: LProcess ann -> Bool
isProcessNull (ProcessNull _) = True
isProcessNull _ = False

docIsNull :: Doc -> Bool
-- Treat rendered `null` as an empty process fragment.
docIsNull d = all isSpace stripped || stripped == "null"
  where
    stripped = dropWhile isSpace (render d)

seqDocs :: Doc -> Doc -> Doc
seqDocs l r
  | docIsNull l = r
  | docIsNull r = l
  | otherwise = l <> text ";" $$ r

wrapBranchDoc :: Doc -> Doc
wrapBranchDoc d = text "(" $$ nest 2 d $$ text ")"

ppSquirrelRepIndex :: Int -> S.Set String -> String
-- Choose compact index names for nested replications.
ppSquirrelRepIndex depth used = name
  where
    names = ["i", "j", "k", "l", "m", "n", "r", "s", "t"]
    candidates =
      drop depth names
        ++ take depth names
        ++ ["i" ++ show i | i <- [(length names + 1) :: Int ..]]
    name = head [candidate | candidate <- candidates, candidate `S.notMember` used]

repDocs :: Doc -> Doc -> Doc
repDocs idx body = text "!_" <> idx <-> parens (nest 2 body)

parDocs :: Doc -> Doc -> Doc
parDocs l r
  | docIsNull l = r
  | docIsNull r = l
  | otherwise = parens $ nest 2 l $$ text "|" <-> r

emptyTypeEnv :: TypingEnvironment
-- Process guards do not come with a lemma typing environment.
emptyTypeEnv = TypingEnvironment {vars = M.empty, events = M.empty, funs = M.empty}

typeVarsEvent :: TypingEnvironment -> FactTag -> [LNTerm] -> M.Map LVar SapicType
-- Recover variable types from event arguments when available.
typeVarsEvent te tag ts =
  case M.lookup tag te.events of
    Just tys ->
      foldl'
        ( \mp (term, ty) ->
            case viewTerm term of
              Lit (Var lvar) -> M.insert lvar ty mp
              _ -> mp
        )
        M.empty
        (zip ts tys)
    Nothing -> M.empty

mergeType :: Eq a => Maybe a -> Maybe a -> Maybe a
-- Keep the newer type when two paths provide one.
mergeType t Nothing = t
mergeType Nothing t = t
mergeType _ t = t

mergeEnv :: M.Map LVar SapicType -> M.Map LVar SapicType -> M.Map LVar SapicType
mergeEnv = M.mergeWithKey (\_ t1 t2 -> Just $ mergeType t1 t2) id id

ppSquirrelLNTerm :: SquirrelContext -> S.Set LVar -> LNTerm -> SquirrelRender
-- Reuse the SAPIC term renderer for formula terms.
ppSquirrelLNTerm tc boundVars = ppSquirrelFormulaTerm tc boundVars . mapLits (fmap (`SapicLVar` Nothing))

ppReachAtom :: SquirrelFormulaStyle -> Doc -> Doc
-- Global lemmas wrap reachability atoms; local formulas do not.
ppReachAtom SquirrelLocalFormula doc = doc
ppReachAtom SquirrelGlobalFormula doc = brackets doc

ppSquirrelAtom :: SquirrelFormulaStyle -> SquirrelContext -> TypingEnvironment -> S.Set LVar -> Bool -> ProtoAtom syn LNTerm -> (SquirrelRender, M.Map LVar SapicType)
-- Render one Tamarin formula atom.
ppSquirrelAtom style tc te boundVars _ (Action i f@(Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | (tag == KUFact) || isKLogFact f =
      case ts of
        [msg] ->
          let ri = ppSquirrelLNTerm tc boundVars i
              rm = ppSquirrelLNTerm tc boundVars msg
              rendered =
                withGlobalNoParens $
                  withWeakSecrecy $
                    renderFromParts
                      ( text "$("
                          <> opParens (ppSquirrelMacroAtWithStyle style "frame" (squirrelDoc ri))
                          <-> text "|>"
                          <-> opParens (squirrelDoc rm)
                          <> text ")"
                      )
                      [ri, rm]
           in (rendered, M.empty)
        _ ->
          translationFail $
            "The input file cannot be exported to Squirrel: malformed attacker-knowledge fact in SAPIC formula: "
              ++ factTagName tag
  | M.lookup (factTagName tag) (squirrelEventArities tc) == Just (length ts) =
      let ri = ppSquirrelLNTerm tc boundVars i
          renderedArgs = map (ppSquirrelLNTerm tc boundVars) ts
          payload = ppSquirrelEventPayload tag renderedArgs
          payloadEq =
            ppSquirrelMacroAtWithStyle style (squirrelEventMacroName tag) (squirrelDoc ri)
              <-> opEqual
              <-> squirrelDoc payload
          happensDoc = text "happens" <> parens (squirrelDoc ri)
          execDoc = ppSquirrelMacroAtWithStyle style "exec" (squirrelDoc ri)
          eventDocs =
            case style of
              SquirrelLocalFormula ->
                sep [opParens happensDoc <-> text "&&", execDoc <-> text "&&", payloadEq]
              SquirrelGlobalFormula ->
                sep
                  [ ppReachAtom style happensDoc <-> text "/\\",
                    ppReachAtom style execDoc <-> text "/\\",
                    ppReachAtom style payloadEq
                  ]
          rendered =
            renderFromParts
              eventDocs
              [ri, payload]
       in (rendered, typeVarsEvent te tag ts)
  | otherwise =
      translationFail $
        "The input file cannot be exported to Squirrel: action fact is not emitted by a SAPIC event in the exported process: "
          ++ factTagName tag
ppSquirrelAtom _ _ _ _ _ (Syntactic _) =
  translationFail "The input file cannot be exported to Squirrel: syntactic SAPIC formula atoms are not supported."
ppSquirrelAtom style tc _ boundVars False (EqE l r) =
  let rl = ppSquirrelLNTerm tc boundVars l
      rr = ppSquirrelLNTerm tc boundVars r
   in (renderFromParts (ppReachAtom style (sep [squirrelDoc rl <-> opEqual, squirrelDoc rr])) [rl, rr], M.empty)
ppSquirrelAtom style tc _ boundVars True (EqE l r) =
  let rl = ppSquirrelLNTerm tc boundVars l
      rr = ppSquirrelLNTerm tc boundVars r
   in (renderFromParts (ppReachAtom style (sep [squirrelDoc rl <-> text "<>", squirrelDoc rr])) [rl, rr], M.empty)
ppSquirrelAtom style tc _ boundVars _ (Less u v) =
  let ru = ppSquirrelLNTerm tc boundVars u
      rv = ppSquirrelLNTerm tc boundVars v
   in (renderFromParts (ppReachAtom style (squirrelDoc ru <-> opLess <-> squirrelDoc rv)) [ru, rv], M.empty)
ppSquirrelAtom _ _ _ _ _ (Subterm _ _) =
  translationFail "The input file cannot be exported to Squirrel: subterm SAPIC formula atoms are not supported."
ppSquirrelAtom style _ _ _ _ (Last i) = (emptySquirrelRender (ppReachAtom style (operator_ "last" <> parens (text (show i)))), M.empty)

mapLits :: (Ord a, Ord b) => (a -> b) -> Term a -> Term b
-- Local literal mapper for the term shapes used here.
mapLits f t = case viewTerm t of
  Lit l -> lit . f $ l
  FApp o as -> fApp o (map (mapLits f) as)

extractFree :: BVar p -> p
-- After opening a formula, only free variables should remain.
extractFree (Free v) = v
extractFree (Bound i) = translationFail $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

toLAt :: (Ord (f1 b), Ord (f1 (BVar b)), Functor f2, Functor f1) => f2 (Term (f1 (BVar b))) -> f2 (Term (f1 b))
-- Convert an opened atom back to free-variable form.
toLAt = fmap (mapLits (fmap extractFree))

ppSquirrelLFormula ::
  (MonadFresh m, Functor syn) =>
  SquirrelContext ->
  TypingEnvironment ->
  ProtoFormula syn (String, LSort) Name LVar ->
  m ([LVar], (SquirrelRender, M.Map LVar SapicType))
-- Default formula printer for local Squirrel syntax.
ppSquirrelLFormula = ppSquirrelLFormulaWithStyle SquirrelLocalFormula

ppSquirrelLFormulaWithStyle ::
  (MonadFresh m, Functor syn) =>
  SquirrelFormulaStyle ->
  SquirrelContext ->
  TypingEnvironment ->
  ProtoFormula syn (String, LSort) Name LVar ->
  m ([LVar], (SquirrelRender, M.Map LVar SapicType))
-- Render a Tamarin formula and infer any types carried by event atoms.
ppSquirrelLFormulaWithStyle style tc te =
  pp S.empty
  where
    ppOperand rendered =
      -- Some global atoms, such as WeakSecrecy expressions, are already complete.
      case style of
        SquirrelGlobalFormula
          | squirrelGlobalNoParens rendered -> squirrelDoc rendered
        _ -> opParens (squirrelDoc rendered)

    pp boundVars (Ato a) = pure ([], ppSquirrelAtom style tc te boundVars False (toLAt a))
    pp _ (TF True) = pure ([], (emptySquirrelRender (ppReachAtom style (operator_ "true")), M.empty))
    pp _ (TF False) = pure ([], (emptySquirrelRender (ppReachAtom style (operator_ "false")), M.empty))
    pp boundVars (Not (Ato a@(EqE _ _))) = pure ([], ppSquirrelAtom style tc te boundVars True (toLAt a))
    pp boundVars (Not p) = do
      (vs, (p', envp)) <- pp boundVars p
      let rendered =
            case style of
              SquirrelLocalFormula ->
                operator_ "not" <> opParens (squirrelDoc p')
              SquirrelGlobalFormula ->
                ppOperand p' <-> text "->" <-> ppReachAtom style (operator_ "false")
      pure (vs, (renderFromParts rendered [p'], envp))
    pp boundVars (Conn op p q) = do
      (vsp, (p', envp)) <- pp boundVars p
      (vsq, (q', envq)) <- pp boundVars q
      let rendered =
            renderFromParts
              (ppConn op p' q')
              [p', q']
      pure (vsp ++ vsq, (rendered, mergeEnv envp envq))
      where
        ppConn And p' q' =
          sep [ppOperand p' <-> ppOp And, ppOperand q']
        ppConn Or p' q' =
          sep [ppOperand p' <-> ppOp Or, ppOperand q']
        ppConn Imp p' q' =
          sep [ppOperand p' <-> ppOp Imp, ppOperand q']
        ppConn Iff p' q' =
          case style of
            SquirrelLocalFormula ->
              sep [ppOperand p' <-> opIff, ppOperand q']
            SquirrelGlobalFormula ->
              sep
                [ opParens (sep [ppOperand p' <-> text "->", ppOperand q']) <-> text "/\\",
                  opParens (sep [ppOperand q' <-> text "->", ppOperand p'])
                ]
        ppOp And =
          case style of
            SquirrelLocalFormula -> text "&&"
            SquirrelGlobalFormula -> text "/\\"
        ppOp Or =
          case style of
            SquirrelLocalFormula -> text "||"
            SquirrelGlobalFormula -> text "\\/"
        ppOp Imp =
          case style of
            SquirrelLocalFormula -> text "=>"
            SquirrelGlobalFormula -> text "->"
    pp boundVars fm@(Qua {}) = scopeFreshness $ do
      -- Open consecutive quantifiers together for a compact binder list.
      (vs, qua, fm') <- openFormulaPrefix fm
      let boundVars' = boundVars `S.union` S.fromList vs
      (vsp, (body, envp)) <- pp boundVars' fm'
      let rendered =
            renderFromParts
              (ppSquirrelQuant qua <-> ppSquirrelQuantVars envp vs <> comma <-> squirrelDoc body)
              [body]
      pure (vsp, (rendered, envp))

    ppSquirrelQuant All =
      case style of
        SquirrelLocalFormula -> text "forall"
        SquirrelGlobalFormula -> text "Forall"
    ppSquirrelQuant Ex =
      case style of
        SquirrelLocalFormula -> text "exists"
        SquirrelGlobalFormula -> text "Exists"

    ppSquirrelQuantVars envp =
      parens . fsep . punctuate comma . map (ppSquirrelQuantVar envp)

    ppSquirrelQuantVar envp v = ppLVar v <> text ":" <> text (ppSquirrelQuantSort envp v)

    ppSquirrelQuantSort envp v =
      -- Prefer types from events, then the typing environment, then the raw sort.
      let sortName =
            case lookupQuantType envp v of
              Just "index" -> "index"
              Just "node" -> "timestamp"
              Just "timestamp" -> "timestamp"
              _ ->
                case lvarSort v of
                  LSortNode -> "timestamp"
                  LSortNat -> "nat"
                  _ -> "message"
       in case (style, sortName) of
            (SquirrelGlobalFormula, "timestamp") -> "timestamp[const]"
            _ -> sortName

    lookupQuantType envp v =
      case M.lookup v envp of
        Just (Just ty) -> Just ty
        _ ->
          case M.lookup v te.vars of
            Just (Just ty) -> Just ty
            _ -> Nothing

ppSquirrelEquationOrWarning :: SquirrelContext -> Int -> CtxtStRule -> IO SquirrelRender
-- Unsupported user equations become warnings instead of aborting the export.
ppSquirrelEquationOrWarning tc idx rule = do
  renderedOrError <- try (evaluate (forceSquirrelRender (ppSquirrelEquationAxiom tc idx rule))) :: IO (Either IOException SquirrelRender)
  pure $
    case renderedOrError of
      Right rendered -> rendered
      Left err ->
        withSkippedEquation idx $
          withWarnings
            [ "Skipping user-defined equation #"
                ++ show idx
                ++ " during Squirrel export: "
                ++ cleanSquirrelFailure (ioeGetErrorString err)
            ]
            (emptySquirrelRender emptyDoc)

ppSquirrelEquationAxiom :: SquirrelContext -> Int -> CtxtStRule -> SquirrelRender
-- Export a Tamarin rewrite rule as a best-effort Squirrel axiom.
ppSquirrelEquationAxiom tc idx (CtxtStRule lhs (StRhs _ rhs)) =
  withWarnings [equationAxiomWarning] $
    renderFromParts
      ( text "axiom [any] "
          <> text ("equation_" ++ show idx)
          <> ppSquirrelEquationBinders freeVars
          <> text ": "
          <> squirrelDoc renderedLhs
          <-> opEqual
          <-> squirrelDoc renderedRhs
          <> text "."
      )
      [renderedLhs, renderedRhs]
  where
    renderedLhs = ppSquirrelEquationTerm tc lhs
    renderedRhs = ppSquirrelEquationTerm tc rhs
    freeVars = S.toList (S.fromList (frees lhs ++ frees rhs))

ppSquirrelEquationBinders :: [LVar] -> Doc
-- Quantify the free variables used by the exported equation.
ppSquirrelEquationBinders [] = emptyDoc
ppSquirrelEquationBinders vars =
  text " "
    <> parens
      ( fsep
          ( punctuate
              comma
              [ppLVar v <> text ":" <> text (ppSquirrelEquationSort (lvarSort v)) | v <- vars]
          )
      )

ppSquirrelEquationSort :: LSort -> String
ppSquirrelEquationSort LSortNode = "timestamp"
ppSquirrelEquationSort LSortNat = "nat"
ppSquirrelEquationSort _ = "message"

equationAxiomWarning :: String
equationAxiomWarning =
  "User-defined Tamarin equations are exported as Squirrel axioms; this is a best-effort translation of rewriting semantics."

ppSquirrelLemmaOrWarning :: SquirrelContext -> TypingEnvironment -> ProtoLemma LNFormula ProofSkeleton -> IO SquirrelRender
-- Unsupported selected lemmas become warnings.
ppSquirrelLemmaOrWarning tc te lem = do
  renderedOrError <- try (evaluate (forceSquirrelRender (ppSquirrelLemma tc te lem))) :: IO (Either IOException SquirrelRender)
  pure $
    case renderedOrError of
      Right rendered -> rendered
      Left err ->
        withSkippedLemma lem._lName $
          withWarnings
            [ "Skipping selected Tamarin lemma "
                ++ lem._lName
                ++ " during Squirrel export: "
                ++ cleanSquirrelFailure (ioeGetErrorString err)
            ]
            (emptySquirrelRender emptyDoc)

forceSquirrelRender :: SquirrelRender -> SquirrelRender
-- Force lazy render fields so recoverable failures are caught in IO.
forceSquirrelRender rendered =
  forceDoc (squirrelDoc rendered)
    `seq` forceStrings (squirrelWarnings rendered)
    `seq` forceStringIntMap (squirrelFunDecls rendered)
    `seq` forceStrings (S.toList (squirrelConstDecls rendered))
    `seq` forceStrings (S.toList (squirrelNameDecls rendered))
    `seq` forceStringIntMap (squirrelStateDecls rendered)
    `seq` forceStringIntMap (squirrelMutexDecls rendered)
    `seq` squirrelNeedsWeakSecrecy rendered
    `seq` squirrelGlobalNoParens rendered
    `seq` S.foldr seq () (squirrelSkippedEquations rendered)
    `seq` forceStrings (S.toList (squirrelSkippedLemmas rendered))
    `seq` rendered
  where
    forceDoc = forceString . render
    forceStrings = foldr (\s acc -> forceString s `seq` acc) ()
    forceString = foldr seq ()
    forceStringIntMap =
      M.foldrWithKey
        ( \name arity acc ->
            forceString name `seq` arity `seq` acc
        )
        ()

cleanSquirrelFailure :: String -> String
-- Remove IO exception boilerplate from generated warnings.
cleanSquirrelFailure reason =
  fromMaybe reason $
    List.stripPrefix "The input file cannot be exported to Squirrel: " normalized
  where
    normalized =
      fromMaybe reason $
        stripSuffix ")" =<< List.stripPrefix "user error (" reason

stripSuffix :: Eq a => [a] -> [a] -> Maybe [a]
stripSuffix suffix value =
  reverse <$> List.stripPrefix (reverse suffix) (reverse value)

ppSquirrelLemma :: SquirrelContext -> TypingEnvironment -> ProtoLemma LNFormula ProofSkeleton -> SquirrelRender
-- Convert a supported Tamarin lemma into a Squirrel lemma skeleton.
ppSquirrelLemma tc te lem
  | LHSLemma `elem` lem._lAttributes || RHSLemma `elem` lem._lAttributes || ReuseDiffLemma `elem` lem._lAttributes =
      translationFail $
        "The input file cannot be exported to Squirrel: diff lemmas are not supported: "
          ++ lem._lName
  | lem._lTraceQuantifier == ExistsTrace =
      translationFail $
        "The input file cannot be exported to Squirrel: exists-trace lemmas are not supported: "
          ++ lem._lName
  | otherwise =
      withWarnings [lemmaAdmitWarning] $
        renderFromParts
          (ppLemmaDoc body)
          [body]
  where
    localBody = fst . snd $ Precise.evalFresh (ppSquirrelLFormulaWithStyle SquirrelLocalFormula tc te lem._lFormula) (avoidPrecise lem._lFormula)
    globalBody = fst . snd $ Precise.evalFresh (ppSquirrelLFormulaWithStyle SquirrelGlobalFormula tc te lem._lFormula) (avoidPrecise lem._lFormula)
    body
      | squirrelNeedsWeakSecrecy localBody = globalBody
      | otherwise = localBody
    lemmaName = text (sanitizeSquirrelLemmaName lem._lName)
    ppLemmaDoc renderedBody =
      lemmaHeader
        $$ nest 2 (squirrelDoc renderedBody)
        <> text "."
        $$ text "Proof."
        $$ nest 2 (text "admit.")
        $$ text "Qed."
    lemmaHeader
      | squirrelNeedsWeakSecrecy localBody =
          text "global lemma" <-> lemmaName <-> text "@system:default" <-> text ":"
      | otherwise =
          text "lemma" <-> lemmaName <-> text ":"

lemmaAdmitWarning :: String
lemmaAdmitWarning =
  "Tamarin lemmas are exported as Squirrel proof obligations with admitted placeholder proofs; they are not automatically re-proved."

sanitizeSquirrelLemmaName :: String -> String
sanitizeSquirrelLemmaName = sanitizeSquirrelSymbol 'l'
