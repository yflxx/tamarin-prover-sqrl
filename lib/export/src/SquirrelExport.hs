{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}

{-# HLINT ignore "Use lambda-case" #-}

module SquirrelExport
  ( prettySquirrelTheory,
  )
where

import Control.Monad.Fresh
import Control.Monad.Trans.PreciseFresh qualified as Precise
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
import Sapic.States
import Sapic.Typing
import System.IO.Unsafe
import Term.SubtermRule (CtxtStRule)
import Text.PrettyPrint.Class
import Theory
import Theory.Sapic
import Theory.Text.Pretty

translationFail :: String -> a
translationFail s = unsafePerformIO (fail s)

data SquirrelContext = SquirrelContext
  { predicates :: [Predicate],
    squirrelTheoryBuiltins :: S.Set String,
    messageBoundIndexVars :: S.Set SapicLVar
  }

data SquirrelRender = SquirrelRender
  { squirrelDoc :: Doc,
    squirrelWarnings :: [String],
    squirrelFunDecls :: M.Map String Int,
    squirrelConstDecls :: S.Set String,
    squirrelStateDecls :: M.Map String Int,
    squirrelMutexDecls :: M.Map String Int
  }

emptySquirrelRender :: Doc -> SquirrelRender
emptySquirrelRender d =
  SquirrelRender
    { squirrelDoc = d,
      squirrelWarnings = [],
      squirrelFunDecls = M.empty,
      squirrelConstDecls = S.empty,
      squirrelStateDecls = M.empty,
      squirrelMutexDecls = M.empty
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
      squirrelStateDecls = mergeMaxMaps (map squirrelStateDecls renders),
      squirrelMutexDecls = mergeMaxMaps (map squirrelMutexDecls renders)
    }

renderFromParts :: Doc -> [SquirrelRender] -> SquirrelRender
renderFromParts d renders = (mergeSquirrelMetadata renders) {squirrelDoc = d}

withWarnings :: [String] -> SquirrelRender -> SquirrelRender
withWarnings warnings rendered =
  rendered {squirrelWarnings = warnings ++ squirrelWarnings rendered}

withStateDecl :: String -> Int -> SquirrelRender -> SquirrelRender
withStateDecl name arity rendered =
  rendered {squirrelStateDecls = M.insertWith max name arity (squirrelStateDecls rendered)}

withMutexDecl :: String -> Int -> SquirrelRender -> SquirrelRender
withMutexDecl name arity rendered =
  rendered {squirrelMutexDecls = M.insertWith max name arity (squirrelMutexDecls rendered)}

data SquirrelBuiltinStmt = SquirrelBuiltinStmt
  { builtinStmtKey :: String,
    builtinStmtDoc :: Doc
  }

data BuiltinTranslation = BuiltinTranslation
  { builtinTranslationStmts :: [SquirrelBuiltinStmt],
    builtinTranslationNames :: S.Set String,
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
builtins "diffie-hellman" =
  bestEffortBuiltin
    [ builtinStmt "dh-group" (text "ddh g, (^) where group:message exponents:message.")
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
  accurateBuiltin
    [ builtinStmt "aenc-decl" (text "aenc asym_enc, asym_dec, asym_pk.") ]
    ["asym_enc", "asym_dec", "asym_pk"]
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
  accurateBuiltin
    [ builtinStmt "senc-decl" (text "senc sym_enc, sym_dec.") ]
    ["sym_enc", "sym_dec"]
builtins "multiset" =
  unsupportedBuiltin
    "Multiset is not supported in Squirrel. If you want to model natural numbers, you can use the dedicated Tamarin builtin."
builtins "bilinear-pairing" =
  unsupportedBuiltin
    "Bilinear pairings are not supported in Squirrel."
builtins x =
  unsupportedBuiltin ("unsupported builtin declaration " ++ x ++ ".")

collectBuiltinDecls :: [String] -> ([Doc], S.Set String, [String])
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
unsupportedTheoryRules thy =
  stRules thy._thySignature._sigMaudeInfo `S.difference` supportedRules
  where
    supportedRules =
      S.unions $
        stRules (minimalMaudeSig False) :
        map (maybe S.empty stRules . supportedBuiltinSig) (theoryBuiltins thy)

supportedBuiltinSig :: String -> Maybe MaudeSig
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

rejectUnsupportedTheoryRules :: OpenTheory -> ()
rejectUnsupportedTheoryRules thy =
  if S.null (unsupportedTheoryRules thy)
    then ()
    else
      translationFail
        "The input file cannot be exported to Squirrel: user-defined equations are not supported."

prettySquirrelTheory :: (OpenTheory, TypingEnvironment) -> IO Doc
prettySquirrelTheory (thy, _) =
  case theoryProcesses thy of
    [] -> pure $ text "(* No SAPIC process found. *)"
    [pr] ->
      let p = makeAnnotations thy pr
          _noUnsupportedTheoryRules = rejectUnsupportedTheoryRules thy
          _hasStates = hasBoundUnboundStates p
          tc =
            SquirrelContext
              { predicates = theoryPredicates thy,
                squirrelTheoryBuiltins = S.fromList (theoryBuiltins thy),
                messageBoundIndexVars = S.empty
              }
          rendered = ppSquirrel tc p
          procDefRendered = map (ppSquirrelProcessDef tc thy) (theoryProcessDefs thy)
          renderedAll = foldl mergeSquirrelRenders rendered (map snd procDefRendered)
          (builtinDecls, builtinNames, builtinWarnings) = collectBuiltinDecls (theoryBuiltins thy)
          warningDocs =
            map
              (\w -> text "(* WARNING: " <> text w <> text " *)")
              (List.nub (builtinWarnings ++ squirrelWarnings renderedAll))
          funDecls = map ppSquirrelFunDecl (M.toList (M.filterWithKey (\k _ -> not (isSquirrelBuiltinSymbol k) && not (k `S.member` squirrelConstDecls renderedAll) && not (k `S.member` builtinNames)) (squirrelFunDecls renderedAll)))
          constDecls = map ppSquirrelConstDecl (S.toList (S.filter (\k -> not (isSquirrelBuiltinSymbol k) && not (k `S.member` builtinNames)) (S.delete "pub_chan" (squirrelConstDecls renderedAll))))
          stateInitDecls = map ppSquirrelStateInitDecl (M.toList (squirrelStateDecls renderedAll))
          stateDecls = map ppSquirrelStateDecl (M.toList (squirrelStateDecls renderedAll))
          statePresenceDecls = map ppSquirrelStatePresenceDecl (M.toList (squirrelStateDecls renderedAll))
          mutexDecls = map ppSquirrelMutexDecl (M.toList (squirrelMutexDecls renderedAll))
          procDefDocs = map fst procDefRendered
          comments = [text "(*" $$ text bd $$ text "*)" | (_, bd) <- theoryFormalComments thy]
          preludeDocs =
            [ text "set postQuantumEquivs = true.",
              text "include Core.",
              text "channel pub_chan."
            ]
          declDocs =
            builtinDecls
              ++ constDecls
              ++ funDecls
              ++ stateInitDecls
              ++ stateDecls
              ++ statePresenceDecls
              ++ mutexDecls
          mainProcessDocs =
            [ text "",
              text "process main =",
              nest 2 (squirrelDoc rendered) <> text ".",
              text "system main."
            ]
          theoryDocs =
            warningDocs
              ++ preludeDocs
              ++ declDocs
              ++ [text ""]
              ++ procDefDocs
              ++ mainProcessDocs
              ++ comments
       in _noUnsupportedTheoryRules `seq` pure (vcat theoryDocs)
    _ ->
      translationFail
        "The input file cannot be exported to Squirrel: multiple SAPIC processes were defined; Squirrel export currently supports exactly one top-level process."

ppSquirrelProcessDef :: SquirrelContext -> OpenTheory -> ProcessDef -> (Doc, SquirrelRender)
ppSquirrelProcessDef tc thy pdef =
  let body = makeAnnotations thy (pdef._pBody)
      vars = fromMaybe [] (pdef._pVars)
      params = if null vars then emptyDoc else parens (fsep (punctuate comma (map ppSquirrelProcParam vars)))
      (bodyDoc, bodyRender) =
        case ppSquirrelLeafProcess tc body of
          Just rendered -> (squirrelDoc rendered, rendered)
          Nothing ->
            let r = ppSquirrel tc body
             in (squirrelDoc r, r)
      doc = text "process " <> text (sanitizeSquirrelProcessName pdef._pName) <> params <> text " =" $$ nest 2 bodyDoc <> text "."
   in (doc, bodyRender)

ppSquirrelProcParam :: SapicLVar -> Doc
ppSquirrelProcParam v = ppUnTypeVar v <> text ":" <> text (ppSquirrelVarType v)

ppSquirrelProcessCall :: SquirrelContext -> String -> [SapicTerm] -> SquirrelRender
ppSquirrelProcessCall tc name args =
  let renderedArgs = map (ppSquirrelTerm tc) args
      callArgs =
        case renderedArgs of
          [] -> emptyDoc
          _ -> parens (fsep (punctuate comma (map squirrelDoc renderedArgs)))
   in renderFromParts (text (sanitizeSquirrelProcessName name) <> callArgs) renderedArgs

ppSquirrelVarType :: SapicLVar -> String
ppSquirrelVarType (SapicLVar _ (Just "index")) = "index"
ppSquirrelVarType (SapicLVar _ (Just "node")) = "timestamp"
ppSquirrelVarType _ = "message"

ppSquirrelLeafProcess :: SquirrelContext -> LProcess (ProcessAnnotation LVar) -> Maybe SquirrelRender
ppSquirrelLeafProcess _ (ProcessAction (Event _) _ (ProcessAction (ChOut _ _) _ (ProcessNull _))) =
  translationFail "The input file cannot be exported to Squirrel: SAPIC events are not supported in Squirrel process bodies."
ppSquirrelLeafProcess tc (ProcessAction (ChOut ch msg) _ (ProcessNull _)) =
  let chRender = ppSquirrelChan ch
      rendered = ppSquirrelTerm tc msg
   in Just $
        renderFromParts
          (text "out(" <> squirrelDoc chRender <> text ", " <> squirrelDoc rendered <> text ")")
          [chRender, rendered]
ppSquirrelLeafProcess _ _ = Nothing

makeAnnotations :: OpenTheory -> PlainProcess -> LProcess (ProcessAnnotation LVar)
makeAnnotations thy p = res
  where
    p' = report $ toAnProcess p
    res = annotatePureStates p'
    report pr =
      if isNothing (List.find (== "locations-report") (theoryBuiltins thy))
        then pr
        else translateTermsReport pr

ppSquirrelTypeArrow :: Int -> String -> String
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

ppSquirrelStateInitDecl :: (String, Int) -> Doc
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
renderSquirrelPkName tc
  | hasSignatureBuiltin tc && hasAsymmetricBuiltin tc =
      translationFail
        "The input file cannot be exported to Squirrel: ambiguous pk term in a theory with both signing and asymmetric encryption. Use pk only in a context where the exporter can infer sig_pk or asym_pk."
  | hasSignatureBuiltin tc = "sig_pk"
  | hasAsymmetricBuiltin tc = "asym_pk"
  | otherwise = "asym_pk"

sanitizeSquirrelSymbol :: Char -> String -> String
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
  | isAscii c && isAlphaNum c = [c]
  | otherwise = "_x" ++ showHex (ord c) "_"

isSquirrelIdentStart :: Char -> Bool
isSquirrelIdentStart c = isAscii c && isAlpha c

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
ppLVarName (LVar n _ 0) = sanitizeSquirrelSymbol 'a' n
ppLVarName (LVar n _ i) = sanitizeSquirrelSymbol 'a' $ n <> "_" <> show i

ppLVar :: LVar -> Doc
ppLVar = text . ppLVarName

ppSapicLVarName :: SapicLVar -> String
ppSapicLVarName (SapicLVar lvar _) = ppLVarName lvar

ppUnTypeVar :: SapicLVar -> Doc
ppUnTypeVar (SapicLVar lvar _) = ppLVar lvar

isSyntheticStateChannelVar :: SapicLVar -> Bool
isSyntheticStateChannelVar (SapicLVar lvar _) = "StateChannel" `List.isPrefixOf` lvarName lvar

data SquirrelCellRef = SquirrelCellRef
  { squirrelCellName :: String,
    squirrelCellArgs :: [SapicTerm]
  }

data SquirrelMutexRef = SquirrelMutexRef
  { squirrelMutexName :: String,
    squirrelMutexArgs :: [SapicTerm]
  }
  deriving (Eq)

ppSquirrelTerm :: SquirrelContext -> SapicTerm -> SquirrelRender
ppSquirrelTerm tc = ppSquirrelTermWith tc (const True)

ppSquirrelFormulaTerm :: SquirrelContext -> S.Set LVar -> SapicTerm -> SquirrelRender
ppSquirrelFormulaTerm tc boundVars = ppSquirrelTermWith tc renderPublicVarAsConstant
  where
    renderPublicVarAsConstant (SapicLVar lvar _) =
      lvarSort lvar == LSortPub && lvar `S.notMember` boundVars

ppSquirrelTermWith :: SquirrelContext -> (SapicLVar -> Bool) -> SapicTerm -> SquirrelRender
ppSquirrelTermWith tc renderPublicVarAsConstant t =
  SquirrelRender
    { squirrelDoc = doc,
      squirrelWarnings = [],
      squirrelFunDecls = funs,
      squirrelConstDecls = consts,
      squirrelStateDecls = M.empty,
      squirrelMutexDecls = M.empty
    }
  where
    (doc, funs, consts) = go t

    partDoc (d, _, _) = d
    partFuns (_, f, _) = f
    partConsts (_, _, c) = c
    partsConstDecls = S.unions . map partConsts
    fromParts d parts = (d, mergeMaxMaps (map partFuns parts), partsConstDecls parts)
    fromPartsWithFun d f arity parts =
      (d, mergeMaxMaps (M.singleton f arity : map partFuns parts), partsConstDecls parts)
    withPartConst c (d, f, constDecls) = (d, f, S.insert c constDecls)

    go tm = case viewTerm tm of
      Lit (Var svar@(SapicLVar lvar@(LVar _ LSortPub _) _))
        | renderPublicVarAsConstant svar ->
            let c = "s" ++ sanitizeSquirrelSymbol 'a' (lvarName lvar) ++ "_" ++ show (lvarIdx lvar)
             in (text c, M.empty, S.singleton c)
      Lit (Var (SapicLVar lvar _)) -> (ppLVar lvar, M.empty, S.empty)
      Lit (Con (Name PubName n)) ->
        let c = ppSquirrelPubName n
         in (text c, M.empty, S.singleton c)
      Lit (Con (Name FreshName n)) ->
        let c = sanitizeSquirrelSymbol 'a' (show n)
         in (text c, M.empty, S.singleton c)
      Lit (Con c) ->
        let c' = sanitizeSquirrelSymbol 'a' (show c)
         in (text c', M.empty, S.singleton c')
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
      FApp (NoEq (f, _)) [] | squirrelBoolNoEqFunName f == Just True -> (text "true", M.empty, S.empty)
      FApp (NoEq (f, _)) [] | squirrelBoolNoEqFunName f == Just False -> (text "false", M.empty, S.empty)
      FApp (NoEq (f, _)) [] | ppFunSym f == "zero" && hasXorBuiltin tc -> (text "zero", M.empty, S.singleton "zero")
      FApp (NoEq s) [] | s == natOneSym -> (text "one", M.empty, S.singleton "one")
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
      case viewTerm tm of
        FApp (NoEq (f, _)) [skTerm] | ppFunSym f == "pk" ->
          let sk = go skTerm
           in fromPartsWithFun (text pkName <> text "(" <> partDoc sk <> text ")") pkName 1 [sk]
        _ -> go tm

    ppFunLike f [] =
      (text f, M.singleton f 0, S.empty)
    ppFunLike f ts =
      let rendered = map go ts
          docs = map partDoc rendered
       in fromPartsWithFun (text f <> text "(" <> fsep (punctuate comma docs) <> text ")") f (length ts) rendered

    goACNested _ [] = (text "empty", M.empty, S.singleton "empty")
    goACNested _ [t1] = go t1
    goACNested f [t1, t2] = ppFunLike f [t1, t2]
    goACNested f (t1 : ts) =
      let r1 = go t1
          rest = goACNested f ts
       in fromPartsWithFun (text f <> text "(" <> partDoc r1 <> text ", " <> partDoc rest <> text ")") f 2 [r1, rest]

    goXor [] = (text "zero", M.empty, S.singleton "zero")
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
ppSquirrelStateAccess tc t = do
  cell <- squirrelStateRef tc t
  pure $
    withStateDecl
      (squirrelCellName cell)
      (length (squirrelCellArgs cell))
      (ppSquirrelRefRender tc (squirrelCellName cell) (squirrelCellArgs cell))

ppSquirrelStatePresenceAccess :: SquirrelContext -> SquirrelCellRef -> SquirrelRender
ppSquirrelStatePresenceAccess tc cell =
  withStateDecl
    (squirrelCellName cell)
    (length (squirrelCellArgs cell))
    (ppSquirrelRefRender tc (squirrelStatePresentName (squirrelCellName cell)) (squirrelCellArgs cell))

ppSquirrelMutexAccess :: SquirrelContext -> SapicTerm -> Maybe SquirrelRender
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

squirrelStateRef :: SquirrelContext -> SapicTerm -> Maybe SquirrelCellRef
squirrelStateRef tc t = do
  (tag, args) <- squirrelStructuredArgs tc t
  pure $ SquirrelCellRef ("st_" ++ sanitizeSquirrelSymbol 's' tag) args

squirrelMutexRef :: SquirrelContext -> SapicTerm -> Maybe SquirrelMutexRef
squirrelMutexRef tc t = do
  (tag, args) <- squirrelStructuredArgs tc t
  pure $ SquirrelMutexRef ("mtx_" ++ sanitizeSquirrelSymbol 'm' tag) args

squirrelStructuredArgs :: SquirrelContext -> SapicTerm -> Maybe (String, [SapicTerm])
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
canonicalStructuredParts tc =
  List.sortBy (compareStructuredParts tc)

canonicalXorStructuredParts :: SquirrelContext -> [(String, [SapicTerm])] -> [(String, [SapicTerm])]
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
structuredPartKey tc (tag, args) = (tag, map (render . squirrelDoc . ppSquirrelTerm tc) args)

ppSquirrelActionWithInputBinder :: SquirrelContext -> Maybe Doc -> LSapicAction -> SquirrelRender
ppSquirrelActionWithInputBinder tc inputBinder = \case
  Rep ->
    SquirrelRender
      { squirrelDoc = text "out(pub_chan, srep_drop)",
        squirrelWarnings = ["Replication inside process bodies is not supported in Squirrel v1 export; replaced by null."],
        squirrelFunDecls = M.empty,
        squirrelConstDecls = S.singleton "srep_drop",
        squirrelStateDecls = M.empty,
        squirrelMutexDecls = M.empty
      }
  New v
    | isSyntheticStateChannelVar v -> emptySquirrelRender (text "null")
    | otherwise -> emptySquirrelRender (text "new " <> ppUnTypeVar v)
  ChIn ch msg mvars ->
    let chRender = ppSquirrelChan ch
        binder = fromMaybe (ppSquirrelInputBinder (text "sq_in") msg mvars) inputBinder
     in chRender
          { squirrelDoc = text "in(" <> squirrelDoc chRender <> text ", " <> binder <> text ")"
          }
  ChOut ch msg ->
    let chRender = ppSquirrelChan ch
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
mergeSquirrelRenders l r =
  (mergeSquirrelMetadata [l, r]) {squirrelDoc = squirrelDoc l}

ppSquirrelChan :: Maybe SapicTerm -> SquirrelRender
ppSquirrelChan ch =
  case ch of
    Just _ ->
      withWarnings
        ["Explicit SAPIC channels are mapped to pub_chan in Squirrel export."]
        (emptySquirrelRender (text "pub_chan"))
    Nothing ->
      withWarnings
        ["Implicit SAPIC channel mapped to pub_chan in Squirrel export."]
        (emptySquirrelRender (text "pub_chan"))

patternVariables :: SapicTerm -> S.Set SapicLVar
patternVariables t =
  case viewTerm t of
    Lit (Var v) -> S.singleton v
    Lit _ -> S.empty
    FApp _ ts -> S.unions (map patternVariables ts)

ppSquirrelPatternGuard :: SquirrelContext -> Doc -> SapicTerm -> SquirrelRender
ppSquirrelPatternGuard tc actual expected =
  let rendered = ppSquirrelTerm tc expected
   in rendered {squirrelDoc = actual <-> text "=" <-> squirrelDoc rendered}

ppSquirrelPatternConstraints ::
  SquirrelContext ->
  S.Set SapicLVar ->
  Doc ->
  SapicTerm ->
  ([(Doc, Doc)], [SquirrelRender])
ppSquirrelPatternConstraints tc mvars base t =
  let (_, projections, guards) = go S.empty base t
   in (projections, guards)
  where
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
            | v `S.member` mvars -> (bound, [], [emptySquirrelRender (actual <-> text "=" <-> ppLVar lvar)])
            | v `S.member` bound -> (bound, [], [emptySquirrelRender (actual <-> text "=" <-> ppLVar lvar)])
            | otherwise -> (S.insert v bound, [(ppLVar lvar, actual)], [])
          Lit _ -> (bound, [], [ppSquirrelPatternGuard tc actual term])
          FApp _ _
            | patternVariables term `S.isSubsetOf` (mvars `S.union` bound) ->
                (bound, [], [ppSquirrelPatternGuard tc actual term])
            | otherwise ->
                translationFail
                  "The input file cannot be exported to Squirrel: non-pair patterns with newly bound variables are not supported."

wrapWithProjections :: [(Doc, Doc)] -> Doc -> Doc
wrapWithProjections [] body = body
wrapWithProjections ((var, proj) : rest) body =
  text "let " <> var <> text " = " <> proj <> text " in"
    $$ wrapWithProjections rest body

wrapWithPatternGuards :: [SquirrelRender] -> Doc -> Doc
wrapWithPatternGuards [] body = body
wrapWithPatternGuards (condition : rest) body =
  text "if " <> squirrelDoc condition <> text " then"
    $$ wrapBranchDoc (wrapWithPatternGuards rest body)

ppSquirrelInputBinder :: Doc -> SapicTerm -> S.Set SapicLVar -> Doc
ppSquirrelInputBinder fallback msg mvars =
  case viewTerm msg of
    Lit (Var v@(SapicLVar lvar _))
      | v `S.member` mvars -> fallback
      | otherwise -> ppLVar lvar
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

termVarNames :: SapicTerm -> S.Set String
termVarNames t =
  case viewTerm t of
    Lit (Var v) -> S.singleton (ppSapicLVarName v)
    Lit _ -> S.empty
    FApp _ ts -> S.unions (map termVarNames ts)

processVarNames :: LProcess ann -> S.Set String
processVarNames = S.map ppSapicLVarName . foldMap S.singleton

freshTempName :: String -> S.Set String -> Doc
freshTempName base used = text $ head [candidate | i <- [0 :: Int ..], let candidate = suffix i, candidate `S.notMember` used]
  where
    suffix 0 = base
    suffix i = base ++ "_" ++ show i

freshInputBinder :: SapicTerm -> S.Set SapicLVar -> LProcess ann -> Doc
freshInputBinder msg mvars continuation =
  ppSquirrelInputBinder fallback msg mvars
  where
    fallback =
      freshTempName
        "sq_in"
        (termVarNames msg `S.union` S.map ppSapicLVarName mvars `S.union` processVarNames continuation)

updateContextAfterAction :: SquirrelContext -> LSapicAction -> SquirrelContext
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
updateContextAfterLookup tc v@(SapicLVar _ (Just "index")) =
  tc {messageBoundIndexVars = S.insert v (messageBoundIndexVars tc)}
updateContextAfterLookup tc _ = tc

inputBoundIndexVars :: SapicTerm -> S.Set SapicLVar -> S.Set SapicLVar
inputBoundIndexVars msg mvars = indexVarsInTerm msg `S.difference` mvars

indexVarsInTerm :: SapicTerm -> S.Set SapicLVar
indexVarsInTerm tm =
  case viewTerm tm of
    Lit (Var v@(SapicLVar _ (Just "index"))) -> S.singleton v
    Lit _ -> S.empty
    FApp _ ts -> S.unions (map indexVarsInTerm ts)

ppSquirrel :: SquirrelContext -> LProcess (ProcessAnnotation LVar) -> SquirrelRender
ppSquirrel tc p =
  let rendered = ppSquirrelWithDepth 0 tc p
      heldAfter = heldDefinitelyAfterProcess tc [] p
   in if null heldAfter
        then rendered
        else
          translationFail
            "The input file cannot be exported to Squirrel: process terminates while holding a lock."

ppSquirrelWithDepth :: Int -> SquirrelContext -> LProcess (ProcessAnnotation LVar) -> SquirrelRender
ppSquirrelWithDepth depth tc = ppSquirrelWithDepthHeld depth tc S.empty []

data BranchRenders = BranchRenders
  { branchThenRender :: SquirrelRender,
    branchElseRender :: SquirrelRender,
    branchHasElse :: Bool,
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
ppSquirrelBranchRenders thenTc elseTc thenName elseName heldMutexes pl rl pr rr =
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
ppSquirrelWithDepthHeld _ _ _ _ (ProcessNull _) = emptySquirrelRender (text "null")
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessAction (ProcessCall _ _) _ p)
  | not (isProcessNull p) = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes p
ppSquirrelWithDepthHeld _ tc _ _ (ProcessAction (ProcessCall name ts) _ _) =
  ppSquirrelProcessCall tc name ts
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessAction Rep _ p) =
  let idxName = ppSquirrelRepIndex depth (usedRepIndexes `S.union` processVarNames p)
      rp = ppSquirrelWithDepthHeld (depth + 1) tc (S.insert idxName usedRepIndexes) heldMutexes p
      d
        | isProcessNull p || docIsNull (squirrelDoc rp) = text "null"
        | otherwise = repDocs (text idxName) (squirrelDoc rp)
   in rp {squirrelDoc = d}
ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessAction a _ p) =
  let inputBinder =
        case a of
          ChIn _ msg mvars -> Just (freshInputBinder msg mvars p)
          _ -> Nothing
      ra = ppSquirrelActionWithInputBinder tc inputBinder a
      tcForContinuation = updateContextAfterAction tc a
      heldForContinuation = updateHeldMutexes tc heldMutexes a
      rp = ppSquirrelWithDepthHeld depth tcForContinuation usedRepIndexes heldForContinuation p
      (rpDoc, patternRenders) =
        case a of
          ChIn _ msg mvars ->
            let binder = fromMaybe (freshInputBinder msg mvars p) inputBinder
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
                | v `S.notMember` mvars -> ppLVar lvar
              _ ->
                freshTempName
                  "sq_let"
                  (termVarNames t1 `S.union` termVarNames t2 `S.union` processVarNames pl `S.union` processVarNames pr)
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
  let rl = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pl
      rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
      branches = ppSquirrelBranchRenders tc tc "then-branch" "else-branch" heldMutexes pl rl pr rr
      thenRender = branchThenRender branches
      elseRender = branchElseRender branches
      hasElse = branchHasElse branches
      rt1 = ppSquirrelTerm tc t1
      rt2 = ppSquirrelTerm tc t2
      condDoc = ppSquirrelCondEqDoc tc t1 rt1 t2 rt2
      d =
        text "if "
          <> condDoc
          <> text " then"
          $$ wrapBranchDoc (squirrelDoc thenRender)
          $$ if hasElse then text "else" $$ wrapBranchDoc (squirrelDoc elseRender) else emptyDoc
   in withWarnings
        (branchWarnings branches)
        (renderFromParts d [thenRender, rr, rt1, rt2, elseRender])

ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes (ProcessComb (Lookup t c) _ pl pr) =
  let tcForThen = updateContextAfterLookup tc c
      rl = ppSquirrelWithDepthHeld depth tcForThen usedRepIndexes heldMutexes pl
      rr = ppSquirrelWithDepthHeld depth tc usedRepIndexes heldMutexes pr
   in case (squirrelStateRef tc t, ppSquirrelStateAccess tc t) of
        (Just cellRef, Just rs) ->
          let cVar = ppUnTypeVar c
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
addHeldMutex held mtx
  | mtx `elem` held =
      translationFail "The input file cannot be exported to Squirrel: process locks a mutex that is already held."
  | otherwise = mtx : held

removeHeldMutex :: [SquirrelMutexRef] -> SquirrelMutexRef -> [SquirrelMutexRef]
removeHeldMutex held mtx
  | mtx `elem` held = filter (/= mtx) held
  | otherwise =
      translationFail "The input file cannot be exported to Squirrel: process unlocks a mutex that is not held."

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

ppSquirrelCondEqDoc :: SquirrelContext -> SapicTerm -> SquirrelRender -> SapicTerm -> SquirrelRender -> Doc
ppSquirrelCondEqDoc tc t1 r1 t2 r2
  | isBoolLiteral True t1 && isBoolLikeTerm tc t2 = squirrelDoc r2
  | isBoolLikeTerm tc t1 && isBoolLiteral True t2 = squirrelDoc r1
  | otherwise = squirrelDoc r1 <> text " = " <> squirrelDoc r2

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
isBoolLiteral expected tm =
  case viewTerm tm of
    FApp (NoEq (f, _)) [] -> squirrelBoolNoEqFunName f == Just expected
    Lit (Con c) -> map toLower (show c) == if expected then "true" else "false"
    _ -> False

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
emptyTypeEnv = TypingEnvironment {vars = M.empty, events = M.empty, funs = M.empty}

mergeType :: Eq a => Maybe a -> Maybe a -> Maybe a
mergeType t Nothing = t
mergeType Nothing t = t
mergeType _ t = t

mergeEnv :: M.Map LVar SapicType -> M.Map LVar SapicType -> M.Map LVar SapicType
mergeEnv = M.mergeWithKey (\_ t1 t2 -> Just $ mergeType t1 t2) id id

ppSquirrelLNTerm :: SquirrelContext -> S.Set LVar -> LNTerm -> SquirrelRender
ppSquirrelLNTerm tc boundVars = ppSquirrelFormulaTerm tc boundVars . mapLits (fmap (`SapicLVar` Nothing))

ppSquirrelAtom :: SquirrelContext -> TypingEnvironment -> S.Set LVar -> Bool -> ProtoAtom syn LNTerm -> (SquirrelRender, M.Map LVar SapicType)
ppSquirrelAtom _ _ _ _ (Action _ (Fact tag _ ts))
  | factTagArity tag /= length ts = translationFail $ "MALFORMED function" ++ show tag
  | otherwise =
      translationFail $
        "The input file cannot be exported to Squirrel: action facts in SAPIC formulas are not supported: "
          ++ factTagName tag
ppSquirrelAtom _ _ _ _ (Syntactic _) =
  translationFail "The input file cannot be exported to Squirrel: syntactic SAPIC formula atoms are not supported."
ppSquirrelAtom tc _ boundVars False (EqE l r) =
  let rl = ppSquirrelLNTerm tc boundVars l
      rr = ppSquirrelLNTerm tc boundVars r
   in (renderFromParts (sep [squirrelDoc rl <-> opEqual, squirrelDoc rr]) [rl, rr], M.empty)
ppSquirrelAtom tc _ boundVars True (EqE l r) =
  let rl = ppSquirrelLNTerm tc boundVars l
      rr = ppSquirrelLNTerm tc boundVars r
   in (renderFromParts (sep [squirrelDoc rl <-> text "<>", squirrelDoc rr]) [rl, rr], M.empty)
ppSquirrelAtom tc _ boundVars _ (Less u v) =
  let ru = ppSquirrelLNTerm tc boundVars u
      rv = ppSquirrelLNTerm tc boundVars v
   in (renderFromParts (squirrelDoc ru <-> opLess <-> squirrelDoc rv) [ru, rv], M.empty)
ppSquirrelAtom _ _ _ _ (Subterm _ _) =
  translationFail "The input file cannot be exported to Squirrel: subterm SAPIC formula atoms are not supported."
ppSquirrelAtom _ _ _ _ (Last i) = (emptySquirrelRender (operator_ "last" <> parens (text (show i))), M.empty)

mapLits :: (Ord a, Ord b) => (a -> b) -> Term a -> Term b
mapLits f t = case viewTerm t of
  Lit l -> lit . f $ l
  FApp o as -> fApp o (map (mapLits f) as)

extractFree :: BVar p -> p
extractFree (Free v) = v
extractFree (Bound i) = translationFail $ "prettyFormula: illegal bound variable '" ++ show i ++ "'"

toLAt :: (Ord (f1 b), Ord (f1 (BVar b)), Functor f2, Functor f1) => f2 (Term (f1 (BVar b))) -> f2 (Term (f1 b))
toLAt = fmap (mapLits (fmap extractFree))

ppSquirrelLFormula ::
  (MonadFresh m, Functor syn) =>
  SquirrelContext ->
  TypingEnvironment ->
  ProtoFormula syn (String, LSort) Name LVar ->
  m ([LVar], (SquirrelRender, M.Map LVar SapicType))
ppSquirrelLFormula tc te =
  pp S.empty
  where
    pp boundVars (Ato a) = pure ([], ppSquirrelAtom tc te boundVars False (toLAt a))
    pp _ (TF True) = pure ([], (emptySquirrelRender (operator_ "true"), M.empty))
    pp _ (TF False) = pure ([], (emptySquirrelRender (operator_ "false"), M.empty))
    pp boundVars (Not (Ato a@(EqE _ _))) = pure ([], ppSquirrelAtom tc te boundVars True (toLAt a))
    pp boundVars (Not p) = do
      (vs, (p', envp)) <- pp boundVars p
      pure (vs, (renderFromParts (operator_ "not" <> opParens (squirrelDoc p')) [p'], envp))
    pp boundVars (Conn op p q) = do
      (vsp, (p', envp)) <- pp boundVars p
      (vsq, (q', envq)) <- pp boundVars q
      let rendered =
            renderFromParts
              (sep [opParens (squirrelDoc p') <-> ppOp op, opParens (squirrelDoc q')])
              [p', q']
      pure (vsp ++ vsq, (rendered, mergeEnv envp envq))
      where
        ppOp And = text "&&"
        ppOp Or = text "||"
        ppOp Imp = text "=>"
        ppOp Iff = opIff
    pp boundVars fm@(Qua {}) = scopeFreshness $ do
      (vs, qua, fm') <- openFormulaPrefix fm
      let boundVars' = boundVars `S.union` S.fromList vs
      (vsp, (body, envp)) <- pp boundVars' fm'
      let rendered =
            renderFromParts
              (ppSquirrelQuant qua <-> ppSquirrelQuantVars vs <> comma <-> squirrelDoc body)
              [body]
      pure (vsp, (rendered, envp))

    ppSquirrelQuant All = text "forall"
    ppSquirrelQuant Ex = text "exists"

    ppSquirrelQuantVars =
      parens . fsep . punctuate comma . map ppSquirrelQuantVar

    ppSquirrelQuantVar v = ppLVar v <> text ":" <> text (ppSquirrelQuantSort (lvarSort v))

    ppSquirrelQuantSort LSortNode = "timestamp"
    ppSquirrelQuantSort LSortNat = "nat"
    ppSquirrelQuantSort _ = "message"
