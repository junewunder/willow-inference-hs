{-# OPTIONS_GHC -Wno-deprecations #-}

module Util
  ( trace'
  , _trace'
  , traceP
  , _traceP
  , traceArg
  , _traceArg
  , capitalize
  , prefixStateChangeVars
  , prefixStateChangeVarsTy
  , effSeq
  , seqMany
  , seqManyStCh
  , isCompilerVar
  , indentBlock
  ) where

import RIO
import RIO.Text (pack)
import Prettyprinter
import Types
import RIO.Char
import RIO.List
import qualified RIO.Text as Text

capitalize :: String -> String
capitalize [] = []
capitalize (x : xs) = toUpper x : map toLower xs

trace' :: (Show a) => String -> a -> a
trace' name thing = trace (pack $ name ++ " = " ++ show thing) thing

traceP :: (Pretty a) => String -> a -> a
traceP name thing = trace (pack $ name ++ " = \n" ++ show (indent 2 (pretty thing))) thing

traceArg :: (Pretty a) => String -> a -> Bool
traceArg name thing = trace (pack $ name ++ " = \n" ++ show (indent 2 (pretty thing))) False

_trace' :: String -> a -> a
_trace' _name thing = thing

_traceArg :: String -> a -> Bool
_traceArg _ _ = False

_traceP :: String -> a -> a
_traceP _name thing = thing

isCompilerVar :: Text -> Bool
isCompilerVar x = "__" `Text.isPrefixOf` x

-- | Prefix every line of an already-rendered block with @n@ spaces. Used to
-- place a wrapped effect tree (see 'renderEffect') under its heading; doing
-- the indent here rather than with 'Prettyprinter.indent' keeps the wrap
-- width and the final column independent.
indentBlock :: Int -> Text -> Text
indentBlock n = Text.intercalate "\n" . map (Text.replicate n " " <>) . Text.lines

-- | Prefix all EffStateChange variable names in an Effect with a given string (e.g., "instName.")
-- Event labels are NOT state-change variables: they are left untouched.
prefixStateChangeVars :: Text -> Effect -> Effect
prefixStateChangeVars prefix eff = case eff of
  EffNone -> EffNone
  EffLoop v -> EffLoop v
  EffStateChange v -> EffStateChange (prefix <> pack "." <> v)
  EffAfter d e -> EffAfter d (prefixStateChangeVars prefix e)
  EffSeq es -> mkEffSeq (map (prefixStateChangeVars prefix) es)
  EffBranch e1 e2 -> EffBranch (prefixStateChangeVars prefix e1) (prefixStateChangeVars prefix e2)
  EffVar v -> EffVar v  -- Effect variables don't need prefixing
  EffEvent lbl -> EffEvent lbl
  EffAlways lbl e -> EffAlways lbl (prefixStateChangeVars prefix e)
  EffEventually lbl e -> EffEventually lbl (prefixStateChangeVars prefix e)
  EffCancel lbl -> EffCancel lbl
  EffRemove lbl -> EffRemove lbl

-- | Prefix all EffStateChange variable names in all Effect fields of a Type
prefixStateChangeVarsTy :: Text -> Type -> Type
prefixStateChangeVarsTy prefix ty = case ty of
  TArrow es t1 t2 eff -> TArrow es (prefixStateChangeVarsTy prefix t1) (prefixStateChangeVarsTy prefix t2) (prefixStateChangeVars prefix eff)
  TDelay d t -> TDelay d (prefixStateChangeVarsTy prefix t)
  TComponent args ret -> TComponent (map (prefixStateChangeVarsTy prefix) args) (prefixStateChangeVarsTy prefix ret)
  TPair t1 t2 -> TPair (prefixStateChangeVarsTy prefix t1) (prefixStateChangeVarsTy prefix t2)
  _ -> ty

-- | Sequence two effects. Flattens one level of 'EffSeq' on either side and
-- rebuilds via 'mkEffSeq', so only idempotent effect trees dedup.
effSeq :: Effect -> Effect -> Effect
effSeq EffNone f = f
effSeq f EffNone = f
effSeq f1 f2 = mkEffSeq (flatten f1 ++ flatten f2)
  where
    flatten (EffSeq es) = es
    flatten e = [e]


seqMany :: [Effect] -> Effect
seqMany = foldr effSeq EffNone

seqManyStCh :: [Text] -> Effect
seqManyStCh = foldr (effSeq . EffStateChange) EffNone
