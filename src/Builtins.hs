-- | Built-in library functions with their type schemas
module Builtins
  ( tyLibraryFunctions,
    builtinFunctionTypes,
    parseBuiltinTypes,
    removeLibFns
  )
where

import RIO
import qualified RIO.Map as Map
import Text.Megaparsec (errorBundlePretty)
import Import
import Parse (pType, runAnnotatedParser)
import qualified RIO.List as List

-- | Map of built-in function names to their schema strings
builtinFunctionTypes :: Map Text Text
builtinFunctionTypes = Map.fromList
  [ ("+", "int -> int -> int")
  , ("-", "int -> int -> int")
  , ("++", "string -> string -> string")
  , ("*", "int -> int -> int")
  , ("/", "int -> int -> int")
  , ("===", "string -> string -> bool")
  , ("==", "int -> int -> bool")
  , ("!==", "string -> string -> bool")
  , ("!=", "int -> int -> bool")
  , ("<", "int -> int -> bool")
  , ("<=", "int -> int -> bool")
  , (">", "int -> int -> bool")
  , (">=", "int -> int -> bool")
  , ("&&", "bool -> bool -> bool")
  , ("||", "bool -> bool -> bool")
  , ("addOne", "int -> int")
  , ("print", "string -> unit")
  , ("printInt", "int -> unit")
  , ("printBool", "bool -> unit")
  , ("toString", "int -> string")
  , ("toInt", "string -> int")
  , ("toBool", "string -> bool")
  , ("mod", "int -> int -> int")
  , ("xor", "bool -> bool -> bool")
  , ("or", "bool -> bool -> bool")
  , ("and", "bool -> bool -> bool")
  , ("not", "bool -> bool")
  , ("()", "unit")
  , ("expensive", "int -> int")
  , ("fetch", "forall e. (string * (string -> unit | e)) -> unit | after 1n {e}")
  , ("fetchData", "forall eSuc, eErr. (string * (string -> unit | eSuc) * (string -> unit | eErr)) -> unit | after 1n {eSuc + eErr}")
  , ("asyncCompute", "forall e1, e2. (int -> unit | e1) -> (int -> unit | e2) -> unit | after 1u {comp<suc> + comp<err>} * eventually comp<suc> {e1 * remove comp<err>} * eventually comp<err> {e2 * remove comp<suc>}")
  , ("fetchUsernameCheck", "forall e1, e2. (string * ((string * bool) -> unit | e1) * (string -> unit | e2)) -> unit | after 1n {req<check,suc> + req<check,err>} * eventually req<check,suc> {e1 * remove req<check,err>} * eventually req<check,err> {e2 * remove req<check,suc>}")
  , ("has", "(string * string) -> bool")
  , ("setTimeout", "forall e. (unit -> unit | e) -> unit | eventually timeout<> {e} * after 100ms {timeout<>}")
  , ("clearTimeout", "unit -> unit | cancel timeout<> * remove timeout<>")
  , ("clearInterval", "unit -> unit")
  , ("const", "int -> int -> int")
  , (";;", "unit -> unit -> unit")
  , ("Date.now", "unit -> int")
  , ("random", "unit -> int")
  ]

-- | Under @--allow-any@, the entries the versions with @any@ had: @null@,
-- and @fetch@/@fetchData@ handing their callbacks an @any@. They override
-- 'builtinFunctionTypes'.
anyFunctionTypes :: Map Text Text
anyFunctionTypes = Map.fromList
  [ ("null", "any")
  , ("fetch", "forall e. (string * (any -> unit | e)) -> unit | after 1n {e}")
  , ("fetchData", "forall eSuc, eErr. (string * (any -> unit | eSuc) * (any -> unit | eErr)) -> unit | after 1n {eSuc + eErr}")
  ]

-- | Parse a schema string into a Type value. Built-in schemas may mention
-- @any@; only 'anyFunctionTypes' does.
parseTypeString :: (IsString string) => Text -> Either string Type
parseTypeString schemaText =
  case runAnnotatedParser True pType "<builtin-schema>" schemaText of
    Left err -> Left (fromString (errorBundlePretty err))
    Right schema -> Right schema

-- | Parse a table of builtin schemas into a TyEnv
parseBuiltinTypes :: (IsString string) => Map Text Text -> Either string (Map Text Type)
parseBuiltinTypes table = do
  let parseEntry (name, schemaText) = do
        schema <- parseTypeString schemaText
        return (name, schema)

  entries <- traverse parseEntry (Map.toList table)
  return $ Map.fromList entries

-- | The library functions environment (parsed from schema strings), with
-- or without the @--allow-any@ entries.
tyLibraryFunctions :: Bool -> Map Text Type
tyLibraryFunctions allowAny = if allowAny then libraryWithAny else library

library, libraryWithAny :: Map Text Type
library = parseOrDie builtinFunctionTypes
libraryWithAny = parseOrDie (Map.union anyFunctionTypes builtinFunctionTypes)

parseOrDie :: Map Text Text -> Map Text Type
parseOrDie table = case parseBuiltinTypes table of
  Left err -> error $ "Failed to parse builtin schemas: " <> err
  Right env -> env

-- | Drop the names of library functions. @null@ counts as one in both modes:
-- without @--allow-any@ it is not in scope, so it never gets this far.
removeLibFns :: [Text] -> [Text]
removeLibFns = List.filter (\x -> x `notElem` Map.keys libraryWithAny)
