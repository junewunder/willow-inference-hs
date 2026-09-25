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
import Text.Megaparsec (runParser, errorBundlePretty)
import Import
import Parse (pType)
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
  , ("fetch", "forall e. (string * (any -> unit | e)) -> unit | after 1n {e}")
  , ("fetchData", "forall eSuc, eErr. (string * (any -> unit | eSuc) * (any -> unit | eErr)) -> unit | after 1n {eSuc + eErr}")
  , ("asyncCompute", "forall e1, e2. (int -> unit | e1) -> (int -> unit | e2) -> unit | after 1u {comp<suc> + comp<err>} * eventually comp<suc> {e1 * remove comp<err>} * eventually comp<err> {e2 * remove comp<suc>}")
  , ("fetchUsernameCheck", "forall e1, e2. (string * ((string * bool) -> unit | e1) * (string -> unit | e2)) -> unit | after 1n {req<check,suc> + req<check,err>} * eventually req<check,suc> {e1 * remove req<check,err>} * eventually req<check,err> {e2 * remove req<check,suc>}")
  , ("has", "(string * string) -> bool")
  , ("setTimeout", "forall e. (unit -> unit | e) -> unit | eventually timeout<> {e} * after 100ms {timeout<>}")
  , ("clearTimeout", "unit -> unit | cancel timeout<> * remove timeout<>")
  , ("clearInterval", "unit -> unit")
  , ("const", "int -> int -> int")
  , (";;", "unit -> unit -> unit")
  , ("null", "any")
  , ("Date.now", "unit -> int")
  , ("random", "unit -> int")
  ]

-- | Parse a schema string into a Type value
parseTypeString :: (IsString string) => Text -> Either string Type
parseTypeString schemaText =
  case runParser pType "<builtin-schema>" schemaText of
    Left err -> Left (fromString (errorBundlePretty err))
    Right schema -> Right schema

-- | Parse all builtin schemas into a TyEnv
parseBuiltinTypes :: (IsString string) => Either string (Map Text Type)
parseBuiltinTypes = do
  let parseEntry (name, schemaText) = do
        schema <- parseTypeString schemaText
        return (name, schema)

  entries <- traverse parseEntry (Map.toList builtinFunctionTypes)
  return $ Map.fromList entries

-- | The library functions environment (parsed from schema strings)
tyLibraryFunctions :: Map Text Type
tyLibraryFunctions = case parseBuiltinTypes of
  Left err -> error $ "Failed to parse builtin schemas: " <> err
  Right env -> env

removeLibFns :: [Text] -> [Text]
removeLibFns = List.filter (\x -> x `notElem` Map.keys tyLibraryFunctions)
