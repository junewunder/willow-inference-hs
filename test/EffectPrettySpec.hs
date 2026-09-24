-- | Tests for the two effect printers in "Types": the canonical one-line
-- 'prettyEffect' (the 'Pretty' instance) and the line-breaking
-- 'prettyEffectReadable' / 'renderEffect'.
--
-- The property that matters for both is that they print the concrete syntax
-- 'Parse.pEffect' accepts, and print enough parentheses that the result
-- reparses to the effect we started with. That is what lets the tool's output
-- be pasted back into a program, and it is the thing most easily broken by a
-- later change to either the printer or the grammar — in particular because
-- @*@ binds LOOSER than @+@, so a printer that assumes arithmetic precedence
-- produces output that reparses to a DIFFERENT effect rather than failing.
module EffectPrettySpec (spec) where

import Import
import Parse (pEffect)
import Test.Hspec
import Text.Megaparsec (runParser, eof)
import Prettyprinter (LayoutOptions (..), PageWidth (..), layoutPretty)
import Prettyprinter.Render.Text (renderStrict)
import qualified RIO.Text as Text

-- | The canonical rendering, laid out with no width limit (it contains no
-- line breaks, so this only avoids a default page width mattering).
canonical :: Effect -> Text
canonical = renderStrict . layoutPretty (LayoutOptions Unbounded) . prettyEffect

reparse :: Text -> Either String Effect
reparse src = case runParser (pEffect <* eof) "effect" (Text.strip src) of
  Left err -> Left (show err)
  Right eff -> Right eff

-- | Representative effects, all in the normal form 'mkEffSeq' produces (the
-- parser rebuilds sequences through it, so a non-normal input would fail the
-- round trip for reasons that have nothing to do with printing).
examples :: [(String, Effect)]
examples =
  [ ("none", EffNone)
  , ("state change", EffStateChange "position")
  , ("dotted sub-component state", EffStateChange "slowUsername.slow")
  , ("loop", EffLoop "status")
  , ("effect variable", EffVar (EffVarName "F"))
  , ("event", EffEvent (EventLabel "req" ["check", "suc"]))
  , ("event with no values", EffEvent (EventLabel "timeout" []))
  , ("event with a # value", EffEvent (EventLabel "click" ["#doc"]))
  , ("cancel", EffCancel (EventLabel "timeout" []))
  , ("remove", EffRemove (EventLabel "click" ["#doc"]))
  , ("delay in renders", EffAfter (Time 1 Renders) (EffStateChange "x"))
  , ("delay in network requests", EffAfter (Time 1 NetworkReq) (EffStateChange "x"))
  , ("delay in milliseconds", EffAfter (Time 100 Millis) (EffStateChange "x"))
  , ("delay in debounce windows", EffAfter (Time 1 Debounce) (EffStateChange "x"))
  , ("delay in intervals", EffAfter (Time 2 Interval) (EffStateChange "x"))
  , ("delay in compute units", EffAfter (Time 3 Compute) (EffStateChange "x"))
  , ("summed delay", EffAfter (Plus (Time 1 Renders) (Time 2 NetworkReq)) (EffStateChange "x"))
  , ("always", EffAlways (EventLabel "click" ["#doc"]) (EffAfter (Time 1 Renders) (EffStateChange "position")))
  , ("eventually", EffEventually (EventLabel "timeout" []) (EffAfter (Time 1 Renders) (EffStateChange "slow")))
  , ("sequence", mkEffSeq [EffCancel (EventLabel "timeout" []), EffRemove (EventLabel "timeout" [])])
  , ("branch", EffBranch (EffStateChange "a") EffNone)
  , ("right-nested branch", EffBranch (EffStateChange "a") (EffBranch (EffStateChange "b") EffNone))
  , ("left-nested branch", EffBranch (EffBranch (EffStateChange "a") (EffStateChange "b")) EffNone)
  , -- The shape that a printer assuming arithmetic precedence gets wrong:
    -- @F + G * H@ reparses as @(F + G) * H@, so the branch needs brackets.
    ( "branch inside a sequence"
    , mkEffSeq
        [ EffBranch (EffAfter (Time 1 Renders) (EffStateChange "availableNames")) EffNone
        , EffRemove (EventLabel "req" ["check", "err"])
        ]
    )
  , ("sequence inside a branch", EffBranch EffNone (mkEffSeq [EffStateChange "a", EffStateChange "b"]))
  , -- Debounce's inferred cascade: the smallest real effect that does not fit
    -- on one 80-column line.
    ( "the Debounce cascade"
    , mkEffSeq
        [ EffCancel (EventLabel "timeout" [])
        , EffRemove (EventLabel "timeout" [])
        , EffEventually (EventLabel "timeout" []) (EffAfter (Time 1 Renders) (EffStateChange "slow"))
        , EffAfter (Time 100 Millis) (EffEvent (EventLabel "timeout" []))
        ]
    )
  ]

effectNamed :: String -> Effect
effectNamed name = case [eff | (n, eff) <- examples, n == name] of
  (eff : _) -> eff
  [] -> error ("EffectPrettySpec: no example named " <> name)

spec :: Spec
spec = do
  describe "prettyEffect (canonical, one line)" $ do
    it "never breaks a line" $
      forM_ examples $ \(name, eff) ->
        (name, Text.isInfixOf "\n" (canonical eff)) `shouldBe` (name, False)

    it "reparses to the effect it was printed from" $
      forM_ examples $ \(name, eff) ->
        (name, reparse (canonical eff)) `shouldBe` (name, Right eff)

    -- The one deliberate exception to the round trip. A unification variable
    -- is the checker's own unknown: a spelling that reparsed would make it a
    -- written variable, which means something else.
    it "prints a unification variable as ?_e3, a spelling the parser rejects" $ do
      canonical (EffUnif 3) `shouldBe` "?_e3"
      renderEffect 72 (EffUnif 3) `shouldBe` "?_e3"
      isLeft (reparse "?_e3") `shouldBe` True

  describe "renderEffect (readable, line-broken)" $ do
    it "reparses to the effect it was printed from, at every width" $
      forM_ [20, 40, 72, 200] $ \width ->
        forM_ examples $ \(name, eff) ->
          ((name, width), reparse (renderEffect width eff)) `shouldBe` ((name, width), Right eff)

    it "agrees with the canonical printer when everything fits on one line" $
      forM_ examples $ \(name, eff) ->
        (name, renderEffect 500 eff) `shouldBe` (name, canonical eff)

    it "never emits trailing whitespace" $
      forM_ [20, 40, 72] $ \width ->
        forM_ examples $ \(name, eff) ->
          let bad = [l | l <- Text.lines (renderEffect width eff), l /= Text.stripEnd l]
           in ((name, width), bad) `shouldBe` ((name, width), [])

    it "breaks a cascade that does not fit, one operand per line" $
      renderEffect 72 (effectNamed "the Debounce cascade")
        `shouldBe` Text.intercalate
          "\n"
          [ "  cancel timeout<>"
          , "* remove timeout<>"
          , "* eventually timeout<> {after 1r {@slow}}"
          , "* after 100ms {timeout<>}"
          ]

    it "brackets a branch nested in a sequence, on one line and broken" $ do
      renderEffect 200 (effectNamed "branch inside a sequence")
        `shouldBe` "(after 1r {@availableNames} + none) * remove req<check,err>"
      renderEffect 40 (effectNamed "branch inside a sequence")
        `shouldBe` Text.intercalate
          "\n"
          [ "  (after 1r {@availableNames} + none)"
          , "* remove req<check,err>"
          ]
