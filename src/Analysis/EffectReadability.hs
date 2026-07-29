{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-unused-pattern-binds #-}

module Analysis.EffectReadability
  ( effectSummary
  ) where

import Import
import RIO
import RIO.Map ( (!?) )
import Util
import qualified RIO.Map as Map
import qualified Data.Set.Ordered as OSet
import qualified RIO.List as List
import Analysis.Common

-- | Generate a summary of an effect for analysis purposes
effectSummary :: Effect -> EffectSummary
effectSummary EffNone = EffSNone
effectSummary (EffLoop _) = EffSLoop
effectSummary (EffStateChange _) = EffSItem
effectSummary (EffAfter delay eff) = EffSAfter delay (effectSummary eff)
effectSummary (EffSeq effs) = EffSSeq $ OSet.fromList $ List.map effectSummary effs
effectSummary (EffBranch eff1 eff2) = EffSBranch (effectSummary eff1) (effectSummary eff2)
effectSummary (EffVar v) = EffSVar v
effectSummary (EffEvent lbl) = EffSEvent lbl
effectSummary (EffAlways lbl eff) = EffSAlways lbl (effectSummary eff)
effectSummary (EffEventually lbl eff) = EffSEventually lbl (effectSummary eff)
effectSummary (EffCancel lbl) = EffSCancel lbl
effectSummary (EffRemove lbl) = EffSRemove lbl
