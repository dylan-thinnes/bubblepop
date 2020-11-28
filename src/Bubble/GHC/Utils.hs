{-# LANGUAGE TemplateHaskell #-}
module Bubble.GHC.Utils where

import Bubble.GHC.Classes
import Language.Haskell.TH.Syntax

occName :: Name -> OccName
occName (Name o _) = o

nameFlavour :: Name -> NameFlavour
nameFlavour (Name _ f) = f

errorEx :: Exp
errorEx = $([| error |] >>= lift)
