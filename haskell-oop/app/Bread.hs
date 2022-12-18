module Bread where

import qualified Condiment
import qualified Knife

data Surface = Surface
  { contents :: Maybe Condiment.Condiment
  }

newSurface :: Surface
newSurface = Surface
  { contents = Nothing
  }

surfaceIsPlain :: Surface -> Bool
surfaceIsPlain Surface {contents=Nothing} = True
surfaceIsPlain _ = False

surfaceIsSmeared :: Surface -> Bool
surfaceIsSmeared = not . surfaceIsPlain

data Slice = Slice
  { top :: Surface
  , bottom :: Surface
  }

newSlice :: Slice
newSlice = Slice
  { top = newSurface
  , bottom = newSurface
  }

sliceIsPlain :: Slice -> Bool
sliceIsPlain Slice {top=t, bottom=b}
  = surfaceIsPlain t && surfaceIsPlain b

sliceIsSmeared :: Slice -> Bool
sliceIsSmeared = not . sliceIsPlain

smearSurface :: Knife.Knife -> Surface -> Either String (Knife.Knife, Surface)
smearSurface k s
  | surfaceIsSmeared s = Left "This surface was already smeared!"
  | Knife.isClean k = Left "This knife is too clean to smear with."
  | otherwise = Right (Knife.clean k, s {contents=Knife.contents k})
