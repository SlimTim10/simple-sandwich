module Sandwich where

import qualified Bread
import qualified Condiment
import qualified Knife

import qualified Data.Maybe as Maybe
import qualified Data.List as L

data Sandwich = Sandwich
  { slices :: [Bread.Slice]
  , built :: Bool
  , isCut :: Bool
  }

new :: [Bread.Slice] -> Sandwich
new slices = Sandwich
  { slices = slices
  , built = False
  , isCut = False
  }

flavours :: Sandwich -> [Condiment.Condiment]
flavours = concat . map sliceFlavours . slices
  where
    sliceFlavours :: Bread.Slice -> [Condiment.Condiment]
    sliceFlavours = Maybe.catMaybes . map Bread.contents . sequence [Bread.top, Bread.bottom]

showFlavours :: Sandwich -> String
showFlavours = f . flavours
  where
    f :: [Condiment.Condiment] -> String
    f cs
      | length cs == 2 = L.intercalate " and " cs
      | otherwise = L.intercalate ", " (init cs) ++ ", and " ++ last cs

isReadyToEat :: Sandwich -> Bool
isReadyToEat sw = built sw && isCut sw

build :: Sandwich -> Either String Sandwich
build sw
  | built sw = Left "It's already a glorious tower of food!"
  | length (slices sw) < 2 = Left "Not enough slices"
  | outsideSmeared = Left "This sandwich would be icky to hold."
  | tooPlain = Left "This sandwich might actually be a loaf."
  | otherwise = Right (sw {built=True})
  where
    bottomSmeared :: Bool
    bottomSmeared = Bread.surfaceIsSmeared . Bread.bottom . head $ slices sw
    
    topSmeared :: Bool
    topSmeared = Bread.surfaceIsSmeared . Bread.top . last $ slices sw
    
    outsideSmeared :: Bool
    outsideSmeared = length (slices sw) >= 2 && (bottomSmeared || topSmeared)

    tooPlain :: Bool
    tooPlain = any Bread.sliceIsPlain . init . tail $ slices sw

cut :: Sandwich -> Knife.Knife -> Either String Sandwich
cut sw k
  | (not . built) sw = Left "Build the sandwich and then cut it in one glorious stroke."
  | Knife.isLoaded k = Left "No! You'll get the edge all yucky with that knife."
  | isCut sw = Left "One cut will do."
  | otherwise = Right (sw {isCut=True})
