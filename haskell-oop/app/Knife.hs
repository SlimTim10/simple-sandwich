module Knife where

import qualified Condiment

data Knife = Knife
  { contents :: Maybe Condiment.Condiment
  }

new :: Knife
new = Knife {contents=Nothing}

isClean :: Knife -> Bool
isClean Knife {contents=Nothing} = True
isClean _ = False

clean :: Knife -> Knife
clean k = k {contents=Nothing}

isLoaded :: Knife -> Bool
isLoaded = not . isClean

loadFrom :: Knife -> Condiment.Jar -> Either String (Knife, Condiment.Jar)
loadFrom k cj
  | isLoaded k = Left "This knife is already loaded. Don't mix your condiments!"
  | otherwise = uncurry load <$> Condiment.relinquishContents cj
  where
    load cj' c = (k {contents=Just c}, cj')
