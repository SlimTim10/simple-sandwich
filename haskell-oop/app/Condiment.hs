module Condiment where

type Condiment = String

data OpenOrClosed = Open | Closed
  deriving (Eq)

data Jar = Jar
  { contents :: Maybe Condiment
  , lid :: OpenOrClosed
  }

newJar :: Condiment -> Jar
newJar c = Jar
  { contents = Just c
  , lid = Closed
  }

isEmpty :: Jar -> Bool
isEmpty Jar{contents=Nothing} = True
isEmpty _ = False

hasStuff :: Jar -> Bool
hasStuff = not . isEmpty

isClosed :: Jar -> Bool
isClosed Jar{lid=Closed} = True
isClosed _ = False

closeJar :: Jar -> Jar
closeJar cj = cj {lid=Closed}

isOpen :: Jar -> Bool
isOpen = not . isClosed

openJar :: Jar -> Jar
openJar cj = cj {lid=Open}

relinquishContents :: Jar -> Either String (Jar, Condiment)
relinquishContents cj@Jar{contents=Just c}
  | isClosed cj = Left "The jar is closed and knife-impermeable."
  | isEmpty cj = Left "The jar is empty. How disappointing."
  | otherwise = Right (cj{contents=Nothing}, c)
