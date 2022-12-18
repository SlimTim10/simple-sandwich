module Condiment where

type Condiment = String

data OpenOrClosed = Open | Closed
  deriving (Eq)

data Jar = Jar
  { condiment :: Condiment
  , lid :: OpenOrClosed
  , empty :: Bool
  }

newJar :: Condiment -> Jar
newJar c = Jar
  { condiment = c
  , lid = Closed
  , empty = False
  }

isEmpty :: Jar -> Bool
isEmpty Jar{empty=True} = True
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
relinquishContents cj
  | isClosed cj = Left "The jar is closed and knife-impermeable."
  | isEmpty cj = Left "The jar is empty. How disappointing."
  | otherwise = Right (cj{empty=True}, condiment cj)
