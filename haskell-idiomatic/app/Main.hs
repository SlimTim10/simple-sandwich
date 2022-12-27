module Main where

data UtensilShape = Knife | Spoon | Fork
  deriving (Show, Eq)

data Utensil = Utensil
  { uShape :: UtensilShape
  , uCondiment :: Maybe Condiment
  }
  deriving (Show)

fetchUtensil :: UtensilShape -> Utensil
fetchUtensil shape = Utensil
  { uShape = shape
  , uCondiment = Nothing
  }

data Condiment = PeanutButter | Jelly
  deriving (Show, Eq)

data OpenOrClosed = Open | Closed
  deriving (Show, Eq)

data CondimentJar = CondimentJar
  { cjCondiment :: Maybe Condiment
  , cjLid :: OpenOrClosed
  }
  deriving (Show)

fetchCondimentJar :: Condiment -> CondimentJar
fetchCondimentJar c = CondimentJar
  { cjCondiment = Just c
  , cjLid = Closed
  }

loadFrom :: Utensil -> CondimentJar -> Either String (Utensil, CondimentJar)
loadFrom _ CondimentJar{cjLid=Closed} = Left "The jar is closed and knife-impermeable."
loadFrom _ CondimentJar{cjCondiment=Nothing} = Left "The jar is empty. How disappointing."
loadFrom Utensil{uShape=Fork} _ = Left "Forks aren't the right shape for condiments."
loadFrom u cj@CondimentJar{cjCondiment=Just c}
  = Right (u { uCondiment = Just c }, cj { cjCondiment = Nothing })

openJar :: CondimentJar -> CondimentJar
openJar cj = cj { cjLid = Open }

data BreadFlavour = Sourdough | WholeGrain | White
  deriving (Show)

data SliceOfBread = SliceOfBread
  { sobFlavour :: BreadFlavour
  , sobTop :: Maybe Condiment
  , sobBottom :: Maybe Condiment
  }
  deriving (Show)

fetchSliceOfBread :: BreadFlavour -> SliceOfBread
fetchSliceOfBread flavour = SliceOfBread
  { sobFlavour = flavour
  , sobTop = Nothing
  , sobBottom = Nothing
  }

data Surface = Top | Bottom
  deriving (Show, Eq)

smearSliceOfBread :: Utensil -> Surface -> SliceOfBread -> Either String (SliceOfBread, Utensil)
smearSliceOfBread u surface slice
  | uShape u /= Knife = Left "You can't smear with that!"
  | uCondiment u == Nothing = Left "This knife is too clean to smear with."
  | surface == Top && sobTop slice /= Nothing = Left "This surface was already smeared!"
  | surface == Bottom && sobBottom slice /= Nothing = Left "This surface was already smeared!"
  | otherwise = Right (smearedSlice, cleanUtensil)
  where
    smearedSlice
      | surface == Top = slice { sobTop = uCondiment u }
      | surface == Bottom = slice { sobBottom = uCondiment u }
    cleanUtensil = u { uCondiment = Nothing}

data Sandwich = Sandwich
  { swBottom :: SliceOfBread
  , swTop :: SliceOfBread
  , swPieces :: [(SliceOfBread, SliceOfBread)]
  }
  deriving (Show)

makeSandwich :: SliceOfBread -> SliceOfBread -> Either String Sandwich
makeSandwich bottom top
  | sobTop bottom == Nothing && sobBottom top == Nothing = Left "This sandwich might actually be a loaf."
  | sobTop top /= Nothing || sobBottom bottom /= Nothing = Left "This sandwich would be icky to hold."
  | otherwise = Right Sandwich { swBottom = bottom, swTop = top, swPieces = [(bottom, top)] }

-- A sandwich is always cut through all the pieces, doubling them all
cutSandwich :: Utensil -> Sandwich -> Either String Sandwich
cutSandwich u sw
  | uShape u == Fork || uShape u == Spoon = Left "You can't cut a sandwich with that!"
  | uCondiment u /= Nothing = Left "No! You'll get the edge all yucky with that knife."
  | otherwise = Right sw { swPieces = newPieces }
  where
    newPieces = concat [swPieces sw, swPieces sw]

main :: IO ()
main = do
  let knife = fetchUtensil Knife
  let pb = fetchCondimentJar PeanutButter
  let jelly = fetchCondimentJar Jelly

  -- First attempt. Didn't open the jar of peanut butter.
  either printError putStrLn $ do
    (pbKnife, emptyPB) <- knife `loadFrom` pb -- Problem
    return "Sandwich made!"

  -- Next attempt. Too plain.
  either printError putStrLn $ do
    (pbKnife, emptyPB) <- knife `loadFrom` openJar pb
    (jellyKnife, emptyJelly) <- knife `loadFrom` openJar jelly
    let bottomSlice = fetchSliceOfBread Sourdough
    let topSlice = fetchSliceOfBread WholeGrain
    sw <- makeSandwich bottomSlice topSlice
    return "Sandwich made!"

  -- Successful sandwich making!
  either printError putStrLn $ do
    (pbKnife, emptyPB) <- knife `loadFrom` openJar pb
    (jellyKnife, emptyJelly) <- knife `loadFrom` openJar jelly
    let bottomSlice = fetchSliceOfBread Sourdough
    let topSlice = fetchSliceOfBread WholeGrain
    (bottomSliceWithPB, cleanKnife) <- smearSliceOfBread pbKnife Top bottomSlice
    (topSliceWithJelly, cleanKnife) <- smearSliceOfBread jellyKnife Bottom topSlice
    sw <- makeSandwich bottomSliceWithPB topSliceWithJelly
    return "Sandwich made!"
  where
    printError :: String -> IO ()
    printError e = putStrLn ("Error: " ++ e)
