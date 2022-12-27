module Main where

import qualified Condiment
import qualified Knife
import qualified Bread
import qualified Sandwich

main :: IO ()
main = do
  let bread = replicate 5 Bread.newSlice
  let pb = Condiment.newJar "Peanut Butter"
  let jelly = Condiment.newJar "Jelly"
  let knife = Knife.new

  -- First attempt. Didn't open the jar of peanut butter.
  either printError putStrLn $ do
    (pbKnife, pbEmpty) <- knife `Knife.loadFrom` pb -- Problem
    (usedKnife1, surface1) <- Bread.smearSurface pbKnife . Bread.top . head $ bread
    (jellyKnife, jellyEmpty) <- knife `Knife.loadFrom` Condiment.openJar jelly
    (usedKnife2, surface2) <- Bread.smearSurface jellyKnife . Bread.bottom . last $ bread
    let sw = Sandwich.new bread
    Sandwich.build sw
    return "Sandwich made!"

  -- Next attempt. Used too much bread inside.
  either printError putStrLn $ do
    (pbKnife, pbEmpty) <- knife `Knife.loadFrom` Condiment.openJar pb
    (usedKnife1, surface1) <- Bread.smearSurface pbKnife . Bread.top . head $ bread
    (jellyKnife, jellyEmpty) <- knife `Knife.loadFrom` Condiment.openJar jelly
    (usedKnife2, surface2) <- Bread.smearSurface jellyKnife . Bread.bottom . last $ bread
    let sw = Sandwich.new bread
    Sandwich.build sw -- Problem
    return "Sandwich made!"

  -- Successful sandwich making!
  either printError putStrLn $ do
    (pbKnife, pbEmpty) <- knife `Knife.loadFrom` Condiment.openJar pb
    (usedKnife1, surface1) <- Bread.smearSurface pbKnife . Bread.top . head $ bread
    (jellyKnife, jellyEmpty) <- knife `Knife.loadFrom` Condiment.openJar jelly
    (usedKnife2, surface2) <- Bread.smearSurface jellyKnife . Bread.bottom . last $ bread
    let sw = Sandwich.new [head bread, last bread]
    Sandwich.build sw
    return "Sandwich made!"
  where
    printError :: String -> IO ()
    printError e = putStrLn ("Error: " ++ e)
