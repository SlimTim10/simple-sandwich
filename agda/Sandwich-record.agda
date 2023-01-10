{-# OPTIONS --without-K --safe #-}

open import Util
open import Maybe
  renaming (_≡_ to _≗_)

data Surface : Type where
  top bottom : Surface

data Condiment : Type where
  peanutButter jelly : Condiment

data BreadFlavour : Type where
  sourdough wholeGrain white : BreadFlavour

record SliceOfBread : Type where
  constructor sliceOfBread
  field
    flavour : BreadFlavour
    -- smearedTop : Condiment ∔ 𝟙
    smearedTop : Maybe Condiment
    -- smearedBottom : Condiment ∔ 𝟙
    smearedBottom : Maybe Condiment

open SliceOfBread

checkShell : SliceOfBread → SliceOfBread → Type
checkShell t b =
  is-nothing (smearedTop t)
  × is-nothing (smearedBottom b)
  × (is-just (smearedBottom t) ∔ is-just (smearedTop b))

-- A sandwich consists of a top and bottom (slices of bread). Neither the top or bottom can be smeared on the outside. At least one of the bottom or top must be smeared on the inside. The sandwich may be in one or more pieces (i.e., it can be cut).
record Sandwich : Type where
  constructor sandwich
  field
    topSlice : SliceOfBread
    bottomSlice : SliceOfBread
    shellOk : checkShell topSlice bottomSlice
    pieces : Σ n ꞉ ℕ , n ≥ 1

open Sandwich

swExample1 : Sandwich
swExample1 = sandwich t b (refl , refl , inl (peanutButter , refl)) (2 , ⋆)
  where
  t = sliceOfBread sourdough nothing (just peanutButter)
  b = sliceOfBread sourdough (just jelly) nothing

data UtensilShape : Type where
  knife spoon fork : UtensilShape

-- A utensil has a shape and may be loaded with a condiment (if it is the right shape).
record Utensil : Type where
  constructor utensil
  field
    shape : UtensilShape
    loadedWith : Maybe ((shape ≡ knife) × Condiment)

open Utensil

knifeExample1 : Utensil
knifeExample1 = utensil knife (just (refl knife , peanutButter))

-- Fetch a utensil of a specified shape.
-- The returned utensil should be the specified shape (not just any utensil) and not loaded (clean).
fetchUtensil
  : (s : UtensilShape)
  → Σ u ꞉ Utensil , (shape u ≡ s) × is-nothing (loadedWith u)
fetchUtensil s = utensil s nothing , refl s , refl

data OpenOrClosed : Type where
  open' closed : OpenOrClosed

record CondimentJar : Type where
  constructor condimentJar
  field
    condiment : Maybe Condiment
    state : OpenOrClosed

open CondimentJar

-- Fetch a jar of a given condiment.
-- The returned jar should contain the specified condiment and be closed.
fetchCondimentJar
  : (c : Condiment)
  → Σ cj ꞉ CondimentJar , (condiment cj ≡ just c) × (state cj ≡ closed)
fetchCondimentJar c = condimentJar (just c) closed , refl (just c) , refl closed

pr₂-inv : {A B : Type} {b : B} → (pr₂ ∘ (λ (a : A) → b , a)) ∼ id
pr₂-inv = refl

map-inv : {A B : Type} {b : B} (ma : Maybe A) → ma ≡ map pr₂ (map (λ (a : A) → b , a) ma)
map-inv {A} {B} {b} (just x) = refl (just x)
map-inv {A} {B} {b} nothing = refl nothing

-- Load a clean knife with a condiment from a jar that is open and full.
-- Take a utensil that is a knife and clean.
-- Take a condiment jar that is full and open.
-- Return the knife, now loaded with the condiment from the jar,
--   and the condiment jar, still open but now empty.
loadFrom
  : ((u , isKnife , notLoaded) :
    Σ u ꞉ Utensil , (shape u ≡ knife) × is-nothing (loadedWith u))
  → ((cj , _) :
    Σ cj ꞉ CondimentJar , is-just (condiment cj) × (state cj ≡ open'))
  → Σ (u' , cj') ꞉ Utensil × CondimentJar
    , (shape u' ≡ shape u) -- Same shape (*the* knife)
      × (condiment cj ≡ map pr₂ (loadedWith u')) -- Loaded with condiment from jar
      × (state cj' ≡ state cj) -- State unchanged (still open)
      × is-nothing (condiment cj') -- Now empty
loadFrom
  (u , isKnife , notLoaded)
  (cj , isFull , isOpen)
  = (record u { loadedWith = loadedWith' } , record cj { condiment = nothing })
    , refl (shape u) , isLoaded' , refl (state cj) , refl
  where
  loadedWith' : Maybe ((shape u ≡ knife) × Condiment)
  loadedWith' = map (λ x → isKnife , x) (condiment cj)

  isLoaded' : condiment cj ≡ map pr₂ loadedWith'
  isLoaded' = map-inv (condiment cj)

-- Open a condiment jar.
openJar
  : (cj : CondimentJar)
  → Σ cj' ꞉ CondimentJar , (condiment cj' ≡ condiment cj) × (state cj' ≡ open')
openJar cj = record cj { state = open' } , refl (condiment cj) , refl open'

-- Fetch a slice of bread of a specified flavour.
-- The returned slice should be the specified flavour and be unsmeared on both sides.
fetchSliceOfBread
  : (f : BreadFlavour)
  → Σ sob ꞉ SliceOfBread
    , (flavour sob ≡ f)
      × is-nothing (smearedTop sob)
      × is-nothing (smearedBottom sob)
fetchSliceOfBread f = sliceOfBread f nothing nothing , refl f , refl , refl

-- Smear a slice of bread with a knife loaded with a condiment.
-- Take a knife that is loaded with a condiment.
-- Take a surface (top or bottom).
-- Take a slice of bread that is not already smeared on the specified surface.
-- Return the slice of bread with nothing changed but the smeared surface,
--   and the knife, now unloaded.
smearSliceOfBread
  : ((u , _ , _) :
    Σ u ꞉ Utensil , (shape u ≡ knife) × is-just (loadedWith u))
  → (sur : Surface)
  → ((sob , _) :
    Σ sob ꞉ SliceOfBread
    , ((sur ≡ top) × is-nothing (smearedTop sob))
      ∔ ((sur ≡ bottom) × is-nothing (smearedBottom sob)))
  → Σ (sob' , u') ꞉ SliceOfBread × Utensil
    , (flavour sob' ≡ flavour sob) -- Same flavour
      × (
        -- Smear the top
        ((sur ≡ top)
          × (smearedTop sob' ≡ map pr₂ (loadedWith u)) -- Top of slice is smeared with condiment from knife
          × (smearedBottom sob' ≡ smearedBottom sob)) -- Bottom unchanged
        ∔
        -- Smear the bottom
        ((sur ≡ bottom)
          × (smearedBottom sob' ≡ map pr₂ (loadedWith u)) -- Bottom of slice is smeared with condiment from knife
          × (smearedTop sob' ≡ smearedTop sob))) -- Top unchanged
        × (shape u' ≡ shape u) -- Same shape utensil
        × is-nothing (loadedWith u') -- Unloaded utensil

smearSliceOfBread
  (u , _)
  top
  (sob , _)
  = (record sob { smearedTop = t' } , record u { loadedWith = nothing })
    , refl (flavour sob) , smearTop
  where
  t' : Maybe Condiment
  t' = map pr₂ (loadedWith u)

  smearTop = inl (refl top , refl t' , refl (smearedBottom sob)) , refl (shape u) , refl

smearSliceOfBread
  (u , _)
  bottom
  (sob , _)
  = (record sob { smearedBottom = b' } , record u { loadedWith = nothing })
    , refl (flavour sob) , smearBottom
  where
  b' : Maybe Condiment
  b' = map pr₂ (loadedWith u)
  
  smearBottom = (inr (refl bottom , refl b' , refl (smearedTop sob))) , refl (shape u) , refl

smearExample1 : SliceOfBread × Utensil
smearExample1 = pr₁ (smearSliceOfBread pbKnife top bottomSlice')
  where
  pbKnife = (utensil knife (just (refl knife , peanutButter))) , refl knife , (refl knife , peanutButter) , refl
  bottomSlice' = (sliceOfBread sourdough nothing nothing) , inl (refl top , refl)

-- First attempt. Didn't open the jar of peanut butter.
sandwichAttempt1 : Sandwich
sandwichAttempt1 = {!!}
  where
  -- Not possible because the pb jar isn't open
  step1 = loadFrom (myKnife , (refl knife , refl)) (pb , ((peanutButter , refl) , {!!}))
    where
    myKnife = pr₁ (fetchUtensil knife)
    pb = pr₁ (fetchCondimentJar peanutButter)
    j = pr₁ (fetchCondimentJar jelly)

  topSlice' = pr₁ (fetchSliceOfBread wholeGrain)
  bottomSlice' = pr₁ (fetchSliceOfBread sourdough)

-- Next attempt. Too plain. Tried to use slices without spreading condiments on them.
sandwichAttempt2 : Sandwich
sandwichAttempt2 = sandwich topSlice' bottomSlice' (refl , refl , {!!}) (1 , ⋆)
  where
  topSlice' = pr₁ (fetchSliceOfBread wholeGrain)
  bottomSlice' = pr₁ (fetchSliceOfBread sourdough)

  step1 = loadFrom (myKnife , refl knife , refl) (pr₁ (openJar pb) , (peanutButter , refl) , refl open')
    where
    myKnife = pr₁ (fetchUtensil knife)
    pb = pr₁ (fetchCondimentJar peanutButter)
    j = pr₁ (fetchCondimentJar jelly)

  pbKnife : Utensil
  pbKnife = pr₁ (pr₁ step1)
  emptyPB : CondimentJar
  emptyPB = pr₂ (pr₁ step1)

-- Successful sandwich making!
sandwichAttempt3 : Sandwich
sandwichAttempt3 = sandwich topSliceWithJelly bottomSliceWithPB (refl , (refl , inl (jelly , refl))) (1 , ⋆)
  where
  step1 : Σ _ ꞉ Utensil × CondimentJar , _
  step1 =
    let
      newKnife = pr₁ (fetchUtensil knife)
      pb = pr₁ (fetchCondimentJar peanutButter)
    in loadFrom (newKnife , refl knife , refl) (pr₁ (openJar pb) , (peanutButter , refl) , refl open')

  step2 : Σ _ ꞉ SliceOfBread × Utensil , _
  step2 =
    let
      bottomSlice = pr₁ (fetchSliceOfBread sourdough)
      pbKnife = pr₁ (pr₁ step1)
      emptyPB = pr₂ (pr₁ step1)
    in
      smearSliceOfBread
      (pbKnife , (refl (shape pbKnife)) , ((refl (shape pbKnife)) , peanutButter) , refl)
      top
      (bottomSlice , (inl (refl top , refl)))

  bottomSliceWithPB : SliceOfBread
  bottomSliceWithPB = pr₁ (pr₁ step2)
  
  step3 : Σ _ ꞉ SliceOfBread × Utensil , _
  step3 =
    let
      jellyKnife : Utensil
      jellyKnife =
        let
          usedKnife = pr₂ (pr₁ step2)
          j = pr₁ (fetchCondimentJar jelly)
        in pr₁ (pr₁ (loadFrom (usedKnife , (refl knife , refl)) (pr₁ (openJar j) , (jelly , refl) , refl open')))
      topSlice = pr₁ (fetchSliceOfBread wholeGrain)
    in
      smearSliceOfBread
      (jellyKnife , (refl knife , (refl knife , jelly) , refl))
      bottom
      (topSlice , (inr (refl bottom , refl)))
  
  topSliceWithJelly : SliceOfBread
  topSliceWithJelly = pr₁ (pr₁ step3)
