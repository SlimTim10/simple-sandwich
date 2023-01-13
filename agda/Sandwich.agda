{-# OPTIONS --without-K --safe #-}

open import Util
open import Maybe
  renaming (_≡_ to _≗_)

-- A slice of bread has a top surface and bottom surface.
data Surface : Type where
  top bottom : Surface

-- We only have peanut butter and jelly in the pantry.
data Condiment : Type where
  peanutButter jelly : Condiment

-- Self-explanatory flavours of bread. Go for sourdough, it's the best.
data BreadFlavour : Type where
  sourdough wholeGrain white : BreadFlavour

-- A slice of bread is of a particular flavour and may be smeared with a condiment on the top or bottom (or both).
record SliceOfBread : Type where
  constructor sliceOfBread
  field
    flavour : BreadFlavour
    -- smearedTop : Condiment ∔ 𝟙
    smearedTop : Maybe Condiment
    -- smearedBottom : Condiment ∔ 𝟙
    smearedBottom : Maybe Condiment

-- Expose the SliceOfBread's constructor and fields to the rest of the code.
open SliceOfBread

-- Check that the "shell" of a sandwich is proper. The shell is the top and bottom slices of bread. Neither one should be smeared on the outside and at least one of them should be smeared on the inside.
-- I couldn't find a way to restrict the scope of this function to Sandwich (like using a "where" clause).
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

-- Expose the Sandwich's constructor and fields to the rest of the code.
open Sandwich

-- An example of a sandwich. This is a sourdough sandwich with peanut butter and jelly, cut into two pieces.
swExample1 : Sandwich
swExample1 = sandwich t b (refl , refl , inl (peanutButter , refl)) (2 , ⋆)
  where
  t = sliceOfBread sourdough nothing (just peanutButter)
  b = sliceOfBread sourdough (just jelly) nothing

-- We have knives, spoons, and forks. Chopsticks are too good to be utensils.
data UtensilShape : Type where
  knife spoon fork : UtensilShape

-- A utensil has a shape and may be loaded with a condiment (if it is a knife).
record Utensil : Type where
  constructor utensil
  field
    shape : UtensilShape
    loadedWith : Maybe ((shape ≡ knife) × Condiment)

-- Expose the Utensil's constructor and fields to the rest of the code.
open Utensil

-- An example of a knife, loaded with peanut butter. Resist the temptation to lick it!
knifeExample1 : Utensil
knifeExample1 = utensil knife (just (refl knife , peanutButter))

-- Fetch a utensil of a specified shape.
-- The returned utensil should be the specified shape (not just any utensil) and not loaded (clean).
fetchUtensil
  : (s : UtensilShape)
  → Σ u ꞉ Utensil , (shape u ≡ s) × is-nothing (loadedWith u)
fetchUtensil s = utensil s nothing , refl s , refl

-- A jar can be open or closed.
data OpenOrClosed : Type where
  open' closed : OpenOrClosed

-- A condiment jar has a condiment inside (or nothing, if it's empty) and is either open or closed.
record CondimentJar : Type where
  constructor condimentJar
  field
    condiment : Maybe Condiment
    state : OpenOrClosed

-- Expose the CondimentJar's constructor and fields to the rest of the code.
open CondimentJar

-- Fetch a jar of a given condiment.
-- The returned jar should contain the specified condiment and be closed.
fetchCondimentJar
  : (c : Condiment)
  → Σ cj ꞉ CondimentJar , (condiment cj ≡ just c) × (state cj ≡ closed)
fetchCondimentJar c = condimentJar (just c) closed , refl (just c) , refl closed

-- A Maybe value is left unchanged if we map it to the second value of a pair and project that second value.
-- Needed to prove this for part of loadFrom (following).
map-pr₂-pair-refl
  : {A B : Type} {b : B} (ma : Maybe A)
  → ma ≡ map pr₂ (map (λ (a : A) → (b , a)) ma)
map-pr₂-pair-refl {A} {B} {b} (just x) = refl (just x)
map-pr₂-pair-refl {A} {B} {b} nothing = refl nothing

-- Tried to generalize the property. (Didn't end up using this.)
pr₂-pair-refl : {A B : Type} {b : B} → (pr₂ ∘ (λ (a : A) → (b , a))) ∼ id
pr₂-pair-refl = refl

-- Another variation.
map-pr₂-pair-refl'
  : {A B : Type} {b : B}
  → map pr₂ ∘ map (λ (a : A) → (b , a)) ∼ id
map-pr₂-pair-refl' {A} {B} {b} (just x) = refl (just x)
map-pr₂-pair-refl' {A} {B} {b} nothing = refl nothing

-- Load a clean knife with a condiment from a jar that is open and full.
-- Take a utensil that is a knife and clean.
-- Take a condiment jar that is full and open.
-- Return the knife, now loaded with the condiment from the jar,
--   and the condiment jar, still open but now empty.
loadFrom
  : (uₛ : Σ u ꞉ Utensil , (shape u ≡ knife) × is-nothing (loadedWith u))
    (cjₛ : Σ cj ꞉ CondimentJar , is-just (condiment cj) × (state cj ≡ open'))
  → Σ (u' , cj') ꞉ Utensil × CondimentJar
    , (shape u' ≡ shape (pr₁ uₛ)) -- Same shape (*the* knife)
      × (condiment (pr₁ cjₛ) ≡ map pr₂ (loadedWith u')) -- Loaded with condiment from jar
      × (state cj' ≡ state (pr₁ cjₛ)) -- State unchanged (still open)
      × is-nothing (condiment cj') -- Now empty
loadFrom
  (u , isKnife , notLoaded)
  (cj , isFull , isOpen)
  = (record u { loadedWith = loadedWith' } , record cj { condiment = nothing })
    , refl (shape u) , isLoaded' , refl (state cj) , refl
  where
  loadedWith' : Maybe ((shape u ≡ knife) × Condiment)
  loadedWith' = map (λ x → (isKnife , x)) (condiment cj)

  isLoaded' : condiment cj ≡ map pr₂ loadedWith'
  isLoaded' = map-pr₂-pair-refl (condiment cj)

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
  : (uₛ : Σ u ꞉ Utensil , (shape u ≡ knife) × is-just (loadedWith u))
    (sur : Surface)
    (sobₛ : Σ sob ꞉ SliceOfBread
    , ((sur ≡ top) × is-nothing (smearedTop sob))
      ∔ ((sur ≡ bottom) × is-nothing (smearedBottom sob)))
  → Σ (sob' , u') ꞉ SliceOfBread × Utensil
    , (flavour sob' ≡ flavour (pr₁ sobₛ)) -- Same flavour
      × (
        -- Smear the top
        ((sur ≡ top)
          × (smearedTop sob' ≡ map pr₂ (loadedWith (pr₁ uₛ))) -- Top of slice is smeared with condiment from knife
          × (smearedBottom sob' ≡ smearedBottom (pr₁ sobₛ))) -- Bottom unchanged
        ∔
        -- Smear the bottom
        ((sur ≡ bottom)
          × (smearedBottom sob' ≡ map pr₂ (loadedWith (pr₁ uₛ))) -- Bottom of slice is smeared with condiment from knife
          × (smearedTop sob' ≡ smearedTop (pr₁ sobₛ)))) -- Top unchanged
        × (shape u' ≡ shape (pr₁ uₛ)) -- Same shape utensil
        × is-nothing (loadedWith u') -- Unloaded utensil

-- Top smearing.
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

-- Bottom smearing.
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

-- A smearing example, where a slice of sourdough bread is smeared with peanut butter on the top.
smearExample1 : SliceOfBread × Utensil
smearExample1 = pr₁ (smearSliceOfBread pbKnife top mySlice)
  where
  pbKnife = (utensil knife (just (refl knife , peanutButter))) , refl knife , (refl knife , peanutButter) , refl
  mySlice = (sliceOfBread sourdough nothing nothing) , inl (refl top , refl)

-- Now onto the best part! Making sandwiches...

-- First attempt. Didn't open the jar of peanut butter.
sandwichAttempt1 : Sandwich
sandwichAttempt1 = {!!}
  where
  -- Get a knife with peanut butter.
  step1 : Σ _ ꞉ Utensil × CondimentJar , _
  step1 =
    let
      newKnife : Utensil
      newKnife = pr₁ (fetchUtensil knife)
      pb : CondimentJar
      pb = pr₁ (fetchCondimentJar peanutButter)
    -- Not possible because the pb jar isn't open!
    in loadFrom (newKnife , (refl knife , refl)) (pb , ((peanutButter , refl) , {!!})) -- closed ≡ open'

-- Next attempt. Too plain. Tried to use slices without spreading condiments on them.
sandwichAttempt2 : Sandwich
sandwichAttempt2 = sandwich topSlice' bottomSlice' (refl , refl , {!!}) (1 , ⋆)
  where
  -- Get a knife with peanut butter.
  step1 : Σ _ ꞉ Utensil × CondimentJar , _
  step1 =
    let
      newKnife : Utensil
      newKnife = pr₁ (fetchUtensil knife)
      pb : CondimentJar
      pb = pr₁ (fetchCondimentJar peanutButter)
    in loadFrom (newKnife , (refl knife , refl)) (pr₁ (openJar pb) , ((peanutButter , refl) , refl open'))

  -- Get a couple slices of bread.
  topSlice' : SliceOfBread
  topSlice' = pr₁ (fetchSliceOfBread wholeGrain)
  bottomSlice' : SliceOfBread
  bottomSlice' = pr₁ (fetchSliceOfBread sourdough)

-- Successful sandwich making!
sandwichAttempt3 : Sandwich
sandwichAttempt3 = sandwich topSliceWithJelly bottomSliceWithPB (refl , (refl , inl (jelly , refl))) (1 , ⋆)
  where
  -- Get a knife with peanut butter.
  step1 : Σ _ ꞉ Utensil × CondimentJar , _
  step1 =
    let
      newKnife : Utensil
      newKnife = pr₁ (fetchUtensil knife)
      pb : CondimentJar
      pb = pr₁ (fetchCondimentJar peanutButter)
    in loadFrom (newKnife , refl knife , refl) (pr₁ (openJar pb) , (peanutButter , refl) , refl open')

  -- Get a slice of bread and smear it with the PB knife.
  step2 : Σ _ ꞉ SliceOfBread × Utensil , _
  step2 =
    let
      bottomSlice : SliceOfBread
      bottomSlice = pr₁ (fetchSliceOfBread sourdough)
      pbKnife : Utensil
      pbKnife = pr₁ (pr₁ step1)
      emptyPB : CondimentJar
      emptyPB = pr₂ (pr₁ step1)
    in
      smearSliceOfBread
      (pbKnife , (refl (shape pbKnife)) , ((refl (shape pbKnife)) , peanutButter) , refl)
      top
      (bottomSlice , (inl (refl top , refl)))

  -- Our successfuly smeared slice to be used as the bottom of the sandwich!
  bottomSliceWithPB : SliceOfBread
  bottomSliceWithPB = pr₁ (pr₁ step2)

  -- Get another slice of bread and smear it with jelly, using the same knife as before.
  step3 : Σ _ ꞉ SliceOfBread × Utensil , _
  step3 =
    let
      jellyKnife : Utensil
      jellyKnife =
        let
          -- The knife is now clean after having spread all its peanut butter on the other slice.
          usedKnife : Utensil
          usedKnife = pr₂ (pr₁ step2)
          j : CondimentJar
          j = pr₁ (fetchCondimentJar jelly)
        in pr₁ (pr₁ (loadFrom (usedKnife , (refl knife , refl)) (pr₁ (openJar j) , (jelly , refl) , refl open')))
      topSlice : SliceOfBread
      topSlice = pr₁ (fetchSliceOfBread wholeGrain)
    in
      smearSliceOfBread
      (jellyKnife , (refl knife , (refl knife , jelly) , refl))
      bottom
      (topSlice , (inr (refl bottom , refl)))

  -- Our successfully smeared slice to be used as the top of the sandwich!
  topSliceWithJelly : SliceOfBread
  topSliceWithJelly = pr₁ (pr₁ step3)
