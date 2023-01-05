{-# OPTIONS --without-K --safe #-}

open import Util
open import Maybe

data Surface : Type where
  top bottom : Surface

data Condiment : Type where
  peanutButter jelly : Condiment

data BreadFlavour : Type where
  sourdough wholeGrain white : BreadFlavour

record SliceOfBread' : Type where
  constructor sliceOfBread
  field
    flavour : BreadFlavour
    -- smearedTop : Condiment ∔ 𝟙
    smearedTop : Maybe Condiment
    -- smearedBottom : Condiment ∔ 𝟙
    smearedBottom : Maybe Condiment

open SliceOfBread'

checkShell : SliceOfBread' → SliceOfBread' → Type
checkShell
  (sliceOfBread tsFlavour tsSmearedTop tsSmearedBottom)
  (sliceOfBread bsFlavour bsSmearedTop bsSmearedBottom)
  = (tsSmearedTop ≡ nothing)
    × (bsSmearedBottom ≡ nothing)
    × ((tsSmearedBottom ≢ nothing) ∔ (bsSmearedTop ≢ nothing))

record Sandwich' : Type where
  constructor sandwich
  field
    topSlice : SliceOfBread'
    bottomSlice : SliceOfBread'
    shellOk : checkShell topSlice bottomSlice
    pieces : Σ n ꞉ ℕ , n ≥ 1

SliceOfBread : Type
SliceOfBread =
  BreadFlavour
  -- × Condiment ∔ 𝟙
  × Maybe Condiment
  -- × Condiment ∔ 𝟙
  × Maybe Condiment

-- A sandwich consists of a top and bottom (slices of bread). Neither the top or bottom can be smeared on the outside. The bottom and top must not both be unsmeared on the inside. The sandwich may be in one or more pieces (i.e., it can be cut).
Sandwich : Type
Sandwich = Σ
  ((tsFlavour , tsSmearedTop , tsSmearedBottom) ,
    (bsFlavour , bsSmearedTop , bsSmearedBottom)) ꞉ SliceOfBread × SliceOfBread
  , ((tsSmearedTop ≡ nothing)
    × (bsSmearedBottom ≡ nothing)
    × ((tsSmearedBottom ≢ nothing) ∔ (bsSmearedTop ≢ nothing)))
  × (Σ n ꞉ ℕ , n ≥ 1)

swExample1 : Sandwich
swExample1 = (topSlice , bottomSlice) , shellOk , pieces
  where
    topSlice = (sourdough , nothing , just peanutButter)
    bottomSlice = (sourdough , just jelly , nothing)
    shellOk = (refl nothing , refl nothing , inl λ ())
    pieces = (2 , ⋆)

data UtensilShape : Type where
  knife spoon fork : UtensilShape

-- A utensil has a shape and may be loaded with a condiment (if it is the right shape).
Utensil : Type
-- Utensil = UtensilShape × Condiment
Utensil = Σ shape ꞉ UtensilShape , Maybe ((shape ≡ knife) × Condiment)

knifeExample1 : Utensil
knifeExample1 = (knife , just (refl knife , peanutButter))

record Utensil' : Type where
  constructor utensil
  field
    shape : UtensilShape
    loadedWith : Maybe ((shape ≡ knife) × Condiment)

open Utensil'

knifeExample1' : Utensil'
knifeExample1' = utensil knife (just (refl knife , peanutButter))

fetchUtensil : UtensilShape → Utensil
fetchUtensil shape = (shape , nothing)

data OpenOrClosed : Type where
  open' closed : OpenOrClosed

CondimentJar : Type
CondimentJar = Condiment × OpenOrClosed

-- fetchCondimentJar
--   : (c : Condiment)
--   → (Σ (c' , oc) ꞉ CondimentJar , (c' ≡ c) × (oc ≡ open'))
-- fetchCondimentJar c = ((c , open') , (refl c , refl open'))

fetchCondimentJar
  : Condiment
  → CondimentJar
fetchCondimentJar c = (c , open')

-- openJar
--   : ((c , state) : CondimentJar)
--   → Σ (c' , state') ꞉ CondimentJar , (c' ≡ c) × (state' ≡ open')
-- openJar (c , state) = ((c , open') , refl c , refl open')

openJar
  : CondimentJar
  → Σ (_ , state') ꞉ CondimentJar , (state' ≡ open')
openJar (c , state) = ((c , open') , refl open')

-- fetchSliceOfBread
--   : (f : BreadFlavour)
--   → Σ (f' , t , b) ꞉ SliceOfBread , (f ≡ f') × (t ≡ nothing) × (b ≡ nothing)
-- fetchSliceOfBread f = ((f , nothing , nothing) , refl f , refl nothing , refl nothing)

fetchSliceOfBread
  : BreadFlavour
  → SliceOfBread
fetchSliceOfBread f = (f , nothing , nothing)

-- smearSliceOfBread
--   : (((_ , loadedWith) , _) : Σ (u , loadedWith) ꞉ Utensil , (u ≡ knife) × (loadedWith ≢ nothing))
--   → (s : Surface)
--   → (((f , _ , _) , _) :
--     Σ (f , t , b) ꞉ SliceOfBread , ((s ≡ top) × (t ≡ nothing)) ∔ ((s ≡ bottom) × (b ≡ nothing)))
--   → (Σ (f' , t' , b') ꞉ SliceOfBread , (f' ≡ f) × ((s ≡ top) × (t' ≡ just loadedWith)))
--     × Utensil
-- smearSliceOfBread u surface slice = {!!}

smearSliceOfBread
  : Σ (u , loadedWith) ꞉ Utensil , (u ≡ knife) × (loadedWith ≢ nothing)
  → (s : Surface)
  → Σ (f , t , b) ꞉ SliceOfBread , ((s ≡ top) × (t ≡ nothing)) ∔ ((s ≡ bottom) × (b ≡ nothing))
  → SliceOfBread × Utensil
smearSliceOfBread
  ((u , loadedWith) , _)
  s
  ((f , t , b) , _)
  = smearSurface s
  where
    smearSurface : Surface → SliceOfBread × Utensil
    smearSurface top = ((f , map pr₂ loadedWith , b) , (u , nothing))
    smearSurface bottom = ((f , t , map pr₂ loadedWith) , (u , nothing))

smearExample1 : SliceOfBread × Utensil
smearExample1 = smearSliceOfBread pbKnife top bottomSlice
  where
    pbKnife = (knife , just (refl knife , peanutButter)) , refl knife , (λ ())
    bottomSlice = (sourdough , nothing , nothing) , inl (refl top , refl nothing)


sandwichAttempt1 : Sandwich
sandwichAttempt1 = {!!}
  where
    myKnife = fetchUtensil knife
    pb = fetchCondimentJar peanutButter
    j = fetchCondimentJar jelly
