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
  × Maybe Condiment -- Top side
  -- × Condiment ∔ 𝟙
  × Maybe Condiment -- Bottom side

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

-- Fetch a utensil of a specified shape.
-- The returned utensil should be the specified shape, not just any utensil.
fetchUtensil
  : (s : UtensilShape)
  → Σ (s' , _) ꞉ Utensil , s' ≡ s
fetchUtensil shape = (shape , nothing) , (refl shape)

data OpenOrClosed : Type where
  open' closed : OpenOrClosed

CondimentJar : Type
CondimentJar = Maybe Condiment × OpenOrClosed

-- Fetch a jar of a given condiment.
-- The returned jar should contain the specified condiment and be closed.
fetchCondimentJar
  : (c : Condiment)
  → Σ (c' , oc) ꞉ CondimentJar , (c' ≡ just c) × (oc ≡ closed)
fetchCondimentJar c = ((just c , closed) , (refl (just c) , refl closed))

pr₂-inv : {A B : Type} {b : B} → (pr₂ ∘ (λ (a : A) → b , a)) ∼ id
pr₂-inv = refl

lemma1 : {A B : Type} {b : B} (ma : Maybe A) → ma ≡ map pr₂ (map (λ (a : A) → b , a) ma)
lemma1 {A} {B} {b} (just x) = refl (just x)
lemma1 {A} {B} {b} nothing = refl nothing

-- Load a clean knife with a condiment from a jar that is open and full.
-- Take a utensil that is a knife and clean.
-- Take a condiment jar that is full and open.
-- Return the knife, now loaded with the condiment from the jar,
--   and the condiment jar, still open but now empty.
loadFrom
  : (((s , loadedWith) , (isKnife , notLoaded)) :
    Σ (s , loadedWith) ꞉ Utensil , (s ≡ knife) × (is-nothing loadedWith))
  → (((c , state) , (isFull , isOpen)) :
    Σ (c , state) ꞉ CondimentJar , (is-just c) × (state ≡ open'))
  → Σ ((s' , loadedWith') , (c' , state')) ꞉ Utensil × CondimentJar
    , (s' ≡ s) -- Same shape
      × (c ≡ map pr₂ loadedWith') -- Loaded with condiment from jar
      × (state' ≡ state) -- State unchanged (still open)
      × (is-nothing c') -- Now empty
loadFrom
  ((s , loadedWith) , (isKnife , notLoaded))
  ((c , state) , (isFull , isOpen))
  = ((s , loadedWith') , (nothing , state)) , (refl s , isLoaded' , refl state , refl)
  where
    loadedWith' : Maybe (((s ≡ knife) × Condiment))
    loadedWith' = map (λ x → isKnife , x) c

    isLoaded' : c ≡ map pr₂ loadedWith'
    isLoaded' = lemma1 c

-- Open a condiment jar.
openJar
  : ((c , state) : CondimentJar)
  → Σ (c' , state') ꞉ CondimentJar , (c' ≡ c) × (state' ≡ open')
openJar (c , state) = ((c , open') , refl c , refl open')

-- Fetch a slice of bread of a specified flavour.
-- The returned slice should be the specified flavour and be unsmeared on both sides.
fetchSliceOfBread
  : (f : BreadFlavour)
  → Σ (f' , t , b) ꞉ SliceOfBread , (f ≡ f') × (t ≡ nothing) × (b ≡ nothing)
fetchSliceOfBread f = ((f , nothing , nothing) , refl f , refl nothing , refl nothing)

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
    myKnife = pr₁ (fetchUtensil knife)
    pb = pr₁ (fetchCondimentJar peanutButter)
    j = pr₁ (fetchCondimentJar jelly)

    -- (pbKnife, emptyPB) = 