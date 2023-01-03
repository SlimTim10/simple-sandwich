{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Maybe
  using (Maybe ; just ; nothing)

open import Util

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

open SliceOfBread' public

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
  × Maybe Condiment
  × Maybe Condiment

Sandwich : Type
Sandwich = Σ
  ((tsFlavour , tsSmearedTop , tsSmearedBottom)
    , (bsFlavour , bsSmearedTop , bsSmearedBottom)) ꞉ SliceOfBread × SliceOfBread
  , ((tsSmearedTop ≡ nothing)
    × (bsSmearedBottom ≡ nothing)
    × ((tsSmearedBottom ≢ nothing) ∔ (bsSmearedTop ≢ nothing)))
  × (Σ n ꞉ ℕ , n ≥ 1)

sw1 : Sandwich
sw1 = ((topSlice , bottomSlice) , shellOk , pieces)
  where
    topSlice = sourdough , nothing , just peanutButter
    bottomSlice = sourdough , just jelly , nothing
    shellOk = refl nothing , refl nothing , inl λ ()
    pieces = 2 , ⋆
