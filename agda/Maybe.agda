{-# OPTIONS --without-K #-}

data Maybe {a} (A : Set a) : Set a where
  just : A → Maybe A
  nothing : Maybe A
  
open import Util
  hiding (_≡_ ; ¬_ ; _≢_)

private
  variable
    A : Type
    B : Type

-- Need dependent identity
data _≡_ {a} {A : Set a} (x : A) : A → Set a where
  instance refl : x ≡ x

infix 0 _≡_

maybe : (A → B) → B → Maybe A → B
maybe j n (just x) = j x
maybe j n nothing  = n

fromMaybe : A → Maybe A → A
fromMaybe = maybe id

-- Dependent
maybe' : ∀ {a b} {A : Set a} {B : Maybe A → Set b} →
        ((x : A) → B (just x)) → B nothing → (x : Maybe A) → B x
maybe' j n (just x) = j x
maybe' j n nothing  = n

map : (A → B) → Maybe A → Maybe B
map f = maybe' (just ∘ f) nothing

-- is-just : Maybe A → Type
-- is-just (just _) = 𝟙
-- is-just nothing  = 𝟘

-- is-nothing : Maybe A → Type
-- is-nothing (just _) = 𝟘
-- is-nothing nothing = 𝟙

map-nothing : ∀ {f : A → B} {ma} → ma ≡ nothing → map f ma ≡ nothing
map-nothing refl = refl

map-just : ∀ {f : A → B} {ma a} → ma ≡ just a → map f ma ≡ just (f a)
map-just refl = refl

is-just : Maybe A → Type
is-just {A} ma = Σ a ꞉ A , ma ≡ just a

map-preserves-just : ∀ {f : A → B} {ma} → is-just ma → is-just (map f ma)
map-preserves-just {A} {a} {b} {ma} (x , y) = (b x) , map-just y

is-nothing : Maybe A → Type
is-nothing ma = ma ≡ nothing

map-preserves-nothing : ∀ {f : A → B} {ma} → is-nothing ma → is-nothing (map f ma)
map-preserves-nothing refl = refl

-- Proof that A ∔ 𝟙 is isomorphic to Maybe A, so we can use either one.
Maybe-isomorphism : {A : Type} → (A ∔ 𝟙) ≅ Maybe A
Maybe-isomorphism =
  Isomorphism
    (λ { (inl x) → just x ; (inr ⋆) → nothing})
    (Inverse
      (λ { (just x) → inl x ; nothing → inr ⋆})
      (λ { (inl x) → refl (inl x) ; (inr ⋆) → refl (inr ⋆)})
      λ { (just x) → refl (just x) ; nothing → refl nothing})
