{-# OPTIONS --without-K --safe #-}

open import Agda.Builtin.Maybe
  using (Maybe ; just ; nothing)
  public

open import Util

maybe : {A B : Type} → (A → B) → B → Maybe A → B
maybe j n (just x) = j x
maybe j n nothing  = n

map : {A B : Type} → (A → B) → Maybe A → Maybe B
map f = maybe (just ∘ f) nothing

-- Proof that A ∔ 𝟙 is isomorphic to Maybe A so we can use either one.
Maybe-isomorphism : {A : Type} → (A ∔ 𝟙) ≅ Maybe A
Maybe-isomorphism =
  Isomorphism
    (λ { (inl x) → just x ; (inr ⋆) → nothing})
    (Inverse
      (λ { (just x) → inl x ; nothing → inr ⋆})
      (λ { (inl x) → refl (inl x) ; (inr ⋆) → refl (inr ⋆)})
      λ { (just x) → refl (just x) ; nothing → refl nothing})
