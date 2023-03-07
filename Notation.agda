{-# OPTIONS --without-K --rewriting #-}

module Notation where

open import HoTT

module _ {i} where
  ‖_‖ : Type i → Type i
  ‖_‖ = Trunc {i} -1

  ∣_∣ : {A : Type i} → A → ‖ A ‖
  ∣ a ∣  = [ a ]

Σ-syn = Σ
syntax Σ-syn A (λ x → B) = Σ[ x ﹕ A ] B

_↔_ : ∀ {i j} (A : Type i) (B : Type j) → Type (lmax i j)
A ↔ B = (A → B) × (B → A)
