{-# OPTIONS --without-K --rewriting #-}

module Equivalence where

open import HoTT

module _ {j₁ j₂ j₃} {A : Type j₁} {B : Type j₂} {C : Type j₃}
  (f : A → B) (g : B → C) (gf-equiv : is-equiv (g ∘ f))
  where
  gfe : A ≃ C
  gfe = g ∘ f , gf-equiv

  gf⁻¹ : C → A
  gf⁻¹ = <– gfe

  2-of-3-pre : is-equiv g → is-equiv f
  2-of-3-pre g-equiv =
    is-eq f (gf⁻¹ ∘ g) homotopy (<–-inv-l gfe)
    where
    ge = g , g-equiv
    g⁻¹ = <– ge

    homotopy : ∀ b → f (gf⁻¹ (g b)) == b
    homotopy b =
      f (gf⁻¹ (g b)) =⟨ ! (<–-inv-l ge (f (gf⁻¹ (g b)))) ⟩
      g⁻¹ (g (f (gf⁻¹ (g b)))) =⟨ <–-inv-r gfe (g b) |in-ctx g⁻¹ ⟩
      g⁻¹ (g b) =⟨ <–-inv-l ge b ⟩
      b =∎

  2-of-3-post : is-equiv f → is-equiv g
  2-of-3-post f-equiv = is-eq g (f ∘ gf⁻¹) (<–-inv-r gfe) homotopy
    where
    fe = f , f-equiv
    f⁻¹ = <– fe

    homotopy : ∀ b → f (gf⁻¹ (g b)) == b
    homotopy b =
      f (gf⁻¹ (g b)) =⟨ ! (<–-inv-r fe b) |in-ctx f ∘ gf⁻¹ ∘ g ⟩
      f (gf⁻¹ (g (f (f⁻¹ b)))) =⟨ <–-inv-l gfe _ |in-ctx f ⟩
      f (f⁻¹ b) =⟨ <–-inv-r fe b ⟩
      b =∎
