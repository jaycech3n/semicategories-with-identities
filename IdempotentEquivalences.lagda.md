Idempotent Equivalences
=======================

In [*Internal ∞-Categorical Models of Dependent Type Theory: Towards 2LTT Eating
HoTT*](https://arxiv.org/abs/2009.01883) (Kraus 2021) it is shown that
idempotent equivalences are a particularly nice way to add identities to
semicategories.

In particular, they give a *propositional* notion of identity structure, without
requiring explicit truncation. This is shown in the aforementioned paper and the
accompanying Agda formalization at
<https://github.com/nicolaikraus/idempotentEquivalences>, most results of which
are reproduced here.

```agda
{-# OPTIONS --without-K --rewriting #-}

open import Semicategories

module IdempotentEquivalences {j₁ j₂} (C : Semicategory j₁ j₂) where

open import HoTT
open import Notation

open Semicategory C
```

An endomorphism i is called idempotent if `i ⋄ i == i`. Idempotent equivalences
are what they say on the cover.

```agda
module _ {x} (i : Hom x x) where
  is-idem : Type j₂
  is-idem = i ⋄ i == i

  is-idem-eqv : Type (lmax j₁ j₂)
  is-idem-eqv = is-eqv i × is-idem

idem-eqv : ∀ x → Type (lmax j₁ j₂)
idem-eqv x = Σ (Hom x x) is-idem-eqv
```

Idempotent equivalences are neutral.

```agda
module _ {x} (i : Hom x x) (e : is-eqv i) (idem : is-idem i) where
  idem-eqv-left-neut : is-left-neut i
  idem-eqv-left-neut f =
    i ⋄ f =⟨ ! (<–-inv-l i⋄≃ (i ⋄ f)) ⟩
    i⋄⁻¹ (i ⋄ i ⋄ f) =⟨ ap i⋄⁻¹ p ⟩
    i⋄⁻¹ (i ⋄ f) =⟨ <–-inv-l i⋄≃ f ⟩
    f =∎
    where
    module _ {w} where
      i⋄≃ : Hom w x ≃ Hom w x
      i⋄≃ = post⋄ i , fst e w
      i⋄ = –> i⋄≃
      i⋄⁻¹ = <– i⋄≃
    p : i ⋄ i ⋄ f == i ⋄ f
    p = ! ass ∙ ap (pre⋄ f) idem

  idem-eqv-right-neut : is-right-neut i
  idem-eqv-right-neut f =
    f ⋄ i =⟨ ! (<–-inv-l ⋄i≃ (f ⋄ i)) ∙ ap ⋄i⁻¹ ass ⟩
    ⋄i⁻¹ (f ⋄ i ⋄ i) =⟨ ap ⋄i⁻¹ p ⟩
    ⋄i⁻¹ (f ⋄ i) =⟨ <–-inv-l ⋄i≃ f ⟩
    f =∎
    where
    module _ {y} where
      ⋄i≃ : Hom x y ≃ Hom x y
      ⋄i≃ = pre⋄ i , snd e y
      ⋄i = –> ⋄i≃
      ⋄i⁻¹ = <– ⋄i≃
    p : f ⋄ i ⋄ i == f ⋄ i
    p = ap (post⋄ f) idem

  idem-eqv-neutral : is-neutral i
  idem-eqv-neutral = idem-eqv-left-neut , idem-eqv-right-neut
```

Thus, any two idempotent equivalences on the same object are equal.

```agda
uniq-idem-eqv : ∀ x (i i' : Hom x x) → is-idem-eqv i → is-idem-eqv i' → i == i'
uniq-idem-eqv x i i' e e' =
  ! (idem-eqv-right-neut i' (fst e') (snd e') i)
  ∙ idem-eqv-left-neut i (fst e) (snd e) i'
```

Given any equivalence `f : Hom x y` and `e : is-eqv f`, we get an idempotent
equivalence `ℐ e : Hom x x`.

```agda
module _ {x y} {f : Hom x y} (e : is-eqv f) where
  module _ {w} where
    _⋄∙≃ : Hom w x ≃ Hom w y
    _⋄∙≃ = post⋄ f , fst e _

    _⋄∙ : Hom w x → Hom w y
    _⋄∙ = –> _⋄∙≃

    _⋄∙⁻¹ : Hom w y → Hom w x
    _⋄∙⁻¹ = <– _⋄∙≃

  ℐ : Hom x x
  ℐ = _⋄∙⁻¹ f

  _⋄ℐ= : f ⋄ ℐ == f
  _⋄ℐ= = <–-inv-r _⋄∙≃ f

  ℐ_-eqv : is-eqv ℐ
  ℐ_-eqv = 2-of-3-pre ℐ f (transport is-eqv (! _⋄ℐ=) e) e

  ℐ_-left-neut : is-left-neut ℐ
  ℐ_-left-neut g =
    ℐ ⋄ g =⟨ ! (<–-inv-l _⋄∙≃ (ℐ ⋄ g)) ⟩
    _⋄∙⁻¹ (_⋄∙ (ℐ ⋄ g)) =⟨ ap _⋄∙⁻¹ (! ass) ⟩
    _⋄∙⁻¹ (_⋄∙ ℐ ⋄ g) =⟨ _⋄ℐ= |in-ctx (λ ◻ → _⋄∙⁻¹ (◻ ⋄ g)) ⟩
    _⋄∙⁻¹ (_⋄∙ g) =⟨ <–-inv-l _⋄∙≃ g ⟩
    g =∎

  ℐ_-idem : is-idem ℐ
  ℐ_-idem = ℐ_-left-neut ℐ

  ℐ_-idem-eqv : is-idem-eqv ℐ
  ℐ_-idem-eqv = ℐ_-eqv , ℐ_-idem
```

The type of identifications of an equivalence f with ℐ f is equivalent to the
type of witnesses of idempotence of f.

```agda
module _ {x} where
  ∙=ℐ≃idem∙ : (f : Hom x x) (e : is-eqv f) → (f == ℐ e) ≃ (f ⋄ f == f)
  ∙=ℐ≃idem∙ f e =
    f == ℐ e
      ≃⟨ ap-equiv (e ⋄∙≃) f (ℐ e) ⟩
    (e ⋄∙) f == (e ⋄∙) (ℐ e)
      ≃⟨ transport (λ ◻ → (f ⋄ f == (e ⋄∙) (ℐ e)) ≃ (f ⋄ f == ◻))
           (e ⋄ℐ=) (ide _) ⟩
    f ⋄ f == f ≃∎
```

Now we can prove that the type of idempotent equivalences on `x : Ob` is
propositional.

```agda
is-prop-idem-eqv : ∀ x → is-prop (idem-eqv x)
is-prop-idem-eqv x =
  all-paths-is-prop (λ{ i → prop-has-all-paths ⦃ is-prop-lem i ⦄ i })
  where module _ (i : idem-eqv x) where
    i→ = fst i
    i→-idem-eqv = snd i

    ≃-lem : idem-eqv x ≃ is-eqv i→
    ≃-lem =
      Σ[ f ﹕ Hom x x ] is-eqv f × is-idem f
        ≃⟨ Σ-emap-r (λ f →
           Σ-emap-r (λ e → (∙=ℐ≃idem∙ f e)⁻¹)) ⟩
      Σ[ f ﹕ Hom x x ] Σ[ e ﹕ is-eqv f ] (f == ℐ e)
        ≃⟨ Σ-emap-r (λ f →
           Σ-emap-r (λ e →
             transport-equiv (f ==_)
               (uniq-idem-eqv x _ _ (ℐ e -idem-eqv) i→-idem-eqv))) ⟩
      Σ[ f ﹕ Hom x x ] is-eqv f × (f == i→)
        ≃⟨ Σ-assoc ⁻¹ ∘e Σ-emap-r (λ _ → ×-comm) ⟩
      Σ (Σ[ f ﹕ Hom x x ] f == i→) (is-eqv ∘ fst)
        ≃⟨ (Σ-emap-l (is-eqv ∘ fst)
             ((contr-equiv-Unit (pathto-is-contr _))⁻¹)
           )⁻¹ ⟩
      Σ ⊤ (λ _ → is-eqv i→)
        ≃⟨ Σ₁-Unit ⟩
      is-eqv i→ ≃∎

    is-prop-lem : is-prop (idem-eqv x)
    is-prop-lem = equiv-preserves-level (≃-lem ⁻¹)
```
