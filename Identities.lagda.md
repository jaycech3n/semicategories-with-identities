Notions of Identities in Semicategories
=======================================

We formulate various notions of propositional identity structure on
semicategories, and prove them equivalent.

```agda
{-# OPTIONS --without-K --rewriting #-}

module Identities where

open import HoTT
open import Semicategories
open import Notation

module _ {j₁ j₂} (C : Semicategory j₁ j₂) where
  open Semicategory C
```

  "Naive" Identities
  ------------------

  A "naive identity" is a morphism which is left- and right-neutral. This is the
  usual, well known definition. We take the -1-truncation because we are working
  in a *wild* semicategory but still want a propositional identity structure.

  ```agda
  NaivId = (x : Ob) → ‖ Σ (Hom x x) is-neutral ‖
  ```

  Idempotent Equivalences
  -----------------------

  An idempotent endomorphism f is one where f ⋄ f == f.

  In <cite Kraus '21> it is shown that *idempotent equivalences* are a
  particularly nice way to add identities to semicategories. The proof that
  these already form a proposition without requiring explicit truncation is
  given in <cite paper and Agda formalization>, and also reproduced in
  <IdempotentEquivalences.lagda.md>.

  ```agda
  open import IdempotentEquivalences C

  IdemEqv = (x : Ob) → idem-eqv x
  ```

  Harpaz Identities
  -----------------

  This is a non-univalent version of "completeness" as formulated by Harpaz.

  ```agda
  HarpazId = (x : Ob) → ‖ Σ[ y ﹕ Ob ] eqv x y ‖
  ```

  Initial and Terminal Morphisms
  ------------------------------

  The identity morphisms in a category are the initial and terminal objects in
  the under and over categories. We may formulate the analogous notion in our
  setting.

  ```agda
  SliceId =
    (x : Ob) → ‖ Σ[ f ﹕ Hom x x ] initial-under x f × terminal-over x f ‖
  ```

  Endo-equivalences
  -----------------

  Finally, we may ask that every object has an endomorphism that's an
  equivalence.

  ```agda
  EndoEqv = (x : Ob) → ‖ eqv x x ‖
  ```

  Equivalence of Identity Structures
  ----------------------------------

  All the structures are equivalent in semicategories: they express the notion
  of "having identity morphisms".

  We prove the following collection of equivalences:
  + Naive identities ⇔ Idempotent equivalences
  + Harpaz identities ⇒ Idempotent equivalences ⇒ Endo-equivalences ⇒ Harpaz identities
  + Endo-equivalences ⇔ Initial and terminal morphisms

  ```agda
  NaivId→IdemEqv : NaivId → IdemEqv
  NaivId→IdemEqv naiv x = Trunc-rec ⦃ is-prop-idem-eqv x ⦄
    (λ{ (f , neut) →
      let e = is-neutral-is-eqv f neut
      in ℐ e , (ℐ e -idem-eqv) })
    (naiv x)

  IdemEqv→NaivId : IdemEqv → NaivId
  IdemEqv→NaivId idemeqv x with idemeqv x
  ... | i , e , idem = ∣ i , idem-eqv-neutral i e idem ∣

  HarpazId→IdemEqv : HarpazId → IdemEqv
  HarpazId→IdemEqv harpaz x = Trunc-rec ⦃ is-prop-idem-eqv x ⦄
    (λ{ (y , f , e) → ℐ e , (ℐ e -idem-eqv) })
    (harpaz x)

  IdemEqv→EndoEqv : IdemEqv → EndoEqv
  IdemEqv→EndoEqv idemeqv x with idemeqv x
  ... | i , e , _ = ∣ i , e ∣

  EndoEqv→HarpazId : EndoEqv → HarpazId
  EndoEqv→HarpazId endoeqv x = Trunc-rec (λ{ f → ∣ x , f ∣ }) (endoeqv x)

  EndoEqv↔SliceId : EndoEqv ↔ SliceId
  EndoEqv↔SliceId = ⇒ , ⇐
    where
    ⇒ : EndoEqv → SliceId
    ⇒ endoeqv x = Trunc-rec
      (λ{ (f , e) → ∣ f , is-eqv-initial-and-terminal f e ∣ })
      (endoeqv x)

    ⇐ : SliceId → EndoEqv
    ⇐ sliceid x = Trunc-rec
      (λ{ (f , it) → ∣ f , initial-and-terminal-is-eqv f it ∣ })
      (sliceid x)
  ```
