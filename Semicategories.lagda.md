Morphisms in Wild Semicategories
================================

Semicategories are "categories without identities". We develop the theory of
morphisms in such structures in HoTT. We use the general notion of a *wild*
semicategory, i.e. where no truncation conditions are required.

```agda
{-# OPTIONS --without-K --rewriting #-}

module Semicategories where

open import HoTT
open import Notation

import Equivalence
```

A *wild semicategory* consists of:
  + a type of objects `Ob`,
  + a type family of morphisms `Hom`, and
  + an associative composition operation `⋄`.

This is of course just a wild category without identities. Note that we do *not*
ask for set-truncation: Ob and Hom are arbitrary types/type families.

```agda
record Semicategory j₁ j₂ : Type (lsucc (lmax j₁ j₂)) where
  infixr 40 _⋄_
  field
    Ob  : Type j₁
    Hom : Ob → Ob → Type j₂
    _⋄_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    ass : ∀ {x y z w} {f : Hom z w} {g : Hom y z} {h : Hom x y}
          → (f ⋄ g) ⋄ h == f ⋄ (g ⋄ h)
```

For the rest of this file we work in a generic wild semicategory.

  Pre- and Post-composition
  -------------------------

  ```agda
  pre⋄ : ∀ {x y z} → Hom x y → Hom y z → Hom x z
  pre⋄ f g = g ⋄ f

  post⋄ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
  post⋄ g f = g ⋄ f
  ```

  An endomorphism `i : Hom y y` is *left neutral* if it acts trivially by
  post-composition on `Hom x y` for any `x : Ob`.

  Similarly, it's *right neutral* if it acts trivially by pre-composition on
  `Hom y z` for any `z : Ob`.

  ```agda
  module _ {y} (i : Hom y y) where
    is-left-neut = ∀ {x} → post⋄ i ∼ idf (Hom x y)
    is-right-neut = ∀ {z} → pre⋄ i ∼ idf (Hom y z)

    is-neutral = is-left-neut × is-right-neut
  ```

  A morphism `f : Hom x y` is *left invertible* if, for any `w : Ob`, its
  post-composition with `Hom w x` is an equivalence of types.

  It's *right invertible* if its pre-composition with `Hom y z` is an
  equivalence of types for any `z : Ob`.

  ```agda
  module _ {x y} (f : Hom x y) where
    is-left-inv = ∀ w → is-equiv (post⋄ {w} f)
    is-right-inv = ∀ z → is-equiv (pre⋄ {z = z} f)
  ```

  It's easily seen that left (right) neutral morphisms are left (right)
  invertible.

  ```agda
  module _ {y} (i : Hom y y) where
    left-neut-left-inv : is-left-neut i → is-left-inv i
    left-neut-left-inv lneut _ = is-eq (post⋄ i) (idf _) lneut lneut

    right-neut-right-inv : is-right-neut i → is-right-inv i
    right-neut-right-inv rneut _ = is-eq (pre⋄ i) (idf _) rneut rneut
  ```

  Equivalences
  ------------

  The notion of an equivalence in a semicategory is fundamental.

  A morphism `f : Hom x y` is called a *equivalence* if it is both left- and
  right-invertible. Following Harpaz, we may also call f an *invertible
  morphism*.

  ```agda
  is-eqv : ∀ {x y} → Hom x y → Type (lmax j₁ j₂)
  is-eqv f = is-left-inv f × is-right-inv f
  ```

  In particular, any neutral morphism is an equivalence.

  ```agda
  is-neutral-is-eqv : ∀ {x} (f : Hom x x) → is-neutral f → is-eqv f
  is-neutral-is-eqv f neut =
    left-neut-left-inv f (fst neut)
    , right-neut-right-inv f (snd neut)
  ```

  We write `eqv x y` for the type of equivalences from x to y.

  ```agda
  eqv : Ob → Ob → Type (lmax j₁ j₂)
  eqv x y = Σ (Hom x y) is-eqv

  syntax eqv x y = x ≅ y

  module _ {x y} (e : x ≅ y) where
    —> : Hom x y -- That's an em-dash, \em
    —> = fst e

    eqv-of : is-eqv —>
    eqv-of = snd e
  ```

  Equivalences satisfy the 2-out-of-3 property:

  ```agda
  module _ {x y z} (f : Hom x y) (g : Hom y z) (e : is-eqv (g ⋄ f)) where
    g⋄∘f⋄-equiv : ∀ {x} → is-equiv (post⋄ {x} g ∘ post⋄ f)
    g⋄∘f⋄-equiv = transport is-equiv (λ= (λ _ → ass)) (fst e _)

    ⋄f∘⋄g-equiv : ∀ {z} → is-equiv (pre⋄ {z = z} f ∘ pre⋄ g)
    ⋄f∘⋄g-equiv = transport is-equiv (λ= (λ _ → ! ass)) (snd e _)

    2-of-3-pre : is-eqv g → is-eqv f
    2-of-3-pre g-eqv = f-left-inv , f-right-inv
      where
      f-left-inv : is-left-inv f
      f-left-inv w = Equivalence.2-of-3-pre (post⋄ f) (post⋄ g)
        g⋄∘f⋄-equiv (fst g-eqv _)

      f-right-inv : is-right-inv f
      f-right-inv z = Equivalence.2-of-3-post (pre⋄ g) (pre⋄ f)
        ⋄f∘⋄g-equiv (snd g-eqv _)

    2-of-3-post : is-eqv f → is-eqv g
    2-of-3-post f-eqv = g-left-inv , g-right-inv
      where
      g-left-inv : is-left-inv g
      g-left-inv w = Equivalence.2-of-3-post (post⋄ f) (post⋄ g)
        g⋄∘f⋄-equiv (fst f-eqv _)

      g-right-inv : is-right-inv g
      g-right-inv z = Equivalence.2-of-3-pre (pre⋄ g) (pre⋄ f)
        ⋄f∘⋄g-equiv (snd f-eqv _)
  ```

  Initial and Terminal Morphisms
  ------------------------------

  We may consider the (*very* wild!) "slice/coslice non-associative
  semicategories" of a wild semicategory, and formulate the notion of initial
  and terminal morphisms in such.

  ```agda
  initial-under : (x : Ob) {y : Ob} → Hom x y → Type (lmax j₁ j₂)
  initial-under x {y} f =
    (z : Ob) (h : Hom x z) → is-contr (Σ[ g ﹕ Hom y z ] g ⋄ f == h)

  terminal-over : {x : Ob} (y : Ob) → Hom x y → Type (lmax j₁ j₂)
  terminal-over {x} y g =
    (w : Ob) (h : Hom w y) → is-contr (Σ[ f ﹕ Hom w x ] g ⋄ f == h)
  ```

  With the contractible map definition of equivalence of types, the properties
  of left and right invertibility are just terminality-over and
  initiality-under.

  ```agda
  module _ {x y} (f : Hom x y) where
    left-inv-terminal-over : is-left-inv f → terminal-over y f
    left-inv-terminal-over f-left-inv w = equiv-is-contr-map (f-left-inv w)

    terminal-over-left-inv : terminal-over y f → is-left-inv f
    terminal-over-left-inv term w = contr-map-is-equiv (term w)

    right-inv-initial-under : is-right-inv f → initial-under x f
    right-inv-initial-under f-right-inv z = equiv-is-contr-map (f-right-inv z)

    initial-under-right-inv : initial-under x f → is-right-inv f
    initial-under-right-inv init z = contr-map-is-equiv (init z)
  ```

  Immediate corollary: equivalences are exactly those morphisms initial under
  their source and terminal over their target.

  ```agda
    is-eqv-initial-and-terminal :
      is-eqv f
      → initial-under x f × terminal-over y f
    is-eqv-initial-and-terminal f-eqv =
      right-inv-initial-under (snd f-eqv)
      , left-inv-terminal-over (fst f-eqv)

    initial-and-terminal-is-eqv :
      initial-under x f × terminal-over y f
      → is-eqv f
    initial-and-terminal-is-eqv (init , term) =
      terminal-over-left-inv term
      , initial-under-right-inv init
  ```
