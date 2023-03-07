Categories as Semicategories with Identities
============================================

This is the Agda formalization accompanying the TYPES 2023 abstract of the same
title.

It depends on the [Agda 2.6.1-compatible
fork](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) of the
HoTT-Agda library, and typechecks in Agda version 2.6.2.2.

```agda
{-# OPTIONS --without-K --rewriting #-}
```

Contents
--------

1. Prelude:
```agda
import Notation
import Equivalence
```

2. The record type of wild semicategories, basic definitions and results on
morphisms:
```agda
import Semicategories
```

3. Results on idempotent equivalences:
```agda
import IdempotentEquivalences
```

4. Various notions of identity morphisms on semicategories, and proofs of their
mutual equivalence:
```agda
import Identities
```
