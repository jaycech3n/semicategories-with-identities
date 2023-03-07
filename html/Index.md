Categories as Semicategories with Identities
============================================

This is the Agda formalization accompanying the TYPES 2023 abstract of the same
title.

It depends on the [Agda 2.6.1-compatible
fork](https://github.com/awswan/HoTT-Agda/tree/agda-2.6.1-compatible) of the
HoTT-Agda library, and typechecks in Agda version 2.6.2.2.

<pre class="Agda"><a id="366" class="Symbol">{-#</a> <a id="370" class="Keyword">OPTIONS</a> <a id="378" class="Pragma">--without-K</a> <a id="390" class="Pragma">--rewriting</a> <a id="402" class="Symbol">#-}</a>
</pre>
Contents
--------

1. Prelude:
<pre class="Agda"><a id="450" class="Keyword">import</a> <a id="457" href="Notation.html" class="Module">Notation</a>
<a id="466" class="Keyword">import</a> <a id="473" href="Equivalence.html" class="Module">Equivalence</a>
</pre>
2. The record type of wild semicategories, basic definitions and results on
morphisms:
<pre class="Agda"><a id="585" class="Keyword">import</a> <a id="592" href="Semicategories.html" class="Module">Semicategories</a>
</pre>
3. Results on idempotent equivalences:
<pre class="Agda"><a id="659" class="Keyword">import</a> <a id="666" href="IdempotentEquivalences.html" class="Module">IdempotentEquivalences</a>
</pre>
4. Various notions of identity morphisms on semicategories, and proofs of their
mutual equivalence:
<pre class="Agda"><a id="802" class="Keyword">import</a> <a id="809" href="Identities.html" class="Module">Identities</a>
</pre>