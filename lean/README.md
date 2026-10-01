# Modular Lean development

[`ReverseLittlewoodOffordFC.lean`](ReverseLittlewoodOffordFC.lean) states the fully inlined
target: along odd $n$, $F_{2,1}(n)^{1/n}\to1/\sqrt2$. It is derived from
`ReverseLittlewoodOfford.rootSeq_tendsto`.

The development uses Lean **4.33.1** and Formal Conjectures `137aec5`, pinned in
[`lakefile.toml`](lakefile.toml); that revision pins mathlib `0df444a`.
[`lake-manifest.json`](lake-manifest.json) records every dependency. `lake --wfail build` completes
without warnings.

## Structure

| Part | Entry point | Status |
|---|---|---|
| Definitions | [`ReverseLittlewoodOfford/Defs.lean`](ReverseLittlewoodOfford/Defs.lean) | proved |
| Lemma 1: alternating sums in a half-plane | [`AlternatingSum.lean`](ReverseLittlewoodOfford/AlternatingSum.lean) | proved |
| Lemma 2: normal form | [`Normalization.lean`](ReverseLittlewoodOfford/Normalization.lean) | proved |
| Lemmas 3–4: pairs and hereditary deletion | [`HereditaryDeletion.lean`](ReverseLittlewoodOfford/HereditaryDeletion.lean) | proved |
| Lemmas 5, 7, 8: length, stability, concentration | [`Concentration.lean`](ReverseLittlewoodOfford/Concentration.lean) | proved |
| Lower bound (A) | [`LowerBound.lean`](ReverseLittlewoodOfford/LowerBound.lean) | proved |
| Hollom–Sorkin construction | [`UpperConstruction.lean`](ReverseLittlewoodOfford/UpperConstruction.lean) | proved |
| Squeeze lemma for the roots | [`Limit.lean`](ReverseLittlewoodOfford/Limit.lean) | proved |
| The limit | [`Rate.lean`](ReverseLittlewoodOfford/Rate.lean) | proved |
| Final theorem | [`ReverseLittlewoodOffordFC.lean`](ReverseLittlewoodOffordFC.lean) | derived |
| Component axiom audit | [`ReverseLittlewoodOffordVerified.lean`](ReverseLittlewoodOffordVerified.lean) | — |

## Build

Run from this directory:

```bash
lake exe cache get
lake --wfail build
```

Every component reports `[propext, Classical.choice, Quot.sound]`. See the
[main README](../README.md) for the outline and the [standalone version](../lean4web/README.md)
for Lean4Web.
