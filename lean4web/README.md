# Standalone Lean4Web file

[`ReverseLittlewoodOffordLean4Web.lean`](ReverseLittlewoodOffordLean4Web.lean) contains the whole
development in one mathlib-only file. It is generated from [`../lean`](../lean) by
[`../tools/export_lean4web.py`](../tools/export_lean4web.py); edit the modular files and rerun the
script instead of editing this file.

**Try it in Lean4Web** (after the repository is published):
[open the standalone file](https://live.lean-lang.org/#project=mathlib-stable&url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Freverse-littlewood-offord-lean%2Frefs%2Fheads%2Fmain%2Flean4web%2FReverseLittlewoodOffordLean4Web.lean)

The file was checked locally with Lean **4.33.0** and the mathlib revision in
[`lakefile.toml`](lakefile.toml). It compiles without warnings, and the final report is:

```text
'ReverseLittlewoodOfford.reverse_littlewood_offord_rate' depends on axioms:
[propext, Classical.choice, Quot.sound]
```

The file also prints the same report for every component. It takes about 20 seconds to check
locally once mathlib is loaded; Lean4Web may take longer.

To load a local copy, select the Stable mathlib project and use **Load → Load file from disk**.

## Local check

Run from this directory:

```bash
lake update
lake exe cache get
lake env lean ReverseLittlewoodOffordLean4Web.lean
```

See the [main README](../README.md) for the outline and the [modular development](../lean/README.md)
for the source modules.
