# Prospective Formal Conjectures statement

This directory contains an unofficial draft of the odd-$n$ exponential-rate question for the
reverse Littlewood–Offord problem at radius one, in the style of
[Formal Conjectures](https://github.com/google-deepmind/formal-conjectures).

It has not been submitted, reviewed, approved or merged. The proposed destination is
`FormalConjectures/Arxiv/2503.24202/ReverseLittlewoodOfford.lean`.

## File

[`ReverseLittlewoodOfford.lean`](ReverseLittlewoodOfford.lean) contains one declaration,
`Arxiv.«2503.24202».reverse_littlewood_offord_rate`. The full mathematical statement is in the
theorem itself; it does not depend on project-local helper definitions.

The two occurrences of `sorry` are intentional in this statement draft:

- `answer(sorry)` leaves the value of the limit open;
- `by sorry` is the placeholder proof expected for an open problem statement.

The same inlined statement, with the answer `1 / Real.sqrt 2`, is the target of
[`../lean`](../lean). Its `research open` tag records the status in the cited literature, not the
local development.

## Local check

Copy the file into a Formal Conjectures checkout as
`FormalConjectures/Arxiv/2503.24202/ReverseLittlewoodOfford.lean`, then run:

```bash
lake --wfail build 'FormalConjectures.Arxiv.«2503.24202».ReverseLittlewoodOfford'
```

This repository pins the Formal Conjectures revision in [`../lean/lakefile.toml`](../lean/lakefile.toml).
