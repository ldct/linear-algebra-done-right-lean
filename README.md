# Lean Companion to Axler's *Linear Algebra Done Right* (4e)

A Lean 4 companion to Sheldon Axler's [*Linear Algebra Done Right*](https://linear.axler.net/) (4th edition; freely available as a [PDF](https://linear.axler.net/LADR4e.pdf)).

Authored under the conventions in [companion-helper](https://github.com/rkirov/companion-helper):
mathlib definitions are used directly, with `recall` to bridge textbook axioms,
and `@[avoiding …]` from `companion-helper` to keep one-line mathlib lemmas
from trivializing exercises.

## Status

| Section | Drafted | Reviewed | Playtested |
|---|---|---|---|
| 1A. ℝⁿ and ℂⁿ | ✓ | ✓ | — |
| 1B. Definition of vector space | ✓ | — | — |
| 1C. Subspaces | ✓ | — | — |

## Layout

```
LinearAlgebraDoneRightLean/
├── Section_1A.lean
├── Section_1B.lean
└── Section_1C.lean
```

One file per section. Future chapters follow the same pattern (`Section_2A.lean`, …).

## Building

```bash
lake update mathlib && lake exe cache get   # first time only
lake build
```

Toolchain: `leanprover/lean4:v4.29.0`. Mathlib pinned at `v4.29.0`.

## License

Apache-2.0.
