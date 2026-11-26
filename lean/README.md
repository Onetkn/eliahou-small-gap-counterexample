# Formal refutation of the small-gap conjecture

This is a standalone Lean project for the counterexample in `../paper/main.tex`.
It uses Lean 4.36.0 and Mathlib revision
`fc4f59e577feb1a4956671bc04ac18aaaf8cd842`.

The final declaration is:

```lean
Eliahou.Counterexample.not_smallGapConjecture : ¬ genericSmallGapConjecture
```

The theorem `Eliahou.Counterexample.counterexample_family` proves all
semantic properties and the negative general invariant for every admissible
scale. `Statement.lean` states the original implication for arbitrary sets,
multiplicities and full-tail cutoffs. Its depth is ceiling division, rather
than a hardcoded constant. The family also has the actual least conductor.

The formal definitions quantify over all natural numbers. They define the
generated additive monoid, adjoin the entire conductor tail, and define
primitive and decomposable elements by their intrinsic additive meaning.
The proof connects these sets to weighted coefficient tuples, proves the
unique encoding, and derives their cardinalities. The numerical coefficient
counts are evaluated from a proved recurrence by the Lean kernel.

This does not check a bounded list of numerical semigroups. The construction
and its semantic bounds are uniform in the scale parameter `M >= 1000000`.
The ordinary Eliahou definition uses the actual multiplicity and conductor;
the statement layer connects it to the calculation with depth eight.

`Audit.lean` requests transitive axiom dependencies. The verifier rejects
anything outside Lean's standard `propext`, `Classical.choice`, and
`Quot.sound`. No `sorry`, custom mathematical axiom, or `native_decide` is
used to establish the result.

## Setup

Install Python 3.12 or newer, elan, and the GitHub CLI. The source bootstrap
uses the authenticated GitHub API; authenticate `gh`, or provide `GH_TOKEN`
through the environment. No credentials are written into the repository.

On Linux or macOS, from this directory:

```sh
elan toolchain install leanprover/lean4:v4.36.0
python bootstrap_mathlib.py
MATHLIB_NO_CACHE_ON_UPDATE=1 lake update
lake build cache
lake env python cache_mathlib.py
python verify.py --json ../results/lean-verification.json
```

On Windows, with the same prerequisites:

```powershell
elan toolchain install leanprover/lean4:v4.36.0
.\fetch_mathlib_cache.ps1
.\verify.ps1 --json ../results/lean-verification.json
```

Official source snapshots and build products are ignored. Their pinned
revisions are in `source-lock.json`. The helpers prefer a local isolated
elan installation when present and otherwise use `lake` on `PATH`.

The optional `../ci/verify.yml` template can be installed at
`.github/workflows/verify.yml`. It is not active in this repository; the
included verification report records the local build and axiom audit.
