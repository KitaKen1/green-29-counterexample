# A Lean counterexample to Green's Open Problem 29

This repository formalizes a negative solution to the exact target
[`Green29.green_29`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/29.lean)
registered in Formal Conjectures.

Green's question asks whether every `K`-approximate group `A` contains a large subset `S ⊆ A`
such that `S ^ 8 ⊆ A ^ 4`, with a lower bound for `|S| / |A|` that is polynomial in `K`.
The answer is **no**.

**Try it in Lean4Web:**
[open the standalone proof](https://live.lean-lang.org/#url=https%3A%2F%2Fraw.githubusercontent.com%2FKitaKen1%2Fgreen-29-counterexample%2Frefs%2Fheads%2Fmain%2Flean4web%2FGreen29Lean4Web.lean)

The proof is adapted from the
[public validator solution](https://conjectures.io/v1/results/82ab85ee-5dfc-4775-b3e1-8abc16e213b9/solution),
which is credited publicly to submitting hotkey
`5GeGrYFpMrNSh3Nwcx987zWz4cME9A9NbCkEbjBvv4uLUScV`.
Its published digest is
`sha256:cd39995efd69cfa3f64e6dbf93ba236c672a2de0b3d6ea815b718e2c0bfeaa5c`.
The repository files add imports, namespaces, and explicit target wrappers, so that digest applies
to the published original `Main.lean`, not to the adapted files in this repository.

## Formal Conjectures target

The file in `lean/` imports the validator-pinned Formal Conjectures declaration and proves the
proposed solved form:

```lean
theorem green_29_solved :
    answer(False) ↔
      ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
        ∀ {G : Type*} [Group G] [DecidableEq G] (K : ℝ) (A : Finset G),
          1 ≤ K → IsApproximateSubgroup K (A : Set G) →
            ∃ S ⊆ A, C * K ^ (-c) * (A.card : ℝ) ≤ (S.card : ℝ) ∧
            S ^ 8 ⊆ A ^ 4
```

Thus `Green29.green_29` can be changed from `research open` to `research solved` by replacing
`answer(sorry)` with `answer(False)` and citing a stable proof artifact.

The separate declaration `Green29.green_29.variant` is already marked `research solved`.  It does
not require `S ⊆ A` and is not contradicted or reproved here.

## Mathematical explanation (AI generated)

Let `H` be an arbitrarily large finite group and work in

```text
G = Multiplicative ℤ × H.
```

Define

```text
A = ({-1} × H) ∪ ({+1} × H) ∪ {(0, 1)}.
```

This is a genuine `3`-approximate group:

- it contains the identity;
- it is closed under inversion;
- `A²` is covered by the three translates indexed by integer coordinates `-1`, `0`, and `1`.

Its size is `2|H| + 1`.  On the other hand, suppose that `S ⊆ A` and `S⁸ ⊆ A⁴`.  Every element of
`A⁴` has integer coordinate between `-4` and `4`.  If an element `s ∈ S` has integer coordinate
`q`, then `s⁸ ∈ A⁴` has coordinate `8q`, so

```text
-4 ≤ 8q ≤ 4.
```

Hence `q = 0`.  The only element of `A` in the zero layer is `(0, 1)`, and therefore `|S| ≤ 1`.
For fixed `K = 3`, the proposed lower bound `C · 3⁻ᶜ · |A|` grows without bound as `|H|` grows,
which is impossible.

The known variant survives: the middle subgroup `{0} × H` is large and satisfies the required
product-set inclusion, but it is not contained in `A`.

## Files

| Directory | Lean version | Purpose |
|---|---:|---|
| `lean/` | `v4.27.0` | Exact Formal Conjectures version, pinned to commit `379fc029...` |
| `lean4web/` | `v4.27.0` | Standalone mathlib-only version for Lean4Web |

Each directory contains one proof file, `lakefile.toml`, `lean-toolchain`, and the generated
`lake-manifest.json`.

## Verification

Formal Conjectures version:

```bash
cd lean
lake update
lake exe cache get
lake build
```

Standalone mathlib/Lean4Web version:

```bash
cd lean4web
lake update
lake exe cache get
lake build
```

Both proof files contain no `sorry`, `admit`, custom axiom, `native_decide`, or `unsafe` theorem.
Their final `#print axioms` commands report only Lean's standard axioms:

```text
[propext, Classical.choice, Quot.sound]
```

## Status boundary

What is proved here:

```text
The exact proposition on the right-hand side of Green29.green_29 is false.
The correct answer recorded by Formal Conjectures should therefore be answer(False).
```

What is not claimed here:

- that the status update has already merged into Formal Conjectures main;
- that the already-solved `green_29.variant` is new or false;
- a human identity for the submitter beyond the public hotkey attribution;
- a novelty or prior-publication claim beyond settlement of the exact formal target.

The current public result records `verification_status=VERIFIED`,
`manual_review_status=APPROVED`, `reward_status=REWARDED`, and `solution_available=true`.
The production report also records `same_statement=true` and `lean_kernel_passed=true`.
As of 2026-08-22, Formal Conjectures main still labels the declaration `research open`, so the
remaining gap is upstream metadata/proof-link synchronization rather than validator acceptance.

## Sources

- [Green's Open Problem 29](https://people.maths.ox.ac.uk/greenbj/papers/open-problems.pdf#problem.29)
- [Formal Conjectures: current `GreensOpenProblems/29.lean`](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/GreensOpenProblems/29.lean)
- [Validator-pinned Formal Conjectures target](https://github.com/google-deepmind/formal-conjectures/blob/379fc0298dc146df549e7061c3ede0353a5bb51f/FormalConjectures/GreensOpenProblems/29.lean)
- [Public verification report](https://conjectures.io/v1/results/82ab85ee-5dfc-4775-b3e1-8abc16e213b9/report)
- [Certified public result](https://conjectures.io/v1/results/82ab85ee-5dfc-4775-b3e1-8abc16e213b9)
- [Public submitted `Main.lean`](https://conjectures.io/v1/results/82ab85ee-5dfc-4775-b3e1-8abc16e213b9/solution)
- [Detailed validator review notes (draft text; current status is the certified result above)](https://github.com/conjectures-io/conjectures-validator/blob/main/docs/review-decisions/2026-08-06-green-29.md)

## AI usage disclosure

The proof and repository were developed with assistance from OpenAI Codex.
