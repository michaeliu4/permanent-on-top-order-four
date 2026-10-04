# Permanent-on-top bounds in order four

This standalone Lean 4 package contains the current Level 3, full-coverage formalization of the seven headline results formalized from *Permanent-on-top bounds in order four*. It preserves the proof-source bytes, imports, declaration names, and namespaces from protected source commit `b3da9c75451546c72845b58d74308222adb5f9ae` of `Agentic-Systems-LLC/proof-centered-math-lab`.

The public `Results` library imports `Results.SoulesPotOrderFour.Solution.Main`. It contains the exact transitive proof closure: `Defs.lean` and all 34 files under `Solution/`. The challenge file with placeholder proofs and the source repository's definition tests are intentionally outside this standalone results library.

## Formalized results

The exported declarations are:

- `Results.SoulesPotOrderFour.main` — Theorem 1.1;
- `Results.SoulesPotOrderFour.theorem_1_2_bounds` — Theorem 1.2, bounds;
- `Results.SoulesPotOrderFour.theorem_1_2_zero_offdiag` — Theorem 1.2, zero off-diagonal case;
- `Results.SoulesPotOrderFour.theorem_1_3_cutoff` — Theorem 1.3;
- `Results.SoulesPotOrderFour.theorem_3_2_loewner` — Theorem 3.2;
- `Results.SoulesPotOrderFour.theorem_3_3_cutoff_loewner` — Theorem 3.3; and
- `Results.SoulesPotOrderFour.section_5_6_lambdaMax_eq` — the Section 5.6 equality.

The formalization does not assume a published theorem outside Mathlib. The order-three result quoted in the paper is proved in `Solution/ZeroOrder3.lean`. Ten exact rational sum-of-squares certificates are embedded as Lean source data and checked by kernel computation. The source contains no `sorry`, custom axioms, or `native_decide` use.

## Build and axiom audit

The package pins Lean `v4.32.1` and Mathlib tag `v4.32.1`; `lake-manifest.json` fixes Mathlib to commit `520045ab14e26149ee970e2e617ca04b09bde5d6` and records every inherited dependency commit.

```sh
lake exe cache get
lake build Results
lake env lean PrintAxioms.lean
```

`PrintAxioms.lean` audits all seven exported results. The protected-source audit reports only Lean/Mathlib's standard axioms `propext`, `Classical.choice`, and `Quot.sound` for each result, with no `sorryAx` or project-specific assumption. Running the third command reproduces that named theorem list in this package.

## Provenance and limits

`SOURCE-PROVENANCE.json` records the protected commit, formal tree, source Git blob ID, byte size, and SHA-256 digest for every copied Lean file and pin. `lakefile.toml`, `Results.lean`, `PrintAxioms.lean`, this README, and the provenance manifest are public-package metadata or audit entrypoints; they are not proof-source substitutions.

Level 3 full coverage here means the seven declarations listed above, not every statement in the paper. The formalization does not separately cover Theorem 5.1's trace statement, the sharpness example, Section 6, the remarks, or the open determinant inequality. In particular, the unrestricted complex permanent-on-top conjecture remains OPEN. Some proof routes differ from the paper while proving the listed statements. The source review covered all 34 solution modules and reported no mathematical or statement-fidelity finding; that review and a passing source audit are evidence rather than a guarantee beyond the checked Lean declarations. This package contains no private logs, conversations, control files, build cache, or publication claim.
