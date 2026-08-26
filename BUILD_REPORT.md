# Build and Kernel Audit Report

Verification time: 2026-08-26 03:20 (America/Vancouver).

## Pinned Environment

- Lean `4.32.0`, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`
- Lake `5.0.0-src+8c9756b`
- Mathlib commit `11d11a11a667a8fa8ea19d9456fe059f683e308f`
- Platform: `x86_64-w64-windows-gnu`

## Final Reproduction Command

```powershell
.\Build.ps1
```

Final result: exit code `0`; Lake completed `8698` tasks. The project contains
`43` Lean files (the root module, 41 library modules, and the axiom-audit
module), comprising `13123` physical lines in total.

After the build, `Build.ps1` performs two layers of mechanical checks:

1. It rejects every declaration using `sorry`, `admit`, `opaque`, or
   `constant`.
2. It permits exactly one project-specific `axiom`, whose file and name must be
   precisely `acceptedFiniteHorizonSaddleResistingOracle` in
   `NCPLRevised/AcceptedLemma22.lean`.

Both checks passed.

## Transitive Axiom Audit

`NCPLRevised/AxiomAudit.lean` performs 72 `#print axioms` commands and 4
`#check` commands on representative results ranging from the scalar gates to
the final main theorems. The results are as follows:

- `embeddedCellGradient_lipschitz_sq`, `barF_isJointlySmooth`,
  `proposition5_1_concrete`, `theorem3_1_concrete`, and `theorem3_1` depend only
  on the standard foundational principles supplied by Lean and Mathlib:
  `propext`, `Classical.choice`, and `Quot.sound`. They do not depend on any
  project-specific axiom.
- The conditional theorem `theorem3_2_concrete` likewise reports only those
  standard foundational principles; paper Lemma 2.2 appears explicitly as a
  parameter in its signature.
- In addition to the standard foundational principles, the parameter-free final
  results `theorem3_2_concrete_accepted` and `theorem3_2` report only
  `NCPLRevised.acceptedFiniteHorizonSaddleResistingOracle`, corresponding to
  Lemma 2.2, which is explicitly accepted under the stated trust policy.
- The audit output contains neither `sorryAx` nor any other project-specific
  axiom.

## Final Theorem Entry Points

- `NCPLRevised.theorem3_1_concrete`: the fixed explicit-constants version; no
  project-specific axioms.
- `NCPLRevised.theorem3_1`: the paper-style existential-constants statement; no
  project-specific axioms.
- `NCPLRevised.theorem3_2_concrete`: retains only Lemma 2.2 as an explicit
  premise.
- `NCPLRevised.theorem3_2_concrete_accepted`: the parameter-free,
  fixed-constants version.
- `NCPLRevised.theorem3_2`: the paper-style existential-constants statement;
  its sole project-specific axiom dependency is the accepted Lemma 2.2.

## Reproduction Notes

The delivered source tree excludes the `.lake` build cache. On the first build
on another machine, Lake fetches the pinned Mathlib version and its dependencies
according to `lake-manifest.json`. File-level SHA-256 digests are listed in
`SOURCE_HASHES.sha256`.
