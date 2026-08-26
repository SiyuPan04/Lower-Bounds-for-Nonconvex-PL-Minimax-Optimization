# Lower Bounds for Nonconvex–PŁ Minimax Optimization

[![Formal Verification](https://github.com/SiyuPan04/Lower-Bounds-for-Nonconvex-PL-Minimax-Optimization/actions/workflows/verify.yml/badge.svg?branch=main)](https://github.com/SiyuPan04/Lower-Bounds-for-Nonconvex-PL-Minimax-Optimization/actions/workflows/verify.yml)

This repository contains a Lean 4 and Mathlib formal verification of the revised manuscript *Lower Bounds for Nonconvex–PŁ Minimax Optimization*. The formal development follows `main_revised.tex`; the accompanying `ncpl_chain_schematic.pdf` and `ref.bib` were used to cross-check the construction and references. Their source fingerprints are recorded below, while the manuscript files themselves are not distributed in this repository.

## Verified results

The development covers the complete proof chain from scalar gate functions, the weighted dual chain, the scaled perspective block, the Carmon outer activation, and the embedded cell through the assembly of the full `barF` construction, parameter scaling, and the query lower bound. Lemma 4.4, Lemmas 4.5--4.6, Lemma 5.1, and Propositions 5.1--5.3 are represented by concrete theorems and are connected to the final main theorems.

- `NCPLRevised.theorem3_1` formalizes the existential-constant statement of Theorem 3.1. It has no project-defined axioms and requires no unproved smoothness, rotation, or hard-instance hypotheses.
- `NCPLRevised.theorem3_2_concrete` exposes the sole external input to Theorem 3.2 as the parameter `hRO : FiniteHorizonSaddleResistingOracle`.
- Under the stated trust policy, `AcceptedLemma22.lean` records the manuscript's unproved Lemma 2.2 as the single project-defined axiom `acceptedFiniteHorizonSaddleResistingOracle`. The parameter-free endpoint `NCPLRevised.theorem3_2` depends, beyond Lean and Mathlib's standard logical foundations, only on that explicitly accepted axiom.

The trust boundary is therefore precise: Theorem 3.1 has no project-defined axioms; Theorem 3.2's parameter-free endpoint depends only on explicitly accepted manuscript Lemma 2.2. The development does not claim to prove Lemma 2.2 itself. See `ASSUMPTIONS.md` for the complete trust statement.

## Correspondence with the manuscript's complexity notation

The final theorems use a query-wise operational form. For every admissible parameter tuple and every corresponding algorithm, they construct an admissible instance and prove that no natural-number query time below

```text
c₂ (ell / mu) ell Delta / eps²
```

can reach `eps`-stationarity. This is the pointwise query statement required by the manuscript's lower bound for `T_ε`, and it can be used equivalently for that result. The development does not introduce a separate display-level `inf_algorithm sup_f` wrapper, or an equivalent aggregate wrapper, for `T_ε`; the omitted component is notation rather than a proof obligation.

Algorithms are represented as dimension-polymorphic deterministic families that operate uniformly over finite-dimensional instances, while their update rules may still depend on the current dimension. This matches the manuscript's quantifier structure in which an algorithm operates over all admissible dimensions.

## Source layout

- `Gates.lean`, `Weights.lean`, `DualChain.lean`, and `DualChainDerivative.lean`: Lemmas 4.1--4.3 and Proposition 4.1.
- `ScaledPerspectiveBlock.lean`: Lemma 4.4, including the `eta = 0` branch, the actual derivative, the maximizer, and the PL conclusion.
- `CarmonGates.lean` and `CarmonActivation.lean`: the Carmon gate functions and the flat-splicing, derivative-bound, and lifted-target certificates of Lemmas 4.5--4.6.
- `QuadraticPerspectiveSmoothness.lean`, `QuadraticPerspectiveVector.lean`, `ScaleClipKernel.lean`, `ScaleClipPair.lean`, `PerspectiveGradientLipschitz.lean`, `TerminalPerspectiveSmoothness.lean`, `ResidualGradientSmoothness.lean`, and `ResidualGradientDerivative.lean`: the zero-scale Fréchet derivative and dimension-independent Lipschitz estimates required by Lemma 5.1.
- `EmbeddedCellSmoothness.lean`, `EmbeddedCellJointDerivative.lean`, and `EmbeddedCellLipschitz.lean`: the actual embedded cell, its complete gradient, and locally uniform smoothness.
- `HardInstanceAssembly.lean`, `ConcreteHardInstance.lean`, `ConcreteSaddleZeroChain.lean`, and `AssembledSmoothness.lean`: the complete `barF` construction, Propositions 5.1--5.3, the actual joint gradient, and dimension-independent path assembly.
- `SaddleOracleModel.lean`, `OrderedOracleBridge.lean`, `RotationInvarianceCore.lean`, and `DeterministicTransfer.lean`: the algorithm model, coordinate ordering, the rotational invariance of Lemma 2.1, and the deterministic transfer derived from Lemma 2.2.
- `ConcreteZeroRespectingLowerBound.lean`, `CertificateScaling.lean`, and `MainTheorems.lean`: parameter scaling, the zero-respecting lower bound, and Theorems 3.1--3.2.
- `AcceptedLemma22.lean`: the single explicitly accepted project-defined axiom and the parameter-free endpoint for Theorem 3.2.
- `AxiomAudit.lean`: the `#print axioms` audit entry point for the key declarations.

## Build and verification

The project is pinned to:

- Lean `v4.32.0`
- Mathlib commit `11d11a11a667a8fa8ea19d9456fe059f683e308f`

On Windows PowerShell, run:

```powershell
.\Build.ps1
```

To reproduce the verification from a fresh clone:

```bash
git clone https://github.com/SiyuPan04/Lower-Bounds-for-Nonconvex-PL-Minimax-Optimization.git
cd Lower-Bounds-for-Nonconvex-PL-Minimax-Optimization
lake update
lake exe cache get
lake build
lake env lean NCPLRevised/AxiomAudit.lean
```

The build and audit commands may also be run separately in PowerShell:

```powershell
lake build
lake env lean NCPLRevised\AxiomAudit.lean
```

`Build.ps1` rejects `sorry`, `admit`, `opaque`, and every unapproved project-defined `axiom`. Its sole exception is the precisely named Lemma 2.2 axiom in `AcceptedLemma22.lean`.

## Source hashes

```text
main_revised.tex          8CD6E0C4FEAFC4DEEBA9016682274249EED3A3F4F5C03243233AE2C20189EC64
ncpl_chain_schematic.pdf  7681C9D1CB81E61F6390087B17D6C5CC90E53ED9ECFE0BE29EF2692ED01D2247
ref.bib                   0660E14C8F7BC862C9B15A49E1235CADD1E5B98AE5930B38E43A053E02C4FB6
```
