# Formalization Coverage Matrix

In the table below, “Proved” means that the corresponding declaration has a
complete proof term and uses no `sorry`, `admit`, `opaque`, or project-specific
axiom. “Proved; uses Lemma 2.2” is reserved for the final deterministic transfer:
it has no undischarged premise other than the explicitly accepted Lemma 2.2 from
the paper.

| Paper item | Primary formalization module / declaration | Status and machine-checked content |
|---|---|---|
| Lemma 4.1 | `Gates`; `lemma4_1` | Proved: `q`, `p`, the squared negative part, actual one-dimensional derivatives, ranges, Lipschitz properties, and the key inequality. |
| Lemma 4.2 | `Weights`; `lemma4_2_order`, `lemma4_2_sums` | Proved: the weight recurrence, monotone ordering, and two strict sum bounds. |
| Proposition 4.1 | `DualChain`, `DualChainDerivative`; `proposition4_1` | Proved: equation (7), coordinate derivatives and the full Fréchet derivative, the nonpositive coordinate sum, and the strengthened PŁ inequality. |
| Lemma 4.3 | `DualChain`, `DualChainDerivative`; `lemma4_3` | Proved: the maximum, weighted PŁ inequality, and identification of `coupledGradient` with the actual derivative. |
| Carmon gate functions / properties from Fact 4.1 required by the main theorem | `CarmonGates`, `CarmonChain`, `CarmonDifferentiability`, `CarmonCertificate` | Proved: all gate values and derivative bounds used in the argument, the actual outer Fréchet gradient, the zero-chain property, the terminal obstruction, the Gaussian integral, and the `12M` gap. |
| Lemma 4.4 | `ScaledPerspectiveBlock`; `lemma4_4` | Proved: diagonal-weight normalization, the `eta != 0` and `eta = 0` branches, the actual derivative, the maximizer, the maximum value, and the PŁ inequality. No project-specific axiom. |
| Lemmas 4.5--4.6 | `CarmonActivation`; `outer_scale_and_lifted_target_certificate` | Proved: the flat semi-exponential splice, actual first and second derivatives of `rho` with global bounds, the flat region, the three-piece formula, positivity of the target, and `0 <= H <= 10 rho^2`. No project-specific axiom. |
| Lemma 5.1: quadratic-perspective kernel | `QuadraticPerspectiveSmoothness`, `QuadraticPerspectiveVector`, `ScaleClipKernel`, `ScaleClipPair`, `PerspectiveGradientLipschitz` | Proved: the explicit derivative at nonzero scale, the actual Fréchet derivative on the entire zero-scale hyperplane, and a global Lipschitz gradient estimate across zero scale. |
| Lemma 5.1: terminal / residual / embedded cell | `TerminalPerspectiveSmoothness`, `ResidualGradientSmoothness`, `ResidualGradientDerivative`, `EmbeddedCellJointDerivative`, `EmbeddedCellLipschitz` | Proved: the terminal and residual gradient components, the actual dual derivative, splice interfaces, the actual full-cell gradient, and the dimension-free constant `embeddedCellSmoothnessConstant`. |
| Lemma 5.1: complete assembly of `M` cells | `AssembledSmoothness`; `barF_isJointlySmooth`, `hasFDerivAt_barF` | Proved: path overlap of at most two, the actual joint gradient of the complete `barF`, and the dimension-free smoothness constant `concreteEll0 = 2 concreteLC`. No project-specific axiom. |
| Proposition 5.1 | `ConcreteHardInstance`, `AssembledSmoothness`; `proposition5_1_concrete` | Proved: the actual gradient and joint smoothness of the concrete `barF`, attainment of the inner maximum at `barPhi`, and the `mu0/N` dual-PŁ inequality. No project-specific axiom. |
| Proposition 5.2 | `ConcreteSaddleZeroChain`; `proposition5_2_concrete` | Proved: the complete actual gradient is a first-order saddle zero-chain under the paper's interleaved coordinate ordering. No project-specific axiom. |
| Proposition 5.3 | `ConcreteHardInstance`; `proposition5_3_concrete`, `concrete_value_and_dual_certificate` | Proved: the actual gradient of `barPhi`, the terminal gradient lower bound, identification of the last coordinate, and the exact `12M` initial gap. No project-specific axiom. |
| Scaled concrete instance | `ScalingCalculus`, `ScaledZeroChain`, `ConcreteZeroRespectingLowerBound`, `MainTheorems` | Proved: joint smoothness, dual PŁ, value-gap and stationarity scaling, rounding, and the query threshold. |
| Lemma 2.1 | `RotationInvarianceCore`, `SaddleOracleModel` | Proved: the actual gradient under orthogonal embedding, smoothness, dual PŁ, envelope/value gap, function-class membership, and equivalence of stationarity. No project-specific axiom. |
| Theorem 3.1 | `MainTheorems`; `theorem3_1_concrete`, `theorem3_1` | Proved: there exist `c0 > 1`, `c1 > 0`, and `c2 > 0`, and every zero-respecting algorithm fails at every query below the threshold. There is no project-specific axiom or undischarged theorem parameter. |
| Lemma 2.2 | `SaddleOracleModel`, `AcceptedLemma22`; `acceptedFiniteHorizonSaddleResistingOracle` | Explicitly accepted under the stated trust policy, not proved by the proof assistant; this is the project's only custom axiom. |
| Theorem 3.2 (conditional form) | `DeterministicTransfer`, `MainTheorems`; `theorem3_2_concrete` | The implication is proved: its only explicit mathematical premise is `hRO : FiniteHorizonSaddleResistingOracle`; all other analytical and assembly premises have been discharged. |
| Theorem 3.2 (final accepted form) | `AcceptedLemma22`; `theorem3_2_concrete_accepted`, `theorem3_2` | Proved; parameter-free. The only project-specific axiom in its transitive dependencies is the accepted Lemma 2.2. |
| Paper's `T_ε` complexity statement | Query-wise conclusion in `MainTheorems` | The operational content is proved: every natural-number query below the real-valued threshold fails, which equivalently yields the paper's `T_ε` lower bound. No separate `inf_algorithm sup_f` aggregate wrapper is defined. |

## Quantifier Structure of the Final Interfaces

Both `theorem3_1` and `theorem3_2` explicitly provide constants `c0`, `c1`, and
`c2` together with their positivity properties, and then quantify over positive
`ell`, `mu`, `Delta`, and `eps`, the condition-number regime, and the accuracy
regime. For each parameter tuple, Theorem 3.1 constructs a concrete
`SmoothSaddle` that defeats every zero-respecting algorithm. For every arbitrary
deterministic algorithm, Theorem 3.2 constructs an orthogonally embedded
admissible instance and rules out `eps`-stationarity before the same complexity
threshold.

The infimum-supremum notation for `T_ε` is not repackaged as a separate
definition, but the quantifier order above and the query-wise conclusion are
exactly the proof content of that complexity lower bound.
