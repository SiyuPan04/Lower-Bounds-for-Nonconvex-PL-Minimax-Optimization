# Assumptions and Trust Boundary

## Sole Project-Specific Axiom: Paper Lemma 2.2

Paper Lemma 2.2 states a finite-horizon resisting-oracle result without providing
a proof. Under the explicitly declared trust policy, this project accepts the
lemma while confining the trust boundary to a single declaration in one file:

```lean
-- NCPLRevised/AcceptedLemma22.lean
axiom acceptedFiniteHorizonSaddleResistingOracle :
  FiniteHorizonSaddleResistingOracle
```

This is the only project-specific `axiom` permitted in the project. Its logical
role is separated into three layers:

1. `SaddleOracleModel.lean` defines the proposition
   `FiniteHorizonSaddleResistingOracle` but does not assume that it holds.
2. The conditional form of Theorem 3.2 in `DeterministicTransfer.lean` and
   `MainTheorems.lean` lists
   `(hRO : FiniteHorizonSaddleResistingOracle)` explicitly as a theorem
   parameter.
3. Only `AcceptedLemma22.lean` supplies that parameter through the sole axiom
   above, yielding the parameter-free theorem `theorem3_2_concrete_accepted`
   and the paper-style existential-constants theorem `theorem3_2`.

Among the transitive dependencies of the final parameter-free theorem
`NCPLRevised.theorem3_2`, the only project-specific axiom is
`acceptedFiniteHorizonSaddleResistingOracle`. `AxiomAudit.lean` applies
`#print axioms` to both the conditional and accepted interfaces, making this
distinction mechanically observable.

The output may also list foundational principles supplied by Lean and Mathlib,
such as `propext`, `Classical.choice`, and `Quot.sound`. These are not new
mathematical assumptions introduced by this formalization.

## Components Independent of Lemma 2.2

The following components do not depend on the project-specific axiom:

- Lemmas 4.1--4.6 and Proposition 4.1;
- the zero-scale derivative in Lemma 5.1, the genuine Fréchet derivative across
  junction points, and the dimension-independent Lipschitz-gradient
  certificates for both the local and complete assemblies;
- Propositions 5.1--5.3;
- the Euclidean rotation invariance of Lemma 2.1, including preservation of the
  function class and stationarity;
- the explicit hard instance, scaling argument, and query lower bound for
  zero-respecting algorithms;
- `theorem3_1_concrete` and the final existential-constants theorem
  `theorem3_1`.

The assumptions formerly exposed as theorem parameters—`hrotation`, `hhard`,
and the normalized-smoothness premise—have been discharged by explicit
constructions and their corresponding theorems. They no longer occur in the
final Theorem 3.1 or in the final Theorem 3.2 after acceptance of Lemma 2.2.

## `c₀ > 1`

This is not an additional assumption. The project defines

```text
L_C = max 1 embeddedCellSmoothnessConstant,
ell0 = 2 L_C,
mu0 = 1/640,
c0 = 2 ell0 / mu0 = 2560 L_C.
```

Because `L_C >= 1`, the theorem `concreteC0_gt_one` proves `1 < c0` directly.
Both final main theorems also establish `0 < c1` and `0 < c2`.

## Representation Choices (Not Additional Assumptions)

- The lower bound is stated in query-wise operational form: for every query
  index `t` below the threshold, the algorithm's output is not
  `eps`-stationary. This is equivalent to the operational content of the
  paper's lower bound on `T_ε`; the project does not define an aggregate
  `T_ε` wrapper in `inf_algorithm sup_f` form.
- `DeterministicSaddleAlgorithm` is an algorithm family quantified uniformly
  across finite dimensions, while its concrete update maps may depend on the
  dimension. This formalizes the paper's requirement that a single algorithm
  apply to all admissible instances and dimensions.
- Every vector space is represented by explicit finite-dimensional Euclidean
  coordinates. Dimension expansion under rotation and orthogonal frames are
  recorded explicitly in `RotationInvarianceCore.lean` and
  `SaddleOracleModel.lean`.

These are definitional and interface choices, not hidden mathematical
assumptions.
