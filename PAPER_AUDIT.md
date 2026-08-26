# Revised Manuscript and Formalization Audit

Audited source: `main_revised.tex` (4,299 lines; SHA-256
`8CD6E0C4FEAFC4DEEBA9016682274249EED3A3F4F5C03243233AE2C20189EC64`).

Static TeX validation found 82 active labels, all unique, and 137 active
`ref` / `eqref` / `cref` references, all resolved. The chain schematic agrees
with the ordering in the main text:
`x_(i-1) -> y_1^(i) -> ... -> y_N^(i) -> x_i`.

## Manuscript Review

The revised manuscript resolves the principal editorial issues in the previous
version:

- There is no active occurrence of `Lemma ??`.
- The inactive-region branch of the perspective extension is included in the
  definition, and Lemma 5.1 has a formal statement and proof framework.
- The block following Proposition 5.2 correctly refers to `y^(M)`.
- The appendix defines `theta` and uses it to express `rho`.
- The citation to Fact 4.1, the stray text, and the misspelling `Propostion` have
  been corrected.

Lemma 2.2 in the paper still has a statement but no proof. Under the stated
trust policy, the formalization isolates it as the sole custom axiom in
`AcceptedLemma22.lean`; it is not misreported as machine proved.

The identities `ell0 = 2 L_C` and `mu0 = 1/640`, together with `L_C >= 1` from
the main text, are sufficient to derive `c0 = 2560 L_C > 1`. The declaration
`concreteC0_gt_one` proves this fact, so `c0 > 1` is not a gap and requires no
additional assumption.

## Closed Proof Obligations

Every item below, identified as an outstanding obligation in an earlier audit,
is now part of the concrete proof chain:

1. Lemma 4.4: weighted-coordinate normalization, the zero and nonzero
   perspective branches, the actual derivative, maximum value, and PŁ
   certificate. The file is `ScaledPerspectiveBlock.lean`, with entry point
   `NCPLRevised.lemma4_4`.
2. Lemmas 4.5--4.6: the flat splice for `rho`, its first and second derivatives
   and global bounds, and the lifted target's three-piece formula, positivity,
   and `10 rho^2` upper bound. The aggregate entry point is
   `NCPLRevised.outer_scale_and_lifted_target_certificate` in
   `CarmonActivation.lean`.
3. Lemma 5.1: Fréchet differentiability of the quadratic perspective at zero
   scale, terminal and residual gradients, the actual cell derivative across
   splice interfaces, a dimension-free local Lipschitz constant, and the
   complete assembly along `M` cells.
4. Proposition 5.1: the actual joint gradient and joint smoothness of the
   concrete `barF`, the inner maximum, and dual PŁ. The entry point is
   `NCPLRevised.proposition5_1_concrete`.
5. Proposition 5.2: the saddle zero-chain property of the complete actual
   gradient. The entry point is `NCPLRevised.proposition5_2_concrete`.
6. Proposition 5.3: the concrete envelope, actual value gradient, terminal
   obstruction, identification of the last coordinate, and the `12M` gap. The
   entry point is `NCPLRevised.proposition5_3_concrete`.
7. Parameter rounding and scaling, the rotation invariance of Lemma 2.1, the
   algorithm interface, and the quantifier assembly for the main theorems.

All of the above, including the final `NCPLRevised.theorem3_1`, are independent
of project-specific axioms. Parameters such as `hrotation`, `hhard`, and `hbase`,
which served as intermediate interfaces, have been instantiated by proved
theorems in the final concrete specialization.

## Main Theorems and the Sole Trust Boundary

- Theorem 3.1: `NCPLRevised.theorem3_1` is the existential-constants statement
  with no additional premise. The conditions `c0 > 1`, `c1 > 0`, and `c2 > 0`,
  together with every analytical certificate for the concrete hard instance,
  are proved by the formalization.
- Theorem 3.2: `NCPLRevised.theorem3_2_concrete` retains Lemma 2.2 as an explicit
  parameter `hRO` for auditability. The final parameter-free declaration
  `NCPLRevised.theorem3_2` in `AcceptedLemma22.lean` supplies that parameter with
  the sole accepted axiom. The final theorem has no other custom axiom or
  undischarged mathematical premise.

Thus, the project verifies the entire analytical chain in the paper and the
deterministic main theorem after accepting Lemma 2.2. It does not claim to supply
the proof of Lemma 2.2 that is absent from the paper.

## Representational Differences in `T_ε` and the Algorithmic Model

The final result uses a query-wise operational form: for every algorithm and
every natural-number query time `t` satisfying
`t < c2 (ell/mu) ell Delta / eps^2`, the query point on the constructed instance
is not `eps`-stationary. This is equivalent to the query-wise content of the
paper's lower bound for `T_ε` and directly yields the same complexity
conclusion.

The project does not separately define an aggregate wrapper corresponding to
the paper's notation `T_ε := inf_algorithm sup_f ...`. This is a difference in
presentation, not an unproved mathematical step. Correspondingly,
`DeterministicSaddleAlgorithm` is encoded as a dimension-polymorphic family: a
single algorithm object covers all finite-dimensional admissible instances, and
its update/query rule may depend on the current dimension. This preserves the
paper's intended quantifier structure.

## Audit Criteria

`AxiomAudit.lean` invokes `#print axioms` on the key declarations at each layer.
The expected results are:

- Lemmas 4.4--4.6, Lemma 5.1, Propositions 5.1--5.3, and Theorem 3.1 contain no
  project-specific axiom.
- The accepted form of Theorem 3.2 adds only
  `acceptedFiniteHorizonSaddleResistingOracle`.
- No `sorryAx` occurs. A source scan also rejects `sorry`, `admit`, `opaque`, and
  any other `axiom` declaration.

Under these explicit criteria, the perspective-smoothness and hard-instance
assembly risks identified by the earlier audit are closed. The only remaining
trust boundary is Lemma 2.2, which the project explicitly accepts as given.
