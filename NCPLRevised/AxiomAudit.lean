/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised

/-!
Compile this file to display the logical dependencies of the main checked
certificates.  `propext`, `Classical.choice`, and `Quot.sound` are standard
Lean/Mathlib foundations.  No declaration below may use `sorryAx` or a
project-defined axiom, except that the two accepted forms of Theorem 3.2
must report exactly `acceptedFiniteHorizonSaddleResistingOracle` in addition
to the standard foundations.
-/

/-! ## Scalar gates, weights, and the dual relay -/

#print axioms NCPLRevised.lemma4_1
#print axioms NCPLRevised.hasDerivAt_q
#print axioms NCPLRevised.hasDerivAt_p
#print axioms NCPLRevised.hasDerivAt_negPartSq
#print axioms NCPLRevised.lemma4_2_order
#print axioms NCPLRevised.lemma4_2_sums
#print axioms NCPLRevised.proposition4_1
#print axioms NCPLRevised.lemma4_3
#print axioms NCPLRevised.hasDerivAt_dualChain_update
#print axioms NCPLRevised.hasDerivAt_coupledDual_update
#print axioms NCPLRevised.hasFDerivAt_dualChain
#print axioms NCPLRevised.hasFDerivAt_coupledDual

/-! ## Carmon chain and the perspective cell -/

#print axioms NCPLRevised.deriv_carmonPsi
#print axioms NCPLRevised.hasDerivAt_carmonPhi
#print axioms NCPLRevised.hasDerivAt_carmonTheta
#print axioms NCPLRevised.hasDerivAt_outerRho
#print axioms NCPLRevised.outer_scale_and_lifted_target_certificate
#print axioms NCPLRevised.hasEVecFDerivAt_carmonF_gradient
#print axioms NCPLRevised.carmonGradient_is_zeroChain
#print axioms NCPLRevised.one_le_vecSq_carmonGradient_of_terminal_zero
#print axioms NCPLRevised.carmonTermCap_lt_twelve
#print axioms NCPLRevised.carmon_initial_gap_twelve
#print axioms NCPLRevised.carmon_terminal_gap_certificate
#print axioms NCPLRevised.lemma4_4
#print axioms NCPLRevised.hasCellFDerivAt_embeddedCell_gradient

/-! ## Concrete hard instance and zero-chain certificates -/

#print axioms NCPLRevised.barF_envelope
#print axioms NCPLRevised.barF_dual_PL
#print axioms NCPLRevised.proposition5_2_concrete
#print axioms NCPLRevised.proposition5_3_concrete
#print axioms NCPLRevised.concrete_value_and_dual_certificate
#print axioms NCPLRevised.concreteScaledBarF_dual_PL
#print axioms NCPLRevised.concreteScaledOrderedSaddleField_isZeroChain
#print axioms NCPLRevised.concrete_zero_respecting_lower_bound

/-! ## Uniform smoothness and actual-gradient assembly -/

#print axioms NCPLRevised.qPerspectiveEtaLift_lipschitz
#print axioms NCPLRevised.qpPerspectiveEtaLift_lipschitz
#print axioms NCPLRevised.terminalPerspectiveGradient_lipschitz_sq
#print axioms NCPLRevised.embeddedResidualGradient_lipschitz_sq
#print axioms NCPLRevised.qpPerspectiveFDeriv_dual_apply
#print axioms NCPLRevised.hasFDerivAt_embeddedResidualAtScale_y
#print axioms NCPLRevised.embeddedStableCellGradient_lipschitz_sq
#print axioms NCPLRevised.embeddedStableCellGradient_eq_actual
#print axioms NCPLRevised.embeddedCellGradient_lipschitz_sq
#print axioms NCPLRevised.assembledGradient_isJointlySmooth
#print axioms NCPLRevised.hasFDerivAt_barF
#print axioms NCPLRevised.barF_representsGradient
#print axioms NCPLRevised.barF_isJointlySmooth
#print axioms NCPLRevised.proposition5_1_concrete

/-! ## Scaling arithmetic and query obstruction -/

#print axioms NCPLRevised.paper_chain_length_lower
#print axioms NCPLRevised.paper_parameter_certificate
#print axioms NCPLRevised.revised_c0_gt_one
#print axioms NCPLRevised.sequential_query_discovery
#print axioms NCPLRevised.conditional_zero_respecting_lower_bound

/-! ## Rotation and the deterministic oracle model -/

#print axioms NCPLRevised.euclideanSq_orthogonalEmbed
#print axioms NCPLRevised.rotatedObjective_representsGradient
#print axioms NCPLRevised.EuclideanNCPLClass.rotate
#print axioms NCPLRevised.rotatedEnvelope_hasFDerivAt
#print axioms NCPLRevised.rotated_stationarity_iff
#print axioms NCPLRevised.deterministic_failure_before_of_resistingOracle
#print axioms NCPLRevised.SmoothSaddle.rotate_inClass
#print axioms NCPLRevised.SmoothSaddle.rotate_stationary_iff
#print axioms NCPLRevised.zeroRespecting_orderedAlgorithmQuery
#print axioms NCPLRevised.deterministic_failure_of_finiteHorizonResistingOracle

/-! ## Main theorems -/

#print axioms NCPLRevised.concreteScaledSmoothSaddle_inClass_of_base
#print axioms NCPLRevised.zeroRespecting_main_lower_bound_of_base
#print axioms NCPLRevised.deterministic_main_lower_bound_of_base
#print axioms NCPLRevised.theorem3_1_concrete
#print axioms NCPLRevised.theorem3_1
#print axioms NCPLRevised.theorem3_2_concrete

-- These are the only declarations expected to report the accepted
-- manuscript Lemma 2.2 as a custom axiom.
#print axioms NCPLRevised.acceptedFiniteHorizonSaddleResistingOracle
#print axioms NCPLRevised.theorem3_2_deterministic_accepted_of_normalizedSmoothness
#print axioms NCPLRevised.theorem3_2_concrete_accepted
#print axioms NCPLRevised.theorem3_2

-- The signatures make both forms of the trust boundary mechanically visible:
-- an explicit hypothesis in the conditional theorem and the single accepted
-- declaration in the paper-facing theorem.
#check NCPLRevised.deterministic_failure_before_of_resistingOracle
#check NCPLRevised.theorem3_2_concrete
#check NCPLRevised.acceptedFiniteHorizonSaddleResistingOracle
#check NCPLRevised.theorem3_2_concrete_accepted
