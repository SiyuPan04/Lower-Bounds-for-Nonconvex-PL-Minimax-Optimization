/-
Copyright (c) 2026 NCPL formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: NCPL formalization contributors
-/

import NCPLRevised.BlockLayout
import NCPLRevised.CarmonActivation
import NCPLRevised.CarmonCertificate
import NCPLRevised.CarmonChain
import NCPLRevised.CarmonDifferentiability
import NCPLRevised.CarmonGates
import NCPLRevised.CertificateScaling
import NCPLRevised.ConcreteHardInstance
import NCPLRevised.ConcreteSaddleZeroChain
import NCPLRevised.ConcreteZeroRespectingLowerBound
import NCPLRevised.ConditionalLowerBound
import NCPLRevised.DeterministicTransfer
import NCPLRevised.DualChain
import NCPLRevised.DualChainDerivative
import NCPLRevised.EmbeddedCellJointDerivative
import NCPLRevised.EmbeddedCellLipschitz
import NCPLRevised.EmbeddedCellSmoothness
import NCPLRevised.Gates
import NCPLRevised.HardInstanceAssembly
import NCPLRevised.MainTheorems
import NCPLRevised.OrderedOracleBridge
import NCPLRevised.OuterLinearAlgebra
import NCPLRevised.PerspectiveGradientLipschitz
import NCPLRevised.QuadraticPerspectiveSmoothness
import NCPLRevised.QuadraticPerspectiveVector
import NCPLRevised.ResidualGradientDerivative
import NCPLRevised.ResidualGradientSmoothness
import NCPLRevised.ResistingOracleAssumption
import NCPLRevised.RevisedConstants
import NCPLRevised.RotationInvarianceCore
import NCPLRevised.SaddleOracleModel
import NCPLRevised.ScaleClipKernel
import NCPLRevised.ScaleClipPair
import NCPLRevised.ScaledPerspectiveBlock
import NCPLRevised.ScaledZeroChain
import NCPLRevised.ScalingCalculus
import NCPLRevised.TerminalPerspectiveSmoothness
import NCPLRevised.Weights
import NCPLRevised.ZeroChain
import NCPLRevised.AssembledSmoothness
import NCPLRevised.AcceptedLemma22

/-!
Root module for the formalization of *Lower Bounds for Nonconvex-PL
Minimax Optimization* (`main_revised.tex`, revised 2026-08-25).

`AcceptedLemma22` is deliberately imported last: it is the unique custom
trust boundary and all preceding analytic results, including Theorem 3.1,
are independent of it.  `AxiomAudit` is the sole non-imported project file
because it is a standalone audit entry point that imports this root module.
-/
