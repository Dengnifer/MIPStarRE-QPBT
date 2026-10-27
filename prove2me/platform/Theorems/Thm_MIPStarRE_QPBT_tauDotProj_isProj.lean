import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LinePolynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_LowDegreePolynomial
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_OpFamily
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersBase
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_ParametersFiniteAnswers
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_QuantumState
import Definitions.Def_LIDT_MIPStarRE_LDT_CommutativityPoints_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_ExpansionHypercubeGraph_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_GlobalVariance_Defs_Core
import Definitions.Def_LIDT_MIPStarRE_LDT_MakingMeasurementsProjective_Defs
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Families
import Definitions.Def_LIDT_MIPStarRE_LDT_Pasting_Defs_Interpolation
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_NormalizedTrace
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Extraction_Defs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib

namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ProjectiveSetting
end MIPStarRE.QPBT.ProjectiveSetting

/-!
# Extraction foundations

This module defines the register identifications used to pull the Pauli
measurements apart. It retains the distinct local spaces of a
heterogeneous strategy, coarse-grains the generalized Pauli projectors by a
dot product, and records the state and error expressions needed by the later
extraction witness.

The binary phases use the existing `phaseSign`; the fixed field basis remains
the basis stored in `P.model` and is not re-quantified here.

## References

The Pauli dot-product projectors formalize blueprint
`def:tau-dot-product-projector`, from
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1426-1429`.
The register and state helpers support blueprint `def:tilde-m-measurement`,
`def:v-swap-unitary`, and `lem:qld-unitary`, from paper lines 1429-1435 and
1666-1713.
-/



open scoped BigOperators Matrix

open MIPStarRE.QPBT

open LIDT.MIPStarRE.Quantum



/-! ## Heterogeneous extraction registers -/











open MIPStarRE.QPBT.ProjectiveSetting

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}

















/-! ## Coarse-grained Pauli projectors -/

theorem MIPStarRE.QPBT.tauDotProj_isProj {P : _root_.MIPStarRE.QPBT.AdmissibleParams} (W : _root_.MIPStarRE.QPBT.PauliKind)
    (u : _root_.MIPStarRE.QPBT.PauliRegister P) (a : _root_.MIPStarRE.QPBT.PauliScalar P) :
    _root_.LIDT.MIPStarRE.Quantum.IsProj (_root_.MIPStarRE.QPBT.tauDotProj W u a) := by sorry
