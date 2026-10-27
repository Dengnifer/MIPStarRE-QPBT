-- Generated from QPBT/ExplicitConstants.lean by skeleton subtraction.
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
import Mathlib

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Explicit constants for the Pauli basis test

This module records the closed numerical witnesses obtained by following the
current quantitative proof of Pauli-basis-test soundness.  They are Lean-only
quantitative auxiliaries for the source theorem `thm:pauli`; no hypothesis or
conclusion of that theorem is changed.

## References

The proof follows `lem:qld-unitary` and the final isometry argument in
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1666-1876`.
-/

@[expose] public section

namespace MIPStarRE.QPBT

noncomputable section

/-- The fixed point-observable commutator coefficient. -/
def pauliBaselineCommutatorConstant : ℝ :=
  1024 * (172 + Real.sqrt 344)

/-- The fixed two-sided twisted-commutator coefficient. -/
def pauliBaselineTwistedConstant : ℝ :=
  2 * (2 * _root_.MIPStarRE.QPBT.pauliBaselineCommutatorConstant + 4886363136 + 4)

/-- The coefficient of the combined-point error `ε^(1/8)`. -/
def pauliBaselinePointConstant : ℝ :=
  10560 * (344 + 3 * _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant) +
    24 * _root_.MIPStarRE.QPBT.pauliBaselineTwistedConstant + 11008















/-- The one-coordinate direct low-degree coefficient used by the current proof. -/
def pauliBaselineLowDegreeConstant : ℝ := 2500000000

/-- The one-coordinate direct low-degree power used by the current proof. -/
def pauliBaselineLowDegreePower : ℝ := 1 / 80000









/-- The maximum coefficient needed by the current extraction construction. -/
def pauliBaselineExtractionConstant : ℝ := 2800









end

end MIPStarRE.QPBT
