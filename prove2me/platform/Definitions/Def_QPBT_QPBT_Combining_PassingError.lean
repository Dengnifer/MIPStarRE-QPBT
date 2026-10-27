-- Generated from QPBT/Combining/PassingError.lean by skeleton subtraction.
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

namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-! # Capped scalar envelope for direct-game error bounds

This module gives a concrete polynomial envelope for a scalar expression assembled from
seven prospective rejection bounds in the directly indexed extended-line game. It is a
formalization-only arithmetic auxiliary: it does not prove that any game branch satisfies
one of these bounds, nor does it prove a passing-value theorem.

The cap by one records the independent fact that a rejection probability is at most one.
It is essential for the polynomial-error contract: the uncapped function
`2 * x + Real.sqrt x + y` cannot be bounded by one positive power of `x` both near zero
and at infinity.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Parent issue Dengnifer/MIPStarRE-QPBT-bak#119 and arithmetic issue
  Dengnifer/MIPStarRE-QPBT-bak#326
-/

@[expose] public section

namespace MIPStarRE.QPBT

/-- The concrete two-variable polynomial envelope for the capped scalar bound. -/
noncomputable def directPassingErrorEnvelope (x y : ℝ) : ℝ :=
  3 * (Real.sqrt x + y)











end MIPStarRE.QPBT
