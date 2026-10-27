-- Generated from QPBT/Combining/ExtendedLineGame/SameLineRejection.lean by skeleton subtraction.
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_AxisParallelLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_DiagonalLine
import Definitions.Def_LIDT_MIPStarRE_LDT_Basic_Distribution
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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_LowDegreeCode
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/-!
# Same-line branch rejection for the extended direct game

The axis-axis and diagonal-diagonal verifier branches compare the complete
typed coefficient answers returned by the two line measurements. This module
identifies each branch rejection exactly with the corresponding coefficient-
answer consistency defect, averaged over the marginal law of the supplied
line. These are exact transport identities, not numerical passing bounds.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1020-1034`
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issue Dengnifer/MIPStarRE-QPBT-bak#317.
-/

@[expose] public section

open scoped BigOperators MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : Real}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

/-- The consistency defect of the two axis-line coefficient answers on the
constructed two-player state. The question law is the axis-line marginal of
the supplied direct line-point distribution. -/
def axisCoefficientAnswerDefect
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) : Real :=
  _root_.MIPStarRE.QPBT.consistencyDefect
    ((_root_.MIPStarRE.QPBT.directALinePointDist P.extendedDirectLd).map Prod.fst)
    (fun line answer => _root_.MIPStarRE.QPBT.heteroKron
      (((lines.Qline .alice line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer P)).effect answer) 1)
    (fun line answer => _root_.MIPStarRE.QPBT.heteroKron 1
      (((lines.Qline .bob line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.axisAnswer P)).effect answer))
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)

/-- The consistency defect of the two diagonal-line coefficient answers on
the constructed two-player state. The question law is the diagonal-line
marginal of the supplied direct line-point distribution. -/
def diagonalCoefficientAnswerDefect
    (lines : _root_.MIPStarRE.QPBT.ExtendedLinesWitness setting points deltaL) : Real :=
  _root_.MIPStarRE.QPBT.consistencyDefect
    ((_root_.MIPStarRE.QPBT.directDLinePointDist P.extendedDirectLd).map Prod.fst)
    (fun line answer => _root_.MIPStarRE.QPBT.heteroKron
      (((lines.Qline .alice line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalAnswer P)).effect answer) 1)
    (fun line answer => _root_.MIPStarRE.QPBT.heteroKron 1
      (((lines.Qline .bob line).postprocess (_root_.MIPStarRE.QPBT.ExtendedLineGame.diagonalAnswer P)).effect answer))
    (_root_.MIPStarRE.QPBT.ExtendedLineGame.pairState setting)













end ExtendedLineGame

end

end MIPStarRE.QPBT
