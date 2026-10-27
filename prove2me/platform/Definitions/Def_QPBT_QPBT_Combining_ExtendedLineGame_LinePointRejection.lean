-- Generated from QPBT/Combining/ExtendedLineGame/LinePointRejection.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Observables_Defs
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
# Line/point rejection for the extended direct game

This module identifies the axis-line/point, diagonal-line/point, and reversed
point/axis-line branch rejections of the strategy constructed from an
`ExtendedLinesWitness` with the corresponding completed line-point defects.
These are finite postprocessing and state-transport steps in the first
paragraph of the proof of `lem:qld-4-7`; they do not establish a passing-value
bound or construct the supplied witness.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1279-1288`
- Blueprint `lem:qld-4-7`.
- Issues #302, #305, #307, and #309.
-/
@[expose] public section
open scoped BigOperators MatrixOrder ComplexOrder

-- The six-register products use the same instance-search budget as StateTransport.
set_option synthInstance.maxSize 400

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum

noncomputable section

namespace ExtendedLineGame

variable {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {epsilon deltaQ deltaL : ℝ}
variable {setting : _root_.MIPStarRE.QPBT.ProjectiveSetting P epsilon}
variable {points : _root_.MIPStarRE.QPBT.CombinedPointsWitness setting deltaQ}

/-- The unique coordinate of the one-coordinate extended direct low-degree game. -/
def onlyCoordinate : Fin P.extendedDirectLd.k :=
  ⟨0, by change 0 < 1; decide⟩

/-- Read an axis-line answer by completed evaluation at the sampled point.
Failed completed evaluation, including a zero-direction ambiguity, remains
the `none` outcome. -/
def axisGameRead
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd → Option (_root_.MIPStarRE.QPBT.PauliScalar P)
  | .alinePolys coeffs =>
      (_root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directALineDescOf P.extendedDirectLd sample) sample.point
        (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)).map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P)
  | _ => none

/-- Read the unique point coordinate as an optional Pauli scalar. Support for
`lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
def pointGameRead :
    _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd → Option (_root_.MIPStarRE.QPBT.PauliScalar P)
  | .pointVals values => some (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P (values _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate))
  | _ => none

















/-- Read a diagonal-line answer by completed evaluation at the sampled point.
Other answer formats and undefined evaluations return `none`.
Support for `lem:qld-4-7`, paper `14_analysis_of_the_pauli_basis_test.tex:1279-1288`. -/
def diagonalGameRead
    (sample : _root_.MIPStarRE.QPBT.DirectLdSpace P.extendedDirectLd) :
    _root_.MIPStarRE.QPBT.DirectLdAnswer P.extendedDirectLd → Option (_root_.MIPStarRE.QPBT.PauliScalar P)
  | .dlinePolys coeffs =>
      (_root_.MIPStarRE.QPBT.directEvalOpt (_root_.MIPStarRE.QPBT.directDLineDescOf P.extendedDirectLd sample) sample.point
        (coeffs _root_.MIPStarRE.QPBT.ExtendedLineGame.onlyCoordinate)).map (_root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P)
  | _ => none

































end ExtendedLineGame
end

end MIPStarRE.QPBT
