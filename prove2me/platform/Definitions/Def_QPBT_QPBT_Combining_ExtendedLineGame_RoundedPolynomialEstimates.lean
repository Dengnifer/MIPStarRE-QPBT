-- Generated from QPBT/Combining/ExtendedLineGame/RoundedPolynomialEstimates.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_Pauli
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_ExtendedLineGame_PointPointRejection
import Definitions.Def_QPBT_QPBT_Combining_Points
import Definitions.Def_QPBT_QPBT_Combining_Witnesses
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Observables_Defs
import Definitions.Def_QPBT_QPBT_Observables_ExpandedDefs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Definitions.Def_QPBT_QPBT_Test_PauliBasisTest
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.ExtendedLineGame
end MIPStarRE.QPBT.ExtendedLineGame

/-!
# Rounded extended-polynomial ordered estimates

Direct soundness retains all three consistency conclusions through compression.
Its same-space projective rounding supplies the point comparison used in both
ordered estimates, with the actual point and line errors retained.

## References

`eq:qld-g-42` and `eq:qld-g-43`, paper
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1278-1300`.
The directly indexed completed-answer restriction is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex` and
`docs/paper-gaps/qpbt_combined-lines-error-term.tex`.
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus

noncomputable section

namespace ExtendedLineGame

/-- Evaluation of the single extended polynomial returned by direct soundness,
at the point with blocks `(x,z,alpha,beta)`, in the canonical Pauli scalar field.
The singleton tuple carrier is exactly the `k = 1` soundness outcome carrier. -/
def extendedPolynomialRead (P : _root_.MIPStarRE.QPBT.AdmissibleParams) (x : _root_.MIPStarRE.QPBT.ExtendedPointQuestion P)
    (g : _root_.MIPStarRE.QPBT.DirectPolyTuple P.extendedDirectLd) : _root_.MIPStarRE.QPBT.PauliScalar P :=
  _root_.MIPStarRE.QPBT.extendedDirectScalarEquiv P
    (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt ((_root_.MIPStarRE.QPBT.ExtendedLineGame.directPointExtendedQuestionEquiv P).symm x) g (0 : Fin 1))



/-- The full polynomial-outcome squared-norm sum in `eq:qld-g-42/43`.
The order parameter selects either `M_X M_Z` or `M_Z M_X`.
The polynomial effect acts on `p1` and both point effects on `p2`. -/
def extendedPolynomialOrderedError {P : _root_.MIPStarRE.QPBT.AdmissibleParams} {ε : ℝ}
    (S : _root_.MIPStarRE.QPBT.ProjectiveSetting P ε) (p1 p2 : _root_.MIPStarRE.QPBT.Placement)
    (R : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple P.extendedDirectLd (S.ExpandedLocalSpace p1.side))
    (reverse : Bool) : ℝ :=
  _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ExtendedPointQuestion P)) (fun x =>
    ∑ g, ‖_root_.MIPStarRE.QPBT.applyOperatorToState (S.place p1 (R.effect g) *
      (1 - S.place p2
        (∑ ab ∈ Finset.univ.filter (fun ab : _root_.MIPStarRE.QPBT.PauliScalar P × _root_.MIPStarRE.QPBT.PauliScalar P =>
            x.2.1 * ab.1 + x.2.2 * ab.2 = _root_.MIPStarRE.QPBT.ExtendedLineGame.extendedPolynomialRead P x g),
          if reverse then
            (S.pointMeasExp p2.side .Z x.1.2).effect ab.2 *
              (S.pointMeasExp p2.side .X x.1.1).effect ab.1
          else
            (S.pointMeasExp p2.side .X x.1.1).effect ab.1 *
              (S.pointMeasExp p2.side .Z x.1.2).effect ab.2))) S.psiHat‖ ^ 2)

















end ExtendedLineGame

end

end MIPStarRE.QPBT
