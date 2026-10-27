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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_MainTheorem_ScalarBounds_Definitions
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Game
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_GameValue
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Strategy
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_Measurements
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Consistency_State
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Correspondence
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Error
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Strategy
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Support
import Definitions.Def_QPBT_QPBT_Games_StrategyClasses
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Simultaneous polynomial measurements for a general simultaneity parameter

`prop:ld-simultaneous-general-k` produces, from a projective strategy for the
directly indexed low-degree game at parameters `(q, m, d, k)` succeeding with
probability at least `1 - ε`, a pair of polynomial-tuple measurements
satisfying the three consistency relations of `lem:ld-soundness`.

The reduction applies the case `k = 1` once, to the combined strategy of
`def:ld-combined-strategy` at the combined parameters `(q, m + k, d, 1)`: by
`lem:ld-combined-value` that strategy succeeds with probability at least
`1 - 10 ε`, so the case `k = 1` produces measurements with outcomes in the
polynomials of `m + k` variables, satisfying the three relations with the error
of `thm:main-formal` at the combined parameters, and
`lem:ld-combining-recovery` post-processes them by the recovery map of
`def:ld-combining-map`, at the cost of `(m + k) d / q` in the two point
relations.

The displayed error is `Test.mainFormalError` from the direct `k = 1` result
derived from `thm:main-formal` at the combined parameters, plus `(m + k) d / q`.
Its absorption into `deltaLd` at the original parameters, with the universal
constants `a = 10^23` and `b = 1/80000`, is
`exists_directCombinedTransportConstants`, and the absorbed form of the
conclusion is `exists_direct_ld_soundness`.

## Main statements

* `exists_directSimultaneousPolynomialMeasurements_combinedError` —
  `prop:ld-simultaneous-general-k` with the error displayed in the parameters
  of the combined game.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1409-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:682-715`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

set_option maxHeartbeats 1600000 in

theorem MIPStarRE.QPBT.exists_directSimultaneousPolynomialMeasurements_combinedError
    (D : _root_.MIPStarRE.QPBT.DirectLdParams) (S : _root_.MIPStarRE.QPBT.Strategy (_root_.MIPStarRE.QPBT.directLdGame D)) (hS : S.IsProjective)
    (ε : _root_.LIDT.MIPStarRE.LDT.Error) (hwin : 1 - ε ≤ S.value) :
    ∃ GA : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιA,
      ∃ GB : _root_.MIPStarRE.QPBT.DirectPolyMeasTuple D S.ιB,
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              (((S.A (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              ((GB.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome))
            S.ψ ≤
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.combined.toLDTParameters
              (_root_.MIPStarRE.QPBT.directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / D.q ∧
        _root_.MIPStarRE.QPBT.consistencyDefect
            (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D))
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron
              ((GA.postprocess (_root_.MIPStarRE.QPBT.evalDirectPolyTupleAt u)).effect outcome) 1)
            (fun u outcome => _root_.MIPStarRE.QPBT.heteroKron 1
              (((S.B (_root_.MIPStarRE.QPBT.directLdPointQuestionOf D u)).postprocess
                (_root_.MIPStarRE.QPBT.directLdPointValuesOrZero D)).effect outcome))
            S.ψ ≤
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.combined.toLDTParameters
              (_root_.MIPStarRE.QPBT.directLdAuxParameter D.combined) (3 * (10 * ε)) +
            ((D.combined.m * D.d : ℕ) : ℝ) / D.q ∧
        _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Unit)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron (GA.effect g) 1)
            (fun _ g => _root_.MIPStarRE.QPBT.heteroKron 1 (GB.effect g)) S.ψ ≤
          _root_.LIDT.MIPStarRE.LDT.Test.mainFormalError D.combined.toLDTParameters
            (_root_.MIPStarRE.QPBT.directLdAuxParameter D.combined) (3 * (10 * ε)) := by sorry
