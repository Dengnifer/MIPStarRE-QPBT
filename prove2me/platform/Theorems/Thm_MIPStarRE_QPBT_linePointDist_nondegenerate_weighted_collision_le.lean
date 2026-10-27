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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_DistributionAux
import Definitions.Def_QPBT_QPBT_Observables_LineDefs
import Definitions.Def_QPBT_QPBT_Observables_WinImplications_LowDegree
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Weighted collision bounds for sampled lines

This module lifts the uniform affine-parameter collision estimate to the mixed
line-point distribution with an arbitrary nonnegative weight depending only on
the sampled line.

## References

The estimate is the Schwartz--Zippel step in `lem:qld-xz-lines`,
`references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:950-955`.
-/



open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT

theorem MIPStarRE.QPBT.linePointDist_nondegenerate_weighted_collision_le {L : _root_.MIPStarRE.QPBT.LdParams}
    {bound : ℕ} (weight : _root_.MIPStarRE.QPBT.LineDesc L → ℝ)
    (hweight : ∀ line, 0 ≤ weight line) (first second : _root_.MIPStarRE.QPBT.DegPoly L bound)
    (hne : first ≠ second) :
    _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample =>
      if sample.1.direction ≠ 0 then weight sample.1 *
        (if _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 first = _root_.MIPStarRE.QPBT.evalOpt sample.1 sample.2 second
          then 1 else 0) else 0) ≤
      (bound : ℝ) / Fintype.card (_root_.MIPStarRE.QPBT.ScalarQ L) *
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.MIPStarRE.QPBT.linePointDist L) (fun sample =>
          if sample.1.direction ≠ 0 then weight sample.1 else 0) := by sorry
