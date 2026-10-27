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
import Definitions.Def_LIDT_MIPStarRE_Quantum_FiniteMatrix_Basic
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # Marginal mass outside the support of a reference measurement

A complete reference measurement supported on an allowed outcome set bounds
the other measurement's mass outside that set by their bipartite consistency
defect. The measurements act on separate tensor factors of the same state.
Neither projectivity nor state normalization is needed; for a unit vector the
quadratic forms are the corresponding Born probabilities.

These are formalization-only auxiliary estimates for the non-encoding mass
calculation in blueprint `eq:qld-nonencoding-mass`. They can be composed with
the codeword-defect comparison after constructing an encoding-supported
reference measurement on the opposite tensor factor. They do not construct
that reference or establish its evaluated consistency, and do not prove the
non-encoding marginal-mass bound or global-pair witness existence.

## References

- Blueprint `eq:qld-nonencoding-mass` and `lem:qld-nonencoding-mass-bound`.
- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1483-1498`,
  the consistency calculation in `lem:qld-construct-the-paulis` that the
  blueprint's non-encoding mass estimate supports.
- `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:232-248`,
  the bipartite consistency defect.
-/



open scoped BigOperators MatrixOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus

theorem MIPStarRE.QPBT.mass_outside_support_le_point_defect
    {Outcome Left Right : Type*}
    [Fintype Outcome] [DecidableEq Outcome]
    [Fintype Left] [DecidableEq Left] [Fintype Right] [DecidableEq Right]
    (meas : _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome Left) (reference : _root_.LIDT.MIPStarRE.Quantum.Measurement Outcome Right)
    (psi : EuclideanSpace ℂ (Left × Right)) (allowed : Finset Outcome)
    (hsupport : ∀ outcome, outcome ∉ allowed → reference.effect outcome = 0) :
    (∑ outcome ∈ Finset.univ.filter (fun outcome => outcome ∉ allowed),
      _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) 1)) ≤
      ∑ outcome : Outcome, ∑ other : Outcome, if outcome = other then 0 else
        _root_.MIPStarRE.QPBT.DistanceCalculus.stateQForm psi (_root_.MIPStarRE.QPBT.heteroKron (meas.effect outcome) (reference.effect other)) := by sorry
