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
import Definitions.Def_QPBT_QPBT_Games_Consistency
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_TensorSupport
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.RecoveryInternal
end MIPStarRE.QPBT.RecoveryInternal
namespace MIPStarRE.QPBT.SandwichProduct
end MIPStarRE.QPBT.SandwichProduct

/-!
# Transporting a consistency relation along the recovery step

The recovery step of `lem:ld-combining-recovery` replaces a relation between a
point measurement of the original strategy read through a combination and a
measurement of the combined game read at a point of the combined space by a
relation between the point measurement itself and the same measurement read
through the recovered polynomial tuple.  This module isolates the consistency
calculus of that replacement, in a form which does not mention the low-degree
game.

Both relations are diagonal overlaps of the same pair of measurements placed on
opposite tensor factors, and the two relabellings differ only on the event that
the recovered outcome disagrees with the outcome of the point measurement while
the two relabellings agree.  The probability of that event, averaged over the
auxiliary sample, is bounded at each question by a quantity depending only on
the outcome of the second measurement; since the first measurement is complete,
the total Born weight of an outcome of the second measurement does not depend on
the question, and the bound may therefore be averaged over the question against
that weight.

The two conclusions of `lem:ld-soundness` transported here place the point
measurement on opposite tensor factors, so the calculus is recorded twice, once
for each placement; the two statements share the averaging estimate, which is
insensitive to the placement.

## Main statements

* `consistencyDefect_le_of_recoveryBound` — the transport of a consistency
  relation along a relabelling which is correct off a rare event, with the
  point measurement on the first tensor factor.
* `consistencyDefect_le_of_recoveryBound_right` — the same transport with the
  point measurement on the second tensor factor.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:219-288`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus
open MIPStarRE.QPBT.SandwichProduct



open MIPStarRE.QPBT.RecoveryInternal

/-! ## Pair expansions of the diagonal overlap -/









/-! ## The averaging estimate -/





/-! ## The transport of a consistency relation -/

open MIPStarRE.QPBT.RecoveryInternal

set_option maxHeartbeats 1600000 in

theorem MIPStarRE.QPBT.consistencyDefect_le_of_recoveryBound
    {X Y β Γ R ιA ιB : Type*}
    [Fintype X] [DecidableEq X] [Nonempty X]
    [Fintype Y] [DecidableEq Y] [Nonempty Y]
    [Fintype β] [DecidableEq β] [Fintype Γ] [DecidableEq Γ]
    [Fintype R] [DecidableEq R]
    [Fintype ιA] [DecidableEq ιA] [Fintype ιB] [DecidableEq ιB]
    (A : X → _root_.LIDT.MIPStarRE.Quantum.Measurement β ιA) (B : _root_.LIDT.MIPStarRE.Quantum.Measurement Γ ιB)
    (ψ : EuclideanSpace ℂ (ιA × ιB)) (hψ : ‖ψ‖ = 1)
    (f : X → Γ → β) (e₁ : X → Y → β → R) (f₁ : X → Y → Γ → R)
    (F : X → Γ → ℝ) (η : ℝ)
    (hFbound : ∀ x b g, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution Y)
      (fun y => if f x g ≠ b ∧ e₁ x y b = f₁ x y g then (1 : ℝ) else 0) ≤ F x g)
    (hFavg : ∀ g, _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X) (fun x => F x g) ≤ η) :
    _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution X)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron ((A x).effect b) 1)
        (fun x b => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f x)).effect b)) ψ ≤
      _root_.MIPStarRE.QPBT.consistencyDefect (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (X × Y))
        (fun z r => _root_.MIPStarRE.QPBT.heteroKron (((A z.1).postprocess (e₁ z.1 z.2)).effect r) 1)
        (fun z r => _root_.MIPStarRE.QPBT.heteroKron 1 ((B.postprocess (f₁ z.1 z.2)).effect r)) ψ + η := by sorry
