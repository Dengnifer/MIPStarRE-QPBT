-- Generated from QPBT/Combining/DirectLowDegree/Transport/Combining/Recovery.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Preliminaries_Polynomials
import Definitions.Def_LIDT_MIPStarRE_LDT_Tactic_AvgCongr
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Linearity
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Parameters
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Transport_Combining_Restriction
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The joint recovery estimate in the point and combining variables

`lem:ld-combining-recovery` compares the tuple of values at a point of the
components recovered from an outcome of the combined game with the tuple of
answers of the point measurement of the original game.  The comparison rests on
a joint estimate over the sampled point `u` and the sampled combining vector
`α`: for every outcome `p` of the combined game and every tuple `b` of scalars,
the event that the recovered tuple of values at `u` differs from `b` while the
value of `p` at the combined point agrees with the combination `∑_r α_r b_r`
has probability at most `(m + k) d / q`.

Two cases occur.  If `p` is the combined polynomial of a tuple `g`, its value at
the combined point is the combination `∑_r α_r g_r(u)`, and two combinations
with distinct coefficient tuples agree at a uniformly sampled `α` with
probability at most `1 / q`.  If `p` is not combined, then by
`lem:ld-combining-exact-linearity` its restriction `p(u, ·)` fails to be a
linear form except with probability `m d / q` over `u`, and off that event the
restriction and the linear form of `b` are distinct polynomials of total degree
at most `k d`, so they agree at a uniformly sampled `α` with probability at
most `k d / q`.

The estimate is recorded in two stages, because the consistency calculus
averages it against Born weights which depend on the sampled point but not on
the sampled combining vector: a bound at a fixed point which does not depend on
the tuple `b`, and the average of that bound over the point.

## Main statements

* `directCombinedRecoveryLocalBound` — the bound at a fixed point.
* `directCombinedRecoveryEvent_avg_le` — the estimate at a fixed point.
* `directCombinedRecoveryLocalBound_avg_le` — the average of the bound at a
  fixed point over a uniformly sampled point.
* `directCombinedRecoveryBadEvent_avg_le` — the joint estimate of
  `lem:ld-combining-recovery`.

## References

* `references/neexp-paper/05_quantum_preliminaries.tex:1440-1503`
* `references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:413-458`
* `blueprint/src/chapter/ch13_qpbt_test.tex:617-680`
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries

noncomputable section

/-! ## Elementary facts about the parameters -/







/-! ## The collision estimates in the combining variables -/





/-! ## The estimate at a fixed point -/

open scoped Classical in
/-- The bound at a fixed point of the recovery step: the collision probability
`1 / q` of two combinations when the outcome is combined, and otherwise the
indicator that the restriction of the outcome at the point is a linear form
together with the collision probability `k d / q` of two polynomials of total
degree at most `k d` in the combining variables. -/
def directCombinedRecoveryLocalBound (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (p : _root_.MIPStarRE.QPBT.PolyIndex D.combined.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) : _root_.LIDT.MIPStarRE.LDT.Error :=
  if _root_.MIPStarRE.QPBT.IsDirectCombined D p then (1 : _root_.LIDT.MIPStarRE.LDT.Error) / D.q
  else
    (if ∃ c : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D,
        _root_.MIPStarRE.QPBT.combinedRestrict p.1 u = _root_.MIPStarRE.QPBT.combiningLinearForm c then (1 : _root_.LIDT.MIPStarRE.LDT.Error) else 0) +
      ((D.k * D.d : ℕ) : _root_.LIDT.MIPStarRE.LDT.Error) / D.q





/-! ## The averaged estimate -/





end

end MIPStarRE.QPBT
