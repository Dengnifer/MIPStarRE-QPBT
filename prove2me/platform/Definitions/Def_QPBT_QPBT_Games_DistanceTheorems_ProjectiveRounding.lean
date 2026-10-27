-- Generated from QPBT/Games/DistanceTheorems/ProjectiveRounding.lean by skeleton subtraction.
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

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
end LIDT.MIPStarRE.LDT.MakingMeasurementsProjective
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-!
# Projective rounding for consistent POVMs

This module proves the orthonormalization lemma `lem:ortho` with an explicit
error constant: if a POVM `Q` on Alice's space and a POVM `R` on Bob's space are
`δ`-consistent on a unit bipartite state `ψ`, then Alice has a projective
measurement `P` on her original space with `P_a ⊗ 1` within `220 · δ^(1/4)` of
`Q_a ⊗ 1` on `ψ`.

The argument passes to Alice's reduced state and follows the construction of the
LDT orthonormalization theorem. Rounding the almost-projective effects of `Q` and
reducing their ranks gives a family of projectors `Q_a` whose ranges are almost
orthogonal; assembling those ranges into one auxiliary space gives an operator
`X`, whose positive-Gram polar factor `X̂` is a coisometry; and pulling the block
projector of each outcome back along `X̂`, so that `P_a = X̂ᴴ T_a X̂`, gives a
projective family close to `Q`. The family `P` lives on Alice's original space
and is completed to a measurement at one fixed outcome once its missing state
mass has been shown to be small.

## References

- `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:131-153`
- Blueprint `lem:ortho`
- Blueprint `lem:ortho-explicit-constant`, the statement proved in this module
- `references/ldt-paper/orthonormalization.tex`
-/

@[expose] public section

open scoped BigOperators Matrix MatrixOrder ComplexOrder

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum DistanceCalculus
open LIDT.MIPStarRE.LDT.MakingMeasurementsProjective

noncomputable section

/-- The normalized pure state whose vector is the given unit Euclidean vector. -/
 noncomputable def roundPureState {ι : Type*}
    [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) : _root_.LIDT.MIPStarRE.LDT.PureState ι where
  vector := ψ.ofLp
  unit := by
    calc
      star ψ.ofLp ⬝ᵥ ψ.ofLp = ψ.ofLp ⬝ᵥ star ψ.ofLp := dotProduct_comm _ _
      _ = inner ℂ ψ ψ := (EuclideanSpace.inner_eq_star_dotProduct ψ ψ).symm
      _ = (‖ψ‖ ^ 2 : ℂ) := inner_self_eq_norm_sq_to_K ψ
      _ = 1 := by rw [hψ]; norm_num





/-- Regard a nonempty finite coordinate set as an LDT finite Hilbert space. -/
@[reducible]  def roundFiniteHilbertSpace (ι : Type*) [Fintype ι] [DecidableEq ι]
    [Nonempty ι] : _root_.LIDT.MIPStarRE.LDT.MakingMeasurementsProjective.FiniteHilbertSpace :=
  { carrier := ι
    instFintype := inferInstance
    instDecidableEq := inferInstance
    instNonempty := inferInstance }









end

end MIPStarRE.QPBT
