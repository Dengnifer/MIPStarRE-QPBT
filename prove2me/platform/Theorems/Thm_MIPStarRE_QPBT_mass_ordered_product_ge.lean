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
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Games_Distance
import Definitions.Def_QPBT_QPBT_Games_DistanceTheorems_Support
import Definitions.Def_QPBT_QPBT_Games_Sandwich_Defs

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus

/-! # Ordered product masses and the assembly of the pasting estimate

This module records the mass estimates of step 3 of the proof of the adopted
statement of `lem:pasting`, the fine commutator mass of step 5, the assembly of
those estimates into the explicit bound on the defect of the pasted family, the
bound of one on the defect of an arbitrary pair of placed families, and the
scalar comparison of the assembled bound with the error function of the
theorem.  The proof of the adopted statement is recorded in
`docs/paper-gaps/qpbt_pasting-product-error.tex`.

## References

Blueprint `ch12_qpbt_games.tex:960-990`, paper origin
`references/qpbt-paper/06_nonlocal_games_and_mipstar.tex:504-525`.
-/



open scoped BigOperators MatrixOrder Matrix ComplexOrder

open MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum
open MIPStarRE.QPBT.DistanceCalculus

theorem MIPStarRE.QPBT.mass_ordered_product_ge {X R₁ R₂ ι : Type*}
    [Fintype X] [DecidableEq X] [Fintype R₁] [DecidableEq R₁]
    [Fintype R₂] [DecidableEq R₂] [Fintype ι] [DecidableEq ι]
    (D : _root_.LIDT.MIPStarRE.LDT.Distribution X) (Ac P : X → _root_.LIDT.MIPStarRE.Quantum.Measurement R₁ ι) (Q : X → _root_.LIDT.MIPStarRE.Quantum.Measurement R₂ ι)
    (ψ : EuclideanSpace ℂ (ι × ι)) (d K : ℝ)
    (hD : D.IsProbability) (hψ : ‖ψ‖ = 1)
    (hAc : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Ac q))
    (hQ : ∀ q, _root_.MIPStarRE.QPBT.Measurement.IsProjective (Q q))
    (hd : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q a => _root_.MIPStarRE.QPBT.heteroKron ((Ac q).effect a) 1)
      (fun q a => _root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect a)) ψ ≤ d)
    (hK : _root_.MIPStarRE.QPBT.opFamilyDistSq D (fun q (ab : R₁ × R₂) => _root_.MIPStarRE.QPBT.heteroKron 1
      ((P q).effect ab.1 * (Q q).effect ab.2 -
        (Q q).effect ab.2 * (P q).effect ab.1)) (fun _ _ => 0) ψ ≤ K) :
    1 - 2 * Real.sqrt d - d - 2 * Real.sqrt K - K ≤
      _root_.LIDT.MIPStarRE.LDT.avgOver D (fun q => ∑ ab : R₁ × R₂, ‖_root_.MIPStarRE.QPBT.applyOperatorToState
        (_root_.MIPStarRE.QPBT.heteroKron 1 ((P q).effect ab.1 * (Q q).effect ab.2)) ψ‖ ^ 2) := by sorry
