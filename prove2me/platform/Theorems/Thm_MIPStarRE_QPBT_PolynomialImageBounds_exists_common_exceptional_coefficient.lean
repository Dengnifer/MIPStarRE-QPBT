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
import Mathlib
import Mathlib.Analysis.MeanInequalitiesPow

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT.DistanceCalculus
end MIPStarRE.QPBT.DistanceCalculus
namespace MIPStarRE.QPBT.PolynomialImageBounds
end MIPStarRE.QPBT.PolynomialImageBounds

/-!
# Common exceptional fibers for polynomial coefficients

A nonconstant polynomial in one block, with polynomial coefficients in a
second block, has a nonzero coefficient at a nonconstant monomial. Its zero set controls
all exceptional specializations simultaneously, independently of the outcome
of a measurement. The weights may depend on the fixed block but not on the
block being averaged.

## References

Paper `references/qpbt-paper/14_analysis_of_the_pauli_basis_test.tex:1341-1358`,
especially `eq:qld-g-2`; support for blueprint `lem:qld-4-7`.
-/



open scoped BigOperators Matrix MatrixOrder ComplexOrder

open MIPStarRE.QPBT.PolynomialImageBounds

open LIDT.MIPStarRE.LDT hiding Measurement
open LIDT.MIPStarRE.Quantum MIPStarRE.QPBT.DistanceCalculus



variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

theorem MIPStarRE.QPBT.PolynomialImageBounds.exists_common_exceptional_coefficient {n k C D : ℕ}
    (p : MvPolynomial (Fin n) (MvPolynomial (Fin k) F))
    (hp : ¬ ∃ r, p = MvPolynomial.C r)
    (hcoeff : ∀ e, (p.coeff e).totalDegree ≤ C) (hdegree : p.totalDegree ≤ D) :
    ∃ e : Fin n →₀ ℕ, e ≠ 0 ∧ p.coeff e ≠ 0 ∧
      _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin k → F))
        (fun z => if MvPolynomial.eval z (p.coeff e) = 0 then 1 else 0) ≤
          (C : ℝ) / Fintype.card F ∧
      ∀ z : Fin k → F, MvPolynomial.eval z (p.coeff e) ≠ 0 → ∀ b : F,
        _root_.LIDT.MIPStarRE.LDT.avgOver (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin n → F))
          (fun x => if MvPolynomial.eval x (MvPolynomial.map (MvPolynomial.eval z) p) = b
            then 1 else 0) ≤ (D : ℝ) / Fintype.card F := by sorry
