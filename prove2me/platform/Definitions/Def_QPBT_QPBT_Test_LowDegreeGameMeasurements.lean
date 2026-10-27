-- Generated from QPBT/Test/LowDegreeGameMeasurements.lean by skeleton subtraction.
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
import Definitions.Def_LIDT_MIPStarRE_LDT_Test_StrategyCore
import Definitions.Def_LIDT_MIPStarRE_Quantum_Measurement
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Games_DistributionMarginals
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Mathlib

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# Low-degree sampling and polynomial measurements

The low-degree question laws have uniform point and coordinate-index marginals,
and every sampled line is incident to its paired point.  Polynomial outcomes
are bounded multivariate polynomials. The soundness theorem using these
definitions is proved in `LowDegreeGameTheorems`.

## References

The principal definition and theorem are blueprint `def:ld-meas` and
`lem:ld-soundness`. Their paper origin is
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:243-287,392-480`.
The dimension-divisibility hypothesis is documented in
`docs/paper-gaps/qpbt_ld-dimension-divisibility.tex`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-!
### Formalization-only auxiliary facts about the ambient low-degree space
-/

/-- Formalization-only auxiliary equivalence splitting an ambient low-degree
vector into its point, seed, and direction blocks. -/
def ldSpaceSplit (L : _root_.MIPStarRE.QPBT.LdParams) :
    _root_.MIPStarRE.QPBT.LdSpace L ≃ ((Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) × _root_.MIPStarRE.QPBT.ScalarQ L) × (Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) where
  toFun z := ((_root_.MIPStarRE.QPBT.LdSpace.point z, _root_.MIPStarRE.QPBT.LdSpace.seed z), _root_.MIPStarRE.QPBT.LdSpace.direction z)
  invFun p := fun i =>
    match i with
    | .inl (.inl j) => p.1.1 j
    | .inl (.inr _) => p.1.2
    | .inr j => p.2 j
  left_inv z := by
    funext i
    rcases i with (j | u) | j
    · rfl
    · cases u
      rfl
    · rfl
  right_inv p := by
    obtain ⟨⟨a, b⟩, c⟩ := p
    rfl





/-- The coordinate index of a uniformly random scalar is uniform.  This is the
balance assertion in `def:ld-question-distribution`, blueprint
`lem:chi-index-uniform`, paper
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:215-221`.
-/
theorem uniformDistribution_map_chiIndex (L : _root_.MIPStarRE.QPBT.LdParams) :
    (_root_.LIDT.MIPStarRE.LDT.uniformDistribution (_root_.MIPStarRE.QPBT.ScalarQ L)).map (_root_.MIPStarRE.QPBT.chiIndex L) =
      _root_.LIDT.MIPStarRE.LDT.uniformDistribution (Fin L.m) := by
  letI : Nonempty (Fin (L.q / L.m)) :=
    Fin.pos_iff_nonempty.mp L.seedFiberCard_pos
  exact _root_.MIPStarRE.QPBT.uniformDistribution_map_fst_of_equiv
    (_root_.MIPStarRE.QPBT.seedFiberEquiv L) (_root_.MIPStarRE.QPBT.chiIndex L) fun s => (_root_.MIPStarRE.QPBT.seedFiberEquiv_fst L s).symm

















/-- Bounded multivariate polynomials form a finite set over a finite coefficient
semiring. This is the finite outcome set required by blueprint
`def:ld-meas`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable instance polyFuncFintype (m : ℕ) (K : Type*)
    [CommSemiring K] [Fintype K] (d : ℕ) : Fintype ↥(_root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc m K d) := by
  letI : Finite ↥(_root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc m K d) := Module.finite_of_finite K
  exact Fintype.ofFinite _

/-- A bounded multivariate polynomial outcome over an arbitrary finite
coefficient semiring. -/
noncomputable abbrev PolyIndex (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] (d : ℕ) := ↥(_root_.LIDT.MIPStarRE.LDT.Preliminaries.polyFunc m K d)

/-- A POVM indexed by one bounded multivariate polynomial. -/
noncomputable abbrev PolyMeas (m : ℕ) (K : Type*) [CommSemiring K]
    [Fintype K] [DecidableEq K] (d : ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.PolyIndex m K d) ι

/-- The dependent family in `def:ld-meas`: component `i` may
have its own coefficient field, number of variables, and degree bound.
Blueprint `def:ld-meas`, paper
`08_classical_and_quantum_low_degree_tests.tex:394-408`. -/
noncomputable abbrev PolyMeasFamily (k : ℕ) (K : Fin k → Type*)
    [∀ i, CommSemiring (K i)] [∀ i, Fintype (K i)]
    [∀ i, DecidableEq (K i)] (m d : Fin k → ℕ) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement ((i : Fin k) → _root_.MIPStarRE.QPBT.PolyIndex (m i) (K i) (d i)) ι

/-- A simultaneous tuple of `L.k` bounded polynomial representatives. -/
noncomputable abbrev PolyTuple (L : _root_.MIPStarRE.QPBT.LdParams) :=
  Fin L.k → _root_.MIPStarRE.QPBT.PolyIndex L.m (_root_.MIPStarRE.QPBT.ScalarQ L) L.d

/-- The constant-family specialization used by `lem:ld-soundness`. -/
noncomputable abbrev PolyMeasTuple (L : _root_.MIPStarRE.QPBT.LdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  _root_.MIPStarRE.QPBT.PolyMeasFamily L.k (fun _ => _root_.MIPStarRE.QPBT.ScalarQ L) (fun _ => L.m) (fun _ => L.d) ι

/-- Evaluate every component of a polynomial tuple at a point. -/
def evalPolyTupleAt {L : _root_.MIPStarRE.QPBT.LdParams} (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L)
    (g : _root_.MIPStarRE.QPBT.PolyTuple L) : Fin L.k → _root_.MIPStarRE.QPBT.ScalarQ L :=
  fun j => MvPolynomial.eval u (g j).1

/-- Embed a geometric point into the ambient coefficient space used by a
point question. -/
def pointSpaceOf (L : _root_.MIPStarRE.QPBT.LdParams) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) : _root_.MIPStarRE.QPBT.LdSpace L :=
  fun i => match i with
  | .inl (.inl j) => u j
  | .inl (.inr _) => 0
  | .inr _ => 0

/-- The typed low-degree point question associated with `u`. -/
def ldPointQuestionOf (L : _root_.MIPStarRE.QPBT.LdParams) (u : Fin L.m → _root_.MIPStarRE.QPBT.ScalarQ L) : _root_.MIPStarRE.QPBT.LdQuestion L :=
  (.point, _root_.MIPStarRE.QPBT.pointSpaceOf L u)

/-- Read the point component of a low-degree answer, sending answers of the
wrong form to the fixed zero tuple. This total relabeling turns the strategy's
answer measurement into the point POVM used by `lem:ld-soundness`. -/
def ldPointValuesOrZero (L : _root_.MIPStarRE.QPBT.LdParams) : _root_.MIPStarRE.QPBT.LdAnswer L → Fin L.k → _root_.MIPStarRE.QPBT.ScalarQ L
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- The quantitative error function in `lem:ld-soundness`.  Its argument order
is `(a, b, ε, q, m, d, k)`. -/
noncomputable def deltaLd (a b ε : ℝ) (q m d k : ℕ) : ℝ :=
  a * Real.rpow (((d * m * k : ℕ) : ℝ)) a *
    (Real.rpow ε b + Real.rpow (q : ℝ) (-b) +
      Real.rpow 2 (-(b * ((m * d : ℕ) : ℝ))))

end

end MIPStarRE.QPBT
