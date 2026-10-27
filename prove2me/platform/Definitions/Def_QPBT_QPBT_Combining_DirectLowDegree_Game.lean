-- Generated from QPBT/Combining/DirectLowDegree/Game.lean by skeleton subtraction.
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
import Definitions.Def_QPBT_QPBT_Algebra_Coefficients
import Definitions.Def_QPBT_QPBT_Algebra_FieldBasis
import Definitions.Def_QPBT_QPBT_Algebra_Lines
import Definitions.Def_QPBT_QPBT_Combining_DirectLowDegree_Geometry
import Definitions.Def_QPBT_QPBT_Games_Defs
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGame
import Definitions.Def_QPBT_QPBT_Test_LowDegreeGameMeasurements
import Mathlib
import Theorems.Thm_LIDT_MIPStarRE_LDT_Distribution_IsProbability_map

namespace LIDT.MIPStarRE.LDT
end LIDT.MIPStarRE.LDT
namespace LIDT.MIPStarRE.LDT.Preliminaries
end LIDT.MIPStarRE.LDT.Preliminaries
namespace LIDT.MIPStarRE.Quantum
end LIDT.MIPStarRE.Quantum
namespace MIPStarRE.QPBT
end MIPStarRE.QPBT

/-!
# The directly indexed low-degree game

This module defines polynomial evaluation, questions, answers, and the game
for the directly indexed low-degree interface.

## References

The underlying game is blueprint
`def:ld-game`, with source origin
`references/qpbt-paper/08_classical_and_quantum_low_degree_tests.tex:31-391`.
-/

@[expose] public section

open scoped BigOperators

namespace MIPStarRE.QPBT

open LIDT.MIPStarRE.LDT
open LIDT.MIPStarRE.LDT.Preliminaries
open LIDT.MIPStarRE.Quantum

noncomputable section

/-- Coefficient lists for a univariate polynomial of degree at most `c` in the
direct scalar field. -/
abbrev DirectDegPoly (D : _root_.MIPStarRE.QPBT.DirectLdParams) (c : ℕ) :=
  Fin (c + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D

/-- A direct line polynomial evaluates to `a` at `u` when `u` lies on the line
and every parameter presenting `u` gives value `a`.  The universal clause
keeps the zero-direction case explicit. -/
def DirectEvaluatesTo {D : _root_.MIPStarRE.QPBT.DirectLdParams} {c : ℕ} (line : _root_.MIPStarRE.QPBT.DirectLineDesc D)
    (f : _root_.MIPStarRE.QPBT.DirectDegPoly D c) (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (a : _root_.MIPStarRE.QPBT.DirectScalarQ D) : Prop :=
  (∃ t : _root_.MIPStarRE.QPBT.DirectScalarQ D, u = line.base + t • line.direction) ∧
    ∀ t : _root_.MIPStarRE.QPBT.DirectScalarQ D, u = line.base + t • line.direction →
      _root_.MIPStarRE.QPBT.evalCoefficient f t = a

/-- Option-completed evaluation of a direct line polynomial.  `none` is an
explicit outcome when the point does not determine an evaluation; no field
value is used as a fallback. -/
noncomputable def directEvalOpt {D : _root_.MIPStarRE.QPBT.DirectLdParams} {c : ℕ}
    (line : _root_.MIPStarRE.QPBT.DirectLineDesc D) (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (f : _root_.MIPStarRE.QPBT.DirectDegPoly D c) : Option (_root_.MIPStarRE.QPBT.DirectScalarQ D) := by
  classical
  exact if h : ∃ a : _root_.MIPStarRE.QPBT.DirectScalarQ D, _root_.MIPStarRE.QPBT.DirectEvaluatesTo line f u a then
    some (Classical.choose h)
  else none

/-- The typed question alphabet of the directly indexed game. -/
abbrev DirectLdQuestion (D : _root_.MIPStarRE.QPBT.DirectLdParams) := _root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.DirectLdSpace D

/-- Canonicalize a common direct sample for one question type.  Irrelevant
coordinates are fixed, so point questions reveal no sampled line index and
axis-line questions reveal no diagonal direction. -/
noncomputable def directLdMap (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    _root_.MIPStarRE.QPBT.LdType → _root_.MIPStarRE.QPBT.DirectLdSpace D → _root_.MIPStarRE.QPBT.DirectLdSpace D
  | .point, sample => ⟨sample.point, D.firstIndex, 0⟩
  | .aline, sample =>
      let direction := _root_.MIPStarRE.QPBT.coordinateDirection sample.index
      ⟨_root_.MIPStarRE.QPBT.lineRepMap direction sample.point, sample.index, 0⟩
  | .dline, sample =>
      let direction := _root_.MIPStarRE.QPBT.directPrefixProjection sample.index sample.direction
      ⟨_root_.MIPStarRE.QPBT.lineRepMap direction sample.point, sample.index, direction⟩

/-- The directly indexed question distribution.  It has the same uniform
ordered type-pair branches as `ldQuestionDistribution`, but its common sample
contains an actual coordinate index rather than a field seed. -/
noncomputable def directLdQuestionDistribution (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    _root_.LIDT.MIPStarRE.LDT.Distribution (_root_.MIPStarRE.QPBT.DirectLdQuestion D × _root_.MIPStarRE.QPBT.DirectLdQuestion D) :=
  (_root_.LIDT.MIPStarRE.LDT.uniformDistribution ((_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) × _root_.MIPStarRE.QPBT.DirectLdSpace D)).map fun sample =>
    ((sample.1.1, _root_.MIPStarRE.QPBT.directLdMap D sample.1.1 sample.2),
      (sample.1.2, _root_.MIPStarRE.QPBT.directLdMap D sample.1.2 sample.2))

/-- The directly indexed question law is probabilistic. -/
theorem directLdQuestionDistribution_isProbability (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    (_root_.MIPStarRE.QPBT.directLdQuestionDistribution D).IsProbability := by
  exact (_root_.LIDT.MIPStarRE.LDT.uniformDistribution_isProbability
    ((_root_.MIPStarRE.QPBT.LdType × _root_.MIPStarRE.QPBT.LdType) × _root_.MIPStarRE.QPBT.DirectLdSpace D)).map _

/-- The answer alphabet of the directly indexed game. -/
inductive DirectLdAnswer (D : _root_.MIPStarRE.QPBT.DirectLdParams) where
  | pointVals (a : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D)
  | alinePolys (a : Fin D.k → Fin (D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D)
  | dlinePolys (a : Fin D.k → Fin (D.m * D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D)
  deriving DecidableEq

/-- A finite code for the directly indexed answer alphabet. -/
abbrev DirectLdAnswerCode (D : _root_.MIPStarRE.QPBT.DirectLdParams) :=
  (Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) ⊕
    ((Fin D.k → Fin (D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D) ⊕
      (Fin D.k → Fin (D.m * D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D))

/-- The canonical code equivalence for `DirectLdAnswer`, sending point,
axis-line, and diagonal-line answers to the three summands. -/
noncomputable def directLdAnswerEquiv (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    _root_.MIPStarRE.QPBT.DirectLdAnswer D ≃ _root_.MIPStarRE.QPBT.DirectLdAnswerCode D where
  toFun
    | .pointVals a => .inl a
    | .alinePolys a => .inr (.inl a)
    | .dlinePolys a => .inr (.inr a)
  invFun
    | .inl a => .pointVals a
    | .inr (.inl a) => .alinePolys a
    | .inr (.inr a) => .dlinePolys a
  left_inv := by intro answer; cases answer <;> rfl
  right_inv := by
    intro answer
    rcases answer with a | a
    · rfl
    · rcases a with a | a <;> rfl

instance instInhabitedDirectLdAnswer (D : _root_.MIPStarRE.QPBT.DirectLdParams) : Inhabited (_root_.MIPStarRE.QPBT.DirectLdAnswer D) :=
  ⟨.pointVals 0⟩

noncomputable instance instFintypeDirectLdAnswer (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    Fintype (_root_.MIPStarRE.QPBT.DirectLdAnswer D) :=
  Fintype.ofEquiv (_root_.MIPStarRE.QPBT.DirectLdAnswerCode D) (_root_.MIPStarRE.QPBT.directLdAnswerEquiv D).symm

/-- Check that a direct-game answer has the constructor required by its
question type. -/
def validDirectLdAnswer {D : _root_.MIPStarRE.QPBT.DirectLdParams} (t : _root_.MIPStarRE.QPBT.LdType)
    (answer : _root_.MIPStarRE.QPBT.DirectLdAnswer D) : Bool :=
  match t, answer with
  | .point, .pointVals _ => true
  | .aline, .alinePolys _ => true
  | .dline, .dlinePolys _ => true
  | _, _ => false

/-- The directly indexed axis-line versus point acceptance relation. -/
def directAlinePointCondition (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (line point : _root_.MIPStarRE.QPBT.DirectLdSpace D)
    (f : Fin D.k → Fin (D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (a : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) : Prop :=
  ∀ t : _root_.MIPStarRE.QPBT.DirectScalarQ D,
    point.point = line.point + t • _root_.MIPStarRE.QPBT.coordinateDirection line.index →
      ∀ j : Fin D.k, _root_.MIPStarRE.QPBT.evalCoefficient (f j) t = a j

/-- The directly indexed diagonal-line versus point acceptance relation. -/
def directDlinePointCondition (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (line point : _root_.MIPStarRE.QPBT.DirectLdSpace D)
    (f : Fin D.k → Fin (D.m * D.d + 1) → _root_.MIPStarRE.QPBT.DirectScalarQ D)
    (a : Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D) : Prop :=
  ∀ t : _root_.MIPStarRE.QPBT.DirectScalarQ D,
    point.point = line.point + t • line.direction →
      ∀ j : Fin D.k, _root_.MIPStarRE.QPBT.evalCoefficient (f j) t = a j

/-- The directly indexed low-degree win predicate.  It differs from
`ldWinPredicate` only by reading the coordinate index directly from each line
question. -/
noncomputable def directLdWinPredicate (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    _root_.MIPStarRE.QPBT.DirectLdQuestion D → _root_.MIPStarRE.QPBT.DirectLdQuestion D →
      _root_.MIPStarRE.QPBT.DirectLdAnswer D → _root_.MIPStarRE.QPBT.DirectLdAnswer D → Bool :=
  open Classical in
  fun (tA, xA) (tB, xB) a b =>
    if _root_.MIPStarRE.QPBT.validDirectLdAnswer tA a && _root_.MIPStarRE.QPBT.validDirectLdAnswer tB b then
      match tA, tB, a, b with
      | .point, .point, .pointVals u, .pointVals v => decide (u = v)
      | .aline, .point, .alinePolys f, .pointVals u =>
          decide (_root_.MIPStarRE.QPBT.directAlinePointCondition D xA xB f u)
      | .point, .aline, .pointVals u, .alinePolys f =>
          decide (_root_.MIPStarRE.QPBT.directAlinePointCondition D xB xA f u)
      | .dline, .point, .dlinePolys f, .pointVals u =>
          decide (_root_.MIPStarRE.QPBT.directDlinePointCondition D xA xB f u)
      | .point, .dline, .pointVals u, .dlinePolys f =>
          decide (_root_.MIPStarRE.QPBT.directDlinePointCondition D xB xA f u)
      | .aline, .aline, .alinePolys f, .alinePolys g => decide (f = g)
      | .dline, .dline, .dlinePolys f, .dlinePolys g => decide (f = g)
      | _, _, _, _ => true
    else false

/-- The directly indexed low-degree game at an arbitrary positive dimension.
It is an internal analysis game, not the conditionally linear verifier game
`ldGame`. -/
@[reducible] noncomputable def directLdGame (D : _root_.MIPStarRE.QPBT.DirectLdParams) : _root_.MIPStarRE.QPBT.Game where
  QuestionA := _root_.MIPStarRE.QPBT.DirectLdQuestion D
  QuestionB := _root_.MIPStarRE.QPBT.DirectLdQuestion D
  AnswerA := _root_.MIPStarRE.QPBT.DirectLdAnswer D
  AnswerB := _root_.MIPStarRE.QPBT.DirectLdAnswer D
  μ := _root_.MIPStarRE.QPBT.directLdQuestionDistribution D
  μ_prob := _root_.MIPStarRE.QPBT.directLdQuestionDistribution_isProbability D
  decide := _root_.MIPStarRE.QPBT.directLdWinPredicate D

/-- The canonical point question associated with a geometric point. -/
def directLdPointQuestionOf (D : _root_.MIPStarRE.QPBT.DirectLdParams)
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) : _root_.MIPStarRE.QPBT.DirectLdQuestion D :=
  (.point, ⟨u, D.firstIndex, 0⟩)

/-- Total point-answer relabeling used in the direct soundness conclusion.
Wrong-form answers are folded into the zero tuple, exactly as for
`ldPointValuesOrZero`. -/
def directLdPointValuesOrZero (D : _root_.MIPStarRE.QPBT.DirectLdParams) :
    _root_.MIPStarRE.QPBT.DirectLdAnswer D → Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D
  | .pointVals values => values
  | .alinePolys _ => 0
  | .dlinePolys _ => 0

/-- A simultaneous tuple of bounded polynomials for the directly indexed
game. -/
noncomputable abbrev DirectPolyTuple (D : _root_.MIPStarRE.QPBT.DirectLdParams) :=
  Fin D.k → _root_.MIPStarRE.QPBT.PolyIndex D.m (_root_.MIPStarRE.QPBT.DirectScalarQ D) D.d

/-- A polynomial-tuple POVM for the directly indexed game. -/
noncomputable abbrev DirectPolyMeasTuple (D : _root_.MIPStarRE.QPBT.DirectLdParams) (ι : Type*)
    [Fintype ι] [DecidableEq ι] :=
  _root_.LIDT.MIPStarRE.Quantum.Measurement (_root_.MIPStarRE.QPBT.DirectPolyTuple D) ι

/-- Evaluate every component of a direct polynomial tuple at a point. -/
def evalDirectPolyTupleAt {D : _root_.MIPStarRE.QPBT.DirectLdParams}
    (u : Fin D.m → _root_.MIPStarRE.QPBT.DirectScalarQ D) (g : _root_.MIPStarRE.QPBT.DirectPolyTuple D) :
    Fin D.k → _root_.MIPStarRE.QPBT.DirectScalarQ D :=
  fun j => MvPolynomial.eval u (g j).1

end

end MIPStarRE.QPBT
