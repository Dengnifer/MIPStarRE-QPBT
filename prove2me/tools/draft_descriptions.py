#!/usr/bin/env python3
"""Draft description-only metadata for the LIDT and QPBT uploads.

This tool is intentionally offline. It reads the generated upload artifacts and
persisted IDs, writes review JSON under ~/p2m/status, and never contacts the
Prove2Me API.
"""

from __future__ import annotations

import argparse
import json
import re
from collections import defaultdict
from pathlib import Path
from typing import Any


HOME = Path.home()
P2M = HOME / "p2m"
ROOT = Path(__file__).resolve().parents[2]
LIDT_ROOT = P2M / "MIPStarRE"
STATUS = P2M / "status"

LIDT_NAMES = STATUS / "lidt-desc-part2.txt"
LIDT_PAYLOADS = LIDT_ROOT / "prove2me/generated/payloads.json"
LIDT_PLAN = LIDT_ROOT / "prove2me/generated/upload_plan.json"
LIDT_STATE = LIDT_ROOT / "prove2me/records/upload_state.json"
LIDT_OUTPUT = STATUS / "lidt-desc-part2.json"

QPBT_PAYLOADS = ROOT / "prove2me/generated/payloads.json"
QPBT_PLAN = ROOT / "prove2me/generated/upload_plan.json"
QPBT_STATE = ROOT / "prove2me/records/upload_state.json"
QPBT_OUTPUT = STATUS / "qpbt-bundle-desc.json"

FORBIDDEN = (
    "the proposition stated by this",
    "importable step in the formal dependency graph",
    "private",
)

HEADLINE_OVERRIDES = {
    "LIDT.MIPStarRE.LDT.Pasting.fromHToG_headTail_adjoint_qSDDCore_bound": (
        "**The adjoint head-tail commutator is bounded by the half-sandwich "
        "commutation error.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.fromHToG_incompletePart_average_total_eq": (
        "**The average incomplete-part mass is the complement of the averaged "
        "complete mass.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.fromHToG_ofGHatFactsAndHalfSandwich": (
        "**The $\\widehat G$ structural facts and half-sandwich commutation imply "
        "the transfer from $H$ to $G$.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gBotSelfConsistency_ofCompleteSelfConsistency": (
        "**Self-consistency of the complete component implies self-consistency "
        "of its complement.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatFacts": (
        "**The completed measurement $\\widehat G$ satisfies the required "
        "self-consistency and commutation facts.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatFacts_ofComMainAndSelfConsistency": (
        "**The main commutation estimate and self-consistency establish the "
        "$\\widehat G$ structural facts.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatFacts_ofSelfConsistencyAndCommutation": (
        "**Complete and complementary self-consistency together with commutation "
        "establish the $\\widehat G$ structural facts.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatHalfProduct_sum_adjoint_mul_le_one": (
        "**The half-product outcome operators for $\\widehat G$ are subnormalized.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatPairPrefix_sum_adjoint_mul_le_one": (
        "**The two-point prefix products for $\\widehat G$ are subnormalized.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatPairProduct_sddOpRel_triple": (
        "**The left and right pair-product families for $\\widehat G$ satisfy "
        "the required square-distance relation.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.gHatReverseHalfProduct_sum_adjoint_mul_le_one": (
        "**The reverse half-product outcome operators for $\\widehat G$ are "
        "subnormalized.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hAConsistency_error_le_nu_of_pos": (
        "**The endpoint consistency error is absorbed by the induction "
        "parameter $\\nu$.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hAConsistency_sqrt_bound_of_pos": (
        "**The square-root endpoint error satisfies the required power-law bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hAConsistency_submeas": (
        "**The constructed polynomial submeasurement is point-consistent with "
        "the strategy.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass_le_linePointDefectSum": (
        "**The $H_B$ bad mass is bounded by the sum of the line-point "
        "consistency defects.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass_le_one": (
        "**The $H_B$ bad mass is at most one.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hBConsistencyBadMass_nonneg": (
        "**The $H_B$ bad mass is nonnegative.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hBConsistencyCoordMass_le_linePointDefect": (
        "**Each coordinate mismatch mass is bounded by its line-point "
        "consistency defect.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.hBConsistency_fixed_u_defect_le_avgOver_distinct": (
        "**At a fixed point, the pasted consistency defect is bounded by its "
        "average over distinct tuples.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.interpolateCompletedSlicesFromSupport_restrictAtHeight_poly_eq_get_of_mem": (
        "**Interpolation from supported completed slices recovers every "
        "supported slice polynomial.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.interpolateCompletedSlices_restrictAtHeight_eq_get_of_mem_supportSubset": (
        "**Restricting the completed-slice interpolant recovers each eligible "
        "supported slice.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.interpolationEligibleSandwich_exists_mismatch_sum_le_sum": (
        "**The mass of any interpolation mismatch is bounded by the sum of the "
        "coordinate mismatch masses.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.interpolationSupportSubset_subset": (
        "**The eligible interpolation support is contained in the tuple support.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldDnoteq": (
        "**Conditioning a uniform point tuple to have distinct entries changes "
        "its law by at most $k^2/q$ in total variation.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldGbcon_of_axis_self": (
        "**Axis-parallel and self-consistency imply point-to-vertical-line "
        "consistency.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldPasting": (
        "**Low-degree pasting produces a projective polynomial measurement with "
        "the required consistency and completeness bounds.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldPastingNCompleteness_ofComMain_of_axis_self": (
        "**The main commutation theorem and axis consistency imply pasted "
        "measurement completeness.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldPastingNCompleteness_of_overAllOutcomes_fromHToG_tail": (
        "**The all-outcomes estimate and the $H$-to-$G$ tail bound imply pasted "
        "measurement completeness.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldPastingNCompleteness_of_tailLowerBound": (
        "**The Bernoulli-tail lower bound implies pasted measurement completeness.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldPastingNontrivial": (
        "**In the nontrivial regime, the constructed pasted measurement satisfies "
        "the low-degree pasting conclusion.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_zero_eq_endpoint": (
        "**The first left sandwich family is the endpoint evaluation "
        "submeasurement.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointLeftFamily_zero_outcome_some_eq_endpoint": (
        "**A present outcome of the first left sandwich family equals the "
        "endpoint evaluation outcome.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_error_le": (
        "**The endpoint consistency contribution is bounded by the one-point "
        "sandwich error.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_lift_of_axis_self": (
        "**Axis and self consistency control the lifted one-point sandwich "
        "endpoint.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_ldGbcon_of_axis_self": (
        "**Axis and self consistency control the one-point sandwich endpoint.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_endpoint_sqrt_bound": (
        "**The one-point sandwich endpoint square-root term satisfies its "
        "power-law bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePointPrefixMoved_eq_endpoint": (
        "**Moving the selected coordinate to the prefix identifies the family "
        "with endpoint evaluation.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_matchMass_lower_bound": (
        "**The original-prefix consistency error is bounded by the one-point "
        "sandwich error.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_cauchySchwarz_transport": (
        "**Moving the selected prefix changes the consistency error by at most "
        "twice the square root of the commutation error.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_linearDefect_average_cauchySchwarz_bound": (
        "**The averaged linear consistency defect is stable under prefix "
        "transport up to the commutation error.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.ldSandwichLineOnePoint_prefix_outcomeSum_cauchySchwarz_bound": (
        "**The averaged outcome mismatch mass is stable under prefix transport "
        "up to the commutation error.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.pastedInterpolation_verticalLine_defect_le_badMass": (
        "**The vertical-line defect of a pasted interpolant is bounded by its "
        "bad mass.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.postprocess_hRestrictionToVerticalLine_eq_evaluateAt": (
        "**Evaluating a vertical-line restriction recovers direct point "
        "evaluation.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes": (
        "**The all-outcomes estimate controls the global mass of incompatible "
        "completed tuples.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes_ofGHatFacts_of_axis_self": (
        "**The $\\widehat G$ structural facts and axis consistency imply the "
        "all-outcomes estimate.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.overAllOutcomes_ofLinePointBounds": (
        "**The line-point sandwich bounds imply the all-outcomes estimate.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.pointVerticalLineSdd_of_axis_self": (
        "**Axis-parallel and self-consistency bound the point-to-vertical-line "
        "state-dependent distance.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.qBipartiteConsDefect_eq_sum_singleOutcome": (
        "**The bipartite consistency defect decomposes over individual outcomes.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.qSDD_completePart_le_slice": (
        "**Discarding the incomplete outcome cannot increase the slice's quantum "
        "state-dependent distance.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.restrictToVerticalLine_eval_eq_restrictAtHeight_eval": (
        "**Vertical-line restriction agrees with restriction at the specified "
        "height.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.sddOpRel_uniform_equiv": (
        "**Uniform square-distance relations are invariant under reindexing by "
        "an equivalence.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.switcherooAggregateThirdTerm_eq_fourthTerm": (
        "**The third and fourth aggregate switcheroo terms coincide.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.tupleInterpolatedVerticalLine_ne_gives_exists_some_eval_mismatch": (
        "**A vertical-line interpolation mismatch is witnessed at a present "
        "tuple coordinate.**"
    ),
    "LIDT.MIPStarRE.LDT.Pasting.truncatedTypeSumRecurrence": (
        "**Truncated type sums are positive contractions satisfying the binary "
        "prefix recurrence.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.otherTwoNotionsOfSelfConsistency": (
        "**The alternative self-consistency conditions imply consistency of a "
        "measurement with itself.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.approxToSimeq_heterogeneous": (
        "**For projective measurements, state-dependent distance implies "
        "heterogeneous consistency.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.consSubMeas": (
        "**Consistency of indexed submeasurements is equivalent to the expanded "
        "consistency statement.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.fourier_fact_scalar": (
        "**A finite-field additive character averages to one at zero and to zero "
        "elsewhere.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.fourier_fact_vector": (
        "**A finite-field vector character averages to one at the zero vector and "
        "to zero elsewhere.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.simeqToApprox_heterogeneous": (
        "**Heterogeneous consistency bounds the state-dependent distance between "
        "the left and right placements.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.simeqTriangleInequality_heterogeneous": (
        "**Heterogeneous consistency satisfies a triangle inequality through an "
        "intermediate measurement.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_left_gap": (
        "**Switching the final sandwich operator from left to right costs at "
        "most the square root of the measurement distance.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.question_switchSandwich_middle_gap": (
        "**Removing the duplicated left sandwich factor costs at most the "
        "square root of the measurement distance.**"
    ),
    "LIDT.MIPStarRE.LDT.Preliminaries.triangleSub_right": (
        "**Consistency transfers through the right side of a triangle with "
        "error $\\delta + \\sqrt{\\varepsilon}$.**"
    ),
    "LIDT.MIPStarRE.LDT.PureState.ev_eq_re_inner": (
        "**The expectation of an operator in a pure state is the real part of "
        "the corresponding vector inner product.**"
    ),
    "LIDT.MIPStarRE.LDT.PureState.toQuantumState_isNormalized": (
        "**Every pure state induces a normalized density-operator quantum state.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.cascadeSigma_tight_bound": (
        "**The cascade $\\sigma$ term satisfies its tight step-envelope bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound_general": (
        "**The first cascade error satisfies its general step-envelope bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.cascadeZeta1_bound_special": (
        "**The first cascade error satisfies its specialized step-envelope bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.cascadeZeta2_bound": (
        "**The second cascade error satisfies its step-envelope bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.cascadeZeta3_bound": (
        "**The third cascade error satisfies its step-envelope bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.cascadeZeta4_bound": (
        "**The fourth cascade error satisfies its step-envelope bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.errorCascade_le_mainFormalError": (
        "**Every term in the error cascade is absorbed by the final soundness "
        "error envelope.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.mainFormal": (
        "**A successful low individual-degree strategy admits consistent "
        "projective polynomial measurements for both provers.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.consRel_constPolynomialEvaluation_heterogeneous": (
        "**Consistency of polynomial measurements transfers to their pointwise "
        "evaluation families.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.mdq_le_k2m4_stepEnvelope2048": (
        "**The $m d/q$ term is absorbed by the $k^2m^4$ step envelope.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.rpow_Z1_factor_le": (
        "**The real power of the first error factor obeys its linearized bound.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.projectiveEvaluationConsistency_ofFullPolynomialConsistency_heterogeneous": (
        "**Full consistency of two projective polynomial measurements implies "
        "consistency of their point evaluations.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.sqrt_rpow_one_div": (
        "**The square root of an inverse real power halves its exponent.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.sqrt_scaled_stepEnvelope_le": (
        "**A scaled step envelope remains controlled after taking a square root.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.sqrt_stepEnvelope_le": (
        "**Taking a square root doubles the step-envelope parameters.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.sigma_bound": (
        "**The cascade $\\sigma$ term is absorbed by the final error envelope.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_eighth_le": (
        "**The eighth root of the base step envelope is bounded by the scaled "
        "step envelope.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.stepEnvelope_rpow_quarter_le": (
        "**The fourth root of the base step envelope is bounded by the scaled "
        "step envelope.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.zeta1_bound": (
        "**The first cascade error is absorbed by the final soundness error.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.zeta2_bound": (
        "**The second cascade error is absorbed by the final soundness error.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.zeta3_bound": (
        "**The third cascade error is at most twice the final soundness error.**"
    ),
    "LIDT.MIPStarRE.LDT.Test.zeta4_bound": (
        "**The fourth cascade error is absorbed by the final soundness error.**"
    ),
    "LIDT.MIPStarRE.Quantum.Submeasurement.total_le_one": (
        "**The total operator of a submeasurement is bounded above by the identity.**"
    ),
}

GLOSS_OVERRIDES = {
    "MIPStarRE.QPBT.combinedPointExp_apply": (
        "The point-coordinate exponent is the combined monomial exponent at "
        "the injected point variable."
    ),
    "MIPStarRE.QPBT.combinedCoefExp_apply": (
        "The coefficient-coordinate exponent is the combined monomial exponent "
        "at the injected coefficient variable."
    ),
    "MIPStarRE.QPBT.combiningLinearForm_eval": (
        "Evaluating the combining linear form gives the dot product of its "
        "coefficient and argument vectors."
    ),
    "MIPStarRE.QPBT.DirectLdParams.combined_q": (
        "The combined low-degree parameters retain the original field size."
    ),
    "MIPStarRE.QPBT.DirectLdParams.combined_m": (
        "The combined low-degree dimension is the original dimension plus the "
        "number of coefficient coordinates."
    ),
    "MIPStarRE.QPBT.combinedPointVar_val": (
        "A point variable keeps its original coordinate in the combined index."
    ),
    "MIPStarRE.QPBT.combinedCoefficientVar_val": (
        "A coefficient variable is placed after the point coordinates in the "
        "combined index."
    ),
    "MIPStarRE.QPBT.directCombinedPointEquiv_apply": (
        "The direct combined-point equivalence concatenates the point and "
        "coefficient-coordinate vectors."
    ),
    "MIPStarRE.QPBT.combinedPoint_combinedPointVar": (
        "A combined point evaluated at an injected point variable returns the "
        "corresponding point coordinate."
    ),
    "MIPStarRE.QPBT.combinedPoint_combinedCoefficientVar": (
        "A combined point evaluated at an injected coefficient variable returns "
        "the corresponding coefficient."
    ),
    "MIPStarRE.QPBT.combinedRestrictSubstitution_point": (
        "The restriction substitution sends a point variable to the constant "
        "polynomial at that point coordinate."
    ),
    "MIPStarRE.QPBT.combinedRestrictSubstitution_coefficient": (
        "The restriction substitution sends a coefficient variable to its "
        "corresponding polynomial indeterminate."
    ),
    "MIPStarRE.QPBT.directPolyEquivPolynomial_poly": (
        "The direct polynomial equivalence renames the source polynomial's "
        "variables by finite-index reversal."
    ),
    "MIPStarRE.QPBT.directLdSpacePointTranslateEquiv_apply": (
        "The point-translation equivalence shifts the sampled point along its "
        "selected direction and preserves the index and direction."
    ),
    "MIPStarRE.QPBT.directLdSpacePointTranslateEquiv_symm_apply": (
        "The inverse point-translation equivalence applies the opposite shift "
        "and preserves the index and direction."
    ),
    "MIPStarRE.QPBT.matrixMeasurementTransport_effect": (
        "Transporting a matrix measurement relabels each effect through the "
        "inverse outcome equivalence."
    ),
    "MIPStarRE.QPBT.blockDiagonalMeasurement_effect": (
        "Each effect of the assembled measurement is the block-diagonal matrix "
        "of the corresponding component effects."
    ),
    "MIPStarRE.QPBT.matrixMeasurementToLDTProjMeas_outcome": (
        "Converting a projective matrix measurement to an LDT projective "
        "measurement preserves each outcome operator."
    ),
    "MIPStarRE.QPBT.ExtendedLineGame.map_mem_polyFunc": (
        "Mapping polynomial coefficients through a semiring homomorphism "
        "preserves coordinatewise degree bounds."
    ),
    "MIPStarRE.QPBT.ExtendedLineGame.piCongrLeft_const_apply": (
        "Reindexing a constant-codomain function along an equivalence evaluates "
        "the original function at the inverse image."
    ),
    "MIPStarRE.QPBT.reindexLinearMap_apply": (
        "The reindexed linear map extends the original map from the embedded "
        "coordinates and is zero elsewhere."
    ),
    "MIPStarRE.QPBT.DistanceCalculus.pureStateEuclideanVector_apply": (
        "The Euclidean-space representative of a pure state has the same "
        "coordinates as its state vector."
    ),
    "MIPStarRE.Quantum.Measurement.compressAt_effect": (
        "Compressing a measurement at a fixed ancillary coordinate takes the "
        "corresponding principal submatrix of every effect."
    ),
    "MIPStarRE.QPBT.idealPauliMeasurement": (
        "The ideal projective Pauli measurement formed from the Pauli spectral "
        "projections."
    ),
}

GREEK = {
    "α": r"\alpha", "β": r"\beta", "γ": r"\gamma", "δ": r"\delta",
    "ε": r"\varepsilon", "ζ": r"\zeta", "η": r"\eta", "θ": r"\theta",
    "ι": r"\iota", "κ": r"\kappa", "λ": r"\lambda", "μ": r"\mu",
    "ν": r"\nu", "ξ": r"\xi", "π": r"\pi", "ρ": r"\rho",
    "σ": r"\sigma", "τ": r"\tau", "φ": r"\varphi", "χ": r"\chi",
    "ψ": r"\psi", "ω": r"\omega", "Γ": r"\Gamma", "Δ": r"\Delta",
    "Σ": r"\Sigma", "Ψ": r"\Psi",
}

SUBSCRIPTS = str.maketrans("₀₁₂₃₄₅₆₇₈₉", "0123456789")


def load(path: Path) -> Any:
    return json.loads(path.read_text(encoding="utf-8"))


def write_json(path: Path, data: Any) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(
        json.dumps(data, ensure_ascii=False, indent=2, sort_keys=True) + "\n",
        encoding="utf-8",
    )


def split_top_level(text: str, marker: str) -> list[str]:
    parts: list[str] = []
    stack: list[str] = []
    quote = False
    start = 0
    pairs = {"(": ")", "[": "]", "{": "}"}
    for i, char in enumerate(text):
        if char == '"' and (i == 0 or text[i - 1] != "\\"):
            quote = not quote
        if quote:
            continue
        if char in pairs:
            stack.append(pairs[char])
        elif stack and char == stack[-1]:
            stack.pop()
        if not stack and text.startswith(marker, i):
            parts.append(text[start:i].strip())
            start = i + len(marker)
    parts.append(text[start:].strip())
    return parts


def split_once_top_level(text: str, marker: str) -> tuple[str, str] | None:
    parts = split_top_level(text, marker)
    if len(parts) < 2:
        return None
    return parts[0], marker.join(parts[1:]).strip()


def take_balanced(text: str, start: int) -> tuple[str, int]:
    pairs = {"(": ")", "[": "]", "{": "}"}
    opening = text[start]
    closing = pairs[opening]
    depth = 1
    quote = False
    i = start + 1
    while i < len(text):
        char = text[i]
        if char == '"' and text[i - 1] != "\\":
            quote = not quote
        elif not quote:
            if char == opening:
                depth += 1
            elif char == closing:
                depth -= 1
                if depth == 0:
                    return text[start + 1:i], i + 1
        i += 1
    raise ValueError(f"unbalanced binder starting at {start}: {text[start:start+80]}")


def parse_formal(formal: str) -> tuple[list[tuple[str, str]], str]:
    statement = formal.rsplit(":= by sorry", 1)[0].strip()
    match = re.match(r"(?:theorem|lemma)\s+\S+", statement)
    if not match:
        raise ValueError(f"unexpected formal statement: {formal[:120]}")
    i = match.end()
    binders: list[tuple[str, str]] = []
    while True:
        while i < len(statement) and statement[i].isspace():
            i += 1
        if i < len(statement) and statement[i] in "([{":
            opening = statement[i]
            content, i = take_balanced(statement, i)
            binders.append((opening, content.strip()))
            continue
        break
    if i >= len(statement) or statement[i] != ":":
        raise ValueError(f"missing conclusion separator: {formal[:160]}")
    conclusion = statement[i + 1:].strip()
    while conclusion.startswith("∀"):
        rest = conclusion[1:].lstrip()
        quantified: list[tuple[str, str]] = []
        while rest and rest[0] in "({":
            opening = rest[0]
            content, end = take_balanced(rest, 0)
            quantified.append((opening, content.strip()))
            rest = rest[end:].lstrip()
        if not rest.startswith(","):
            break
        binders.extend(quantified)
        conclusion = rest[1:].strip()
    return binders, conclusion


def strip_prefixes(text: str) -> str:
    replacements = (
        "_root_.LIDT.MIPStarRE.LDT.",
        "_root_.LIDT.MIPStarRE.Quantum.",
        "_root_.LIDT.PMF.",
        "LIDT.MIPStarRE.LDT.",
        "LIDT.MIPStarRE.Quantum.",
        "LIDT.PMF.",
        "_root_.",
    )
    for prefix in replacements:
        text = text.replace(prefix, "")
    return text


def short_type(type_text: str) -> str:
    text = strip_prefixes(type_text)
    text = re.sub(r"\s+", " ", text).strip()
    text = text.replace("(ι × ι)", "ι × ι")
    return text


def split_names_type(content: str) -> tuple[list[str], str] | None:
    pieces = split_once_top_level(content, ":")
    if pieces is None:
        return None
    names = pieces[0].split()
    if not names:
        return None
    return names, pieces[1]


def english_type(names: list[str], type_text: str) -> str:
    names_md = ", ".join(f"`{name}`" for name in names)
    short = short_type(type_text)
    plural = len(names) > 1
    if short == "Type*":
        return f"Let {names_md} be {'types' if plural else 'a type'}."
    if short == "ℕ":
        return f"Let {names_md} be {'natural numbers' if plural else 'a natural number'}."
    if short == "Error" or short.endswith(".Error"):
        return f"Let {names_md} be {'real error parameters' if plural else 'a real error parameter'}."
    if short.startswith("Parameters"):
        return f"Fix the LDT parameter record {names_md}."
    if "QuantumState" in short:
        qualifier = "bipartite " if "×" in short else ""
        return f"Let {names_md} be {'quantum states' if plural else f'a {qualifier}quantum state'} of type `{short}`."
    if "SymStrat" in short:
        return f"Let {names_md} be {'symmetric strategies' if plural else 'a symmetric strategy'} of type `{short}`."
    if "ProjStrat" in short:
        return f"Let {names_md} be {'projective strategies' if plural else 'a projective strategy'} of type `{short}`."
    if "IdxPolyFamily" in short:
        return f"Let {names_md} be {'indexed polynomial-measurement families' if plural else 'an indexed polynomial-measurement family'} of type `{short}`."
    if "Distribution" in short:
        return f"Let {names_md} be {'distributions' if plural else 'a distribution'} of type `{short}`."
    if "PointTuple" in short:
        return f"Let {names_md} be {'point tuples' if plural else 'a point tuple'} of type `{short}`."
    if re.search(r"(?:^|\.)Point(?:\s|$)", short):
        return f"Let {names_md} be {'finite-field points' if plural else 'a finite-field point'} of type `{short}`."
    if "Fq" in short:
        return f"Let {names_md} be {'finite-field elements' if plural else 'a finite-field element'} of type `{short}`."
    if "Measurement" in short or "Meas" in short:
        return f"Let {names_md} be {'measurement objects' if plural else 'a measurement object'} of type `{short}`."
    if "Op " in short or short.startswith("Op"):
        return f"Let {names_md} be {'operators' if plural else 'an operator'} of type `{short}`."
    if short.startswith("Finset"):
        return f"Let {names_md} be {'finite sets' if plural else 'a finite set'} of type `{short}`."
    if short == "Bool":
        return f"Let {names_md} be {'Boolean values' if plural else 'a Boolean value'}."
    return f"Let {names_md} be {'objects' if plural else 'an object'} of type `{short}`."


def class_prose(content: str) -> str:
    short = short_type(content)
    if short.startswith("FieldModel"):
        return f"Assume the finite-field model `{short}`."
    if short.startswith("Fintype "):
        return f"Assume `{short.removeprefix('Fintype ')}` is finite."
    if short.startswith("Nonempty "):
        return f"Assume `{short.removeprefix('Nonempty ')}` is nonempty."
    if short.startswith("DecidableEq "):
        return f"Assume decidable equality on `{short.removeprefix('DecidableEq ')}`."
    return f"Assume the typeclass condition `{short}`."


def escape_identifier(name: str) -> str:
    result = []
    subscript = []
    for char in name:
        if char in GREEK:
            if subscript:
                result.append("_{" + "".join(subscript) + "}")
                subscript.clear()
            result.append("{" + GREEK[char] + "}")
        elif char in "₀₁₂₃₄₅₆₇₈₉":
            subscript.append(char.translate(SUBSCRIPTS))
        elif char == "_":
            if subscript:
                result.append("_{" + "".join(subscript) + "}")
                subscript.clear()
            result.append(r"\_")
        elif char == "'":
            if subscript:
                result.append("_{" + "".join(subscript) + "}")
                subscript.clear()
            result.append("^{\\prime}")
        elif char.isalnum():
            if subscript:
                result.append("_{" + "".join(subscript) + "}")
                subscript.clear()
            result.append(char)
        else:
            if subscript:
                result.append("_{" + "".join(subscript) + "}")
                subscript.clear()
            result.append(char)
    if subscript:
        result.append("_{" + "".join(subscript) + "}")
    return "".join(result)


TOKEN_RE = re.compile(
    r"(?:_root_\.)?[\w𝒜-𝓏ℕℝℂ]+(?:\.[\w𝒜-𝓏ℕℝℂ]+)*"
    r"|\d+(?:\.\d+)?|:=|=>|≤|≥|≠|→|↔|∧|∨|∈|∉|⊆|∑|∏|∀|∃|ᴴ|⁻¹|×|•|¬|≃|∪"
    r"|[(){}\[\]⟨⟩,.:;+*/^<>=|-]"
)


def render_variable(name: str) -> str:
    aliases = {
        "eps": r"\varepsilon", "delta": r"\delta", "gamma": r"\gamma",
        "zeta": r"\zeta", "kappa": r"\kappa", "psi": r"\psi",
    }
    if name in aliases:
        return aliases[name]
    if name == "𝒟":
        return r"\mathcal D"
    if name.startswith("𝒟"):
        suffix = name[1:]
        return r"\mathcal D" + (r"_{\mathrm{" + suffix + "}}" if suffix else "")
    if name and name[0] in GREEK:
        base = GREEK[name[0]]
        suffix = name[1:]
        if suffix:
            if all(char in "₀₁₂₃₄₅₆₇₈₉" for char in suffix):
                return base + "_{" + suffix.translate(SUBSCRIPTS) + "}"
            return base + r"_{\mathrm{" + escape_identifier(suffix) + "}}"
        return base
    match = re.fullmatch(r"([A-Za-z]+)_([A-Za-z0-9]+)", name)
    if match:
        return r"\mathit{" + match.group(1) + "}_{\\mathrm{" + match.group(2) + "}}"
    return r"\mathit{" + escape_identifier(name) + "}"


def render_dotted(token: str, variables: set[str]) -> str:
    parts = token.split(".")
    if len(parts) == 1:
        return render_variable(token)
    first = parts[0]
    if first in variables or first[:1].islower() or first[:1] in GREEK or first.startswith("𝒟"):
        rendered = render_variable(first)
        for projection in parts[1:]:
            if projection.isdigit():
                rendered += "." + projection
            else:
                rendered += r".\mathsf{" + escape_identifier(projection) + "}"
        return rendered
    return r"\mathsf{" + escape_identifier(parts[-1]) + "}"


def latex_expr(expression: str, variables: set[str]) -> str:
    text = strip_prefixes(expression)
    text = text.replace("⬝ᵥ", " vecInner ").replace("*ᵥ", " matVecMul ")
    text = text.replace("@", "")
    text = re.sub(
        r"\(\s*[\w𝒜-𝓏₀-₉]+\s*:=\s*[\w𝒜-𝓏₀-₉.]+\s*\)",
        "",
        text,
    )
    local_variables = set(variables)
    local_variables.update(re.findall(r"\bfun\s+([\w𝒜-𝓏]+)", text))
    local_variables.update(re.findall(r"∑\s+([\w𝒜-𝓏]+)", text))
    local_variables.update(re.findall(r"∏\s+([\w𝒜-𝓏]+)", text))
    local_variables.update(re.findall(r"∃\s+([\w𝒜-𝓏]+)\s*:", text))
    tokens = TOKEN_RE.findall(text)
    output: list[str] = []
    operator = {
        "≤": r"\le", "≥": r"\ge", "≠": r"\ne", "→": r"\Longrightarrow",
        "↔": r"\Longleftrightarrow", "∧": r"\land", "∨": r"\lor",
        "∈": r"\in", "∉": r"\notin", "⊆": r"\subseteq", "∑": r"\sum",
        "∏": r"\prod", "∀": r"\forall", "∃": r"\exists", "×": r"\times",
        "•": r"\mathbin{\bullet}", "¬": r"\neg", "≃": r"\simeq", "∪": r"\cup",
        "ᴴ": r"^{\dagger}", "⁻¹": r"^{-1}", "*": r"\,",
        ":=": "=", "=>": r"\mapsto", "|": r"\mid",
    }
    keyword = {
        "fun": r"\lambda", "let": r"\text{let}", "in": r"\text{in}",
        "if": r"\text{if}", "then": r"\text{then}", "else": r"\text{else}",
        "with": r"\text{with}", "true": r"\mathrm{true}", "false": r"\mathrm{false}",
        "by": r"\text{by}", "open": r"\text{open}",
    }
    constants = {
        "ℕ": r"\mathbb N", "ℝ": r"\mathbb R", "ℂ": r"\mathbb C",
        "Real.sqrt": r"\sqrt", "Real.rpow": r"\operatorname{rpow}",
        "Unit": r"\mathbf 1", "Finset.univ": r"\mathrm{univ}",
    }
    for token in tokens:
        if token in operator:
            rendered = operator[token]
        elif token in keyword:
            rendered = keyword[token]
        elif token in constants:
            rendered = constants[token]
        elif re.fullmatch(r"\d+(?:\.\d+)?", token):
            rendered = token
        elif token in "(){}[],:;+/-^<>=.":
            rendered = token
        else:
            short = token.split(".")[-1]
            if token in local_variables or short in local_variables:
                rendered = render_variable(short)
            elif "." in token:
                rendered = render_dotted(token, local_variables)
            elif len(short) == 1 and (short.isalpha() or short in GREEK):
                rendered = render_variable(short)
            else:
                rendered = r"\mathsf{" + escape_identifier(short) + "}"
        output.append(rendered)
    rendered = " ".join(output)
    rendered = re.sub(r"\s+([,.:;\)\}\]])", r"\1", rendered)
    rendered = re.sub(r"([\(\{\[])\s+", r"\1", rendered)
    rendered = rendered.replace(". \\mathsf", ".\\mathsf")
    rendered = rendered.replace("^ {", "^{").replace("_ {", "_{")
    variable_pattern = r"(?:\\mathit\{[^{}]+\}|\\[A-Za-z]+(?:_\{[^{}]+\})?)"
    rendered = re.sub(
        rf"\\sum ({variable_pattern}) \\in (.+?) \\text\{{with\}} (.+?),",
        lambda match: (
            r"\sum_{\substack{" + match.group(1) + r" \in " + match.group(2)
            + r" \\ " + match.group(3) + "}}"
        ),
        rendered,
    )
    rendered = re.sub(
        rf"\\sum ({variable_pattern}) \\in (.+?),",
        lambda match: r"\sum_{" + match.group(1) + r" \in " + match.group(2) + "}",
        rendered,
    )
    rendered = re.sub(
        rf"\\sum ({variable_pattern}): (.+?),",
        lambda match: r"\sum_{" + match.group(1) + r" \in " + match.group(2) + "}",
        rendered,
    )
    rendered = re.sub(
        rf"\\prod ({variable_pattern}): (.+?),",
        lambda match: r"\prod_{" + match.group(1) + r" \in " + match.group(2) + "}",
        rendered,
    )
    rendered = re.sub(r"\(([^()]{1,100}): \\mathsf\{Error\}\)", r"\1", rendered)
    rendered = re.sub(r"\((\d+): \\mathbb N\)", r"\1", rendered)
    return rendered


def binder_paragraphs(binders: list[tuple[str, str]]) -> tuple[list[str], set[str]]:
    prose: list[str] = []
    variables: set[str] = set()
    for opening, content in binders:
        if opening == "[":
            prose.append(class_prose(content))
            continue
        parsed = split_names_type(content)
        if parsed is None:
            prose.append(f"Fix the quantified data `{short_type(content)}`.")
            continue
        names, type_text = parsed
        variables.update(names)
        if all(name.startswith("h") for name in names):
            formula = latex_expr(type_text, variables)
            prose.append(
                f"Assume {', '.join(f'`{name}`' for name in names)}, the condition ${formula}$."
            )
        else:
            prose.append(english_type(names, type_text))
    return prose, variables


def normalize_headline(text: str) -> str:
    headline = text.split("\n\n", 1)[0].strip()
    headline = re.sub(r"\s+", " ", headline)
    if headline.startswith("**"):
        return headline
    return f"**{headline}**"


def readable_phrase(text: str) -> str:
    replacements = {
        "ldSandwichLineOnePoint": "one-point low-degree sandwich",
        "qBipartiteConsDefect": "bipartite consistency defect",
        "hAConsistency": "$H_A$-consistency",
        "hBConsistency": "$H_B$-consistency",
        "sddOpRel": "operator square-distance relation",
        "avgOver": "average over",
        "gHat": "$\\widehat G$",
        "Zeta1": "$\\zeta_1$", "Zeta2": "$\\zeta_2$",
        "Zeta3": "$\\zeta_3$", "Zeta4": "$\\zeta_4$",
        "Sigma": "$\\sigma$", "Nu": "$\\nu$",
        "rpow": "real power",
        "nonneg": "nonnegative", "sqrt": "square root",
    }
    protected: dict[str, str] = {}
    for index, (old, new) in enumerate(replacements.items()):
        marker = f"\x00{index}\x00"
        if old in text:
            text = text.replace(old, marker)
            protected[marker] = new
    text = humanize(text).lower()
    for marker, replacement in protected.items():
        text = text.replace(marker, f" {replacement} ")
    text = re.sub(r"\bnu\b", r"$\\nu$", text)
    text = text.replace("coord mass", "coordinate mass")
    text = text.replace("of pos", "under positivity")
    text = re.sub(r"\s+", " ", text).strip()
    return text


def sentence_start(phrase: str) -> str:
    if not phrase:
        return phrase
    if phrase.startswith("$"):
        return "The " + phrase
    return phrase[0].upper() + phrase[1:]


def improve_generated_headline(name: str, headline: str) -> str:
    if name in HEADLINE_OVERRIDES:
        return HEADLINE_OVERRIDES[name]
    short = name.split(".")[-1]
    generated = humanize(short)
    plain = re.sub(r"\s+", " ", headline.strip("* ."))
    if plain.lower() != generated.lower():
        return headline
    if "_le_" in short:
        left, right = short.split("_le_", 1)
        return (
            f"**{sentence_start(readable_phrase(left))} is bounded above by "
            f"{readable_phrase(right)}.**"
        )
    if "_eq_" in short:
        left, right = short.split("_eq_", 1)
        return (
            f"**{sentence_start(readable_phrase(left))} equals "
            f"{readable_phrase(right)}.**"
        )
    if short.endswith("_nonneg"):
        return f"**Nonnegativity of {readable_phrase(short.removesuffix('_nonneg'))}.**"
    if short.endswith("_bound"):
        return f"**A quantitative bound for {readable_phrase(short.removesuffix('_bound'))}.**"
    return f"**{sentence_start(readable_phrase(short))}.**"


def preserved_tail(text: str) -> str:
    credit_at = text.index("Formalization credit:")
    return text[credit_at:].strip()


def humanize(name: str) -> str:
    name = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", name)
    return name.replace("_", " ").replace("  ", " ").strip()


def role_sentence(name: str, consumers: list[str], payload_by_name: dict[str, dict[str, Any]]) -> str:
    if consumers:
        selected = consumers[:2]
        labels = []
        for consumer in selected:
            headline = payload_by_name.get(consumer, {}).get("natural_language_statement", "")
            if headline:
                purpose = improve_generated_headline(
                    consumer, normalize_headline(headline),
                )
                purpose = re.sub(r"\s+", " ", purpose)
                purpose = purpose.replace("**", "").strip(" .")
                labels.append(f"`{consumer.split('.')[-1]}` ({purpose})")
            else:
                labels.append(f"`{consumer.split('.')[-1]}`")
        suffix = " and ".join(labels)
        remaining = len(consumers) - 2
        noun = "result" if remaining == 1 else "results"
        extra = "" if remaining <= 0 else f", together with {remaining} further downstream {noun}"
        return f"This result feeds {suffix}{extra}."
    short = name.split(".")[-1]
    if short == "mainFormal":
        return "This is the final formal low-individual-degree soundness theorem, collecting the projective polynomial measurements and their consistency estimates."
    headline = improve_generated_headline(
        name, normalize_headline(payload_by_name[name]["natural_language_statement"]),
    )
    headline = re.sub(r"\s+", " ", headline).strip("* .")
    return f"This standalone identity supplies the QPBT import boundary for the following LDT fact: {headline}."


def extract_leading_lets(conclusion: str) -> tuple[list[tuple[str, str, str]], str]:
    if not conclusion.startswith("let "):
        return [], conclusion
    lines = conclusion.splitlines()
    blocks: list[list[str]] = []
    tail: list[str] = []
    current: list[str] | None = None
    for line in lines:
        stripped = line.strip()
        if stripped.startswith("let "):
            if current is not None:
                blocks.append(current)
            current = [stripped]
        elif current is not None and not stripped.startswith("∃"):
            current.append(stripped)
        else:
            if current is not None:
                blocks.append(current)
                current = None
            tail.append(stripped)
    if current is not None:
        blocks.append(current)
    lets: list[tuple[str, str, str]] = []
    for block in blocks:
        joined = " ".join(block)
        match = re.match(r"let\s+(\S+)\s*:\s*(.*?)\s*:=\s*(.*)", joined)
        if not match:
            return [], conclusion
        lets.append((match.group(1), match.group(2), match.group(3)))
    body = " ".join(piece for piece in tail if piece).strip()
    if not body:
        return [], conclusion
    return lets, body


def leading_existentials(conclusion: str) -> list[tuple[str, str | None]]:
    witnesses: list[tuple[str, str | None]] = []
    rest = conclusion.strip()
    while rest.startswith("∃"):
        rest = rest[1:].lstrip()
        comma_parts = split_top_level(rest, ",")
        if len(comma_parts) < 2:
            break
        binder = comma_parts[0]
        rest = ",".join(comma_parts[1:]).strip()
        parsed = split_once_top_level(binder, ":")
        if parsed is None:
            witnesses.append((binder.strip(), None))
        else:
            witnesses.append((parsed[0].strip(), short_type(parsed[1])))
    return witnesses


def theorem_description(
    name: str,
    payload: dict[str, Any],
    consumers: list[str],
    payload_by_name: dict[str, dict[str, Any]],
) -> str:
    binders, conclusion = parse_formal(payload["formal_statement"])
    binder_text, variables = binder_paragraphs(binders)
    lets, conclusion = extract_leading_lets(conclusion)
    for let_name, let_type, let_value in lets:
        variables.add(let_name)
        binder_text.append(
            f"Define `{let_name}` of type `{short_type(let_type)}` by "
            f"${latex_expr(let_value, variables)}$."
        )
    witnesses = leading_existentials(conclusion)
    if witnesses:
        descriptions = []
        for witness, witness_type in witnesses:
            if witness_type is None:
                descriptions.append(f"`{witness}` as a witness of the displayed property")
            else:
                descriptions.append(f"`{witness}` of type `{witness_type}`")
        binder_text.append(
            "The conclusion asserts the existence, in order, of "
            + ", then ".join(descriptions)
            + "."
        )
    implication_parts = split_top_level(conclusion, "→")
    premises = implication_parts[:-1]
    conclusion = implication_parts[-1]
    for index, premise in enumerate(premises, start=1):
        binder_text.append(
            f"Assume the additional premise $H_{{{index}}}$:\n\n"
            f"$$\n{latex_expr(premise, variables)}.\n$$"
        )
    formula = latex_expr(conclusion, variables)
    if any(command in formula for command in (r"\sum", r"\prod", r"\lambda")):
        binder_text.append(
            "Variables bound inside the displayed sums, products, or indexed families "
            "range over the finite domains shown in the formula."
        )
    context = " ".join(binder_text)
    headline = normalize_headline(payload["natural_language_statement"])
    headline = improve_generated_headline(name, headline)
    role = role_sentence(name, consumers, payload_by_name)
    tail = preserved_tail(payload["natural_language_statement"])
    return (
        f"{headline}\n\n"
        f"{context}\n\n"
        f"Under these hypotheses, the precise conclusion is\n\n"
        f"$$\n{formula}.\n$$\n\n"
        f"{role}\n\n"
        f"{tail}"
    )


def clean_docstring(raw: str) -> str:
    text = raw.strip()
    text = re.sub(r"^/--?", "", text)
    text = re.sub(r"-/$", "", text)
    text = re.sub(r"\*\*[^*]+:\*\*", "", text)
    text = re.sub(r"`([^`]+)`", r"\1", text)
    text = re.sub(r"\s+", " ", text).strip(" -\n")
    sentences = re.split(r"(?<=[.!?])\s+", text)
    gloss = sentences[0] if sentences and sentences[0] else text
    gloss = re.sub(r"^(The|A|An)\s+", lambda m: m.group(0), gloss)
    return gloss.rstrip(".") + "."


def fallback_gloss(anchor: str, classification: str) -> str:
    public_anchor = anchor
    if public_anchor.startswith("_private.") and ".MIPStarRE." in public_anchor:
        public_anchor = "MIPStarRE." + public_anchor.split(".MIPStarRE.", 1)[-1]
    if public_anchor in GLOSS_OVERRIDES:
        return GLOSS_OVERRIDES[public_anchor]
    short = anchor.split(".")[-1]
    phrase = humanize(short)
    if "Nonempty" in short:
        subject = humanize(short.replace("Nonempty", "")).strip()
        return f"A nonemptiness witness for {subject.lower()}."
    if "Fintype" in short:
        subject = humanize(short.replace("Fintype", "")).strip()
        return f"The finite enumeration structure on {subject.lower()}."
    if "DecidableEq" in short:
        subject = humanize(short.replace("DecidableEq", "")).strip()
        return f"Decidable equality for {subject.lower()}."
    if short.startswith("inst"):
        return f"The `{short}` typeclass instance supporting {phrase.removeprefix('inst ').lower()}."
    if classification == "def-embedded-theorem":
        for suffix, description in (
            ("_apply", "The evaluation formula for"),
            ("_effect", "The effect-operator formula for"),
            ("_outcome", "The outcome-operator formula for"),
            ("_eval", "The evaluation formula for"),
            ("_point", "The point-coordinate specialization of"),
            ("_coefficient", "The coefficient-coordinate specialization of"),
            ("_poly", "The polynomial-component identity for"),
            ("_val", "The underlying-index formula for"),
        ):
            if short.endswith(suffix):
                stem = short.removesuffix(suffix)
                return f"{description} `{stem}`."
        return f"The defining identity for `{short}`."
    return f"The `{short}` construction for {phrase.lower()}."


def command_gloss(command: dict[str, Any], source: bytes) -> str:
    doc = command.get("docstring")
    if not doc:
        return fallback_gloss(command["anchor"], command["classification"])
    start = doc["start"]["offset"]
    end = doc["end"]["offset"]
    gloss = clean_docstring(source[start:end].decode("utf-8"))
    gloss = re.sub(r"\bprivate\b", "internal", gloss, flags=re.IGNORECASE)
    if not gloss or len(gloss) < 12:
        return fallback_gloss(command["anchor"], command["classification"])
    if len(gloss) > 260:
        for separator in (":", ";"):
            head = gloss.split(separator, 1)[0].strip()
            if 30 <= len(head) <= 240:
                return head.rstrip(".") + "."
        return fallback_gloss(command["anchor"], command["classification"])
    return gloss


def select_principal(commands: list[dict[str, Any]]) -> list[dict[str, Any]]:
    def score(command: dict[str, Any]) -> tuple[int, int, int]:
        short = command["anchor"].split(".")[-1]
        private = command["anchor"].startswith("_private.")
        instance = short.startswith("inst") or "DecidableRel" in short
        embedded = command["classification"] == "def-embedded-theorem"
        return (private, instance, embedded)

    ordered = sorted(enumerate(commands), key=lambda item: (score(item[1]), item[0]))
    return [command for _, command in ordered[:8]]


def qpbt_bundle_description(
    payload: dict[str, Any], bundle: dict[str, Any], commands_by_id: dict[str, dict[str, Any]],
) -> str:
    source_path = ROOT / bundle["source"]
    source = source_path.read_bytes()
    commands = [commands_by_id[cid] for cid in bundle["commands"]]
    principals = select_principal(commands)
    entries = []
    for command in principals:
        anchor = command["anchor"]
        if anchor.startswith("_private."):
            anchor = anchor.split(".MIPStarRE.", 1)[-1]
            anchor = "MIPStarRE." + anchor
        entries.append(f"- `{anchor}`: {command_gloss(command, source)}")
    old = payload["natural_language_statement"]
    preserved_at = old.index("**Formalization Credit.**")
    preserved = old[preserved_at:].strip()
    count = len(commands)
    return (
        f"This definition bundle contains {count} source commands from `{bundle['module']}`.\n\n"
        f"Its principal declarations are:\n\n"
        + "\n".join(entries)
        + "\n\n"
        + preserved
    )


def build_lidt() -> dict[str, dict[str, str]]:
    names = [line for line in LIDT_NAMES.read_text(encoding="utf-8").splitlines() if line]
    payloads = load(LIDT_PAYLOADS)
    plan = load(LIDT_PLAN)
    state = load(LIDT_STATE)
    payload_by_name = {item["theorem_name"]: item for item in payloads["theorems"]}
    node_by_id = plan["nodes"]
    reverse: dict[str, list[str]] = defaultdict(list)
    for node in node_by_id.values():
        for dependency in node.get("theoremDependencies", []):
            dependency_name = node_by_id[dependency]["platformName"]
            reverse[dependency_name].append(node["platformName"])
    result: dict[str, dict[str, str]] = {}
    for name in names:
        entry = state["theorems"][name]
        result[name] = {
            "theorem_id": entry["theorem_id"],
            "natural_language_statement": theorem_description(
                name, payload_by_name[name], reverse[name], payload_by_name,
            ),
        }
    return result


def build_qpbt() -> dict[str, dict[str, str]]:
    payloads = load(QPBT_PAYLOADS)
    plan = load(QPBT_PLAN)
    state = load(QPBT_STATE)
    payload_by_name = {item["definition_name"]: item for item in payloads["definitions"]}
    result: dict[str, dict[str, str]] = {}
    for bundle_id in plan["definitionOrder"]:
        bundle = plan["definitions"][bundle_id]
        name = bundle["definitionName"]
        entry = state["definitions"][name]
        result[name] = {
            "definition_id": entry.get("definition_id") or entry["theorem_id"],
            "natural_language_statement": qpbt_bundle_description(
                payload_by_name[name], bundle, plan["commands"],
            ),
        }
    return result


def check_common(path: Path, data: dict[str, Any], expected: set[str]) -> list[str]:
    problems: list[str] = []
    if set(data) != expected:
        problems.append(
            f"key mismatch: missing={sorted(expected-set(data))[:5]} extra={sorted(set(data)-expected)[:5]}"
        )
    for name, item in data.items():
        text = item.get("natural_language_statement", "")
        lowered = text.lower()
        for phrase in FORBIDDEN:
            if phrase in lowered:
                problems.append(f"{name}: contains forbidden phrase {phrase!r}")
        if "—" in text:
            problems.append(f"{name}: contains em dash")
        if text.count("$") % 2:
            problems.append(f"{name}: unbalanced dollar delimiters")
        if not text.strip():
            problems.append(f"{name}: empty description")
    try:
        load(path)
    except Exception as error:  # pragma: no cover - command-line guard
        problems.append(f"JSON parse failed: {error}")
    return problems


def self_check() -> list[str]:
    lidt = load(LIDT_OUTPUT)
    qpbt = load(QPBT_OUTPUT)
    expected_lidt = set(filter(None, LIDT_NAMES.read_text(encoding="utf-8").splitlines()))
    expected_qpbt = {
        item["definition_name"] for item in load(QPBT_PAYLOADS)["definitions"]
    }
    problems = check_common(LIDT_OUTPUT, lidt, expected_lidt)
    problems.extend(check_common(QPBT_OUTPUT, qpbt, expected_qpbt))
    for name, item in lidt.items():
        if not item.get("theorem_id"):
            problems.append(f"{name}: missing theorem_id")
        text = item["natural_language_statement"]
        headline = text.split("\n\n", 1)[0]
        if not (headline.startswith("**") and headline.endswith("**")):
            problems.append(f"{name}: malformed bold headline")
        original = next(
            row["natural_language_statement"] for row in load(LIDT_PAYLOADS)["theorems"]
            if row["theorem_name"] == name
        )
        tail = preserved_tail(original)
        if not text.endswith(tail):
            problems.append(f"{name}: credit/formalization tail changed")
        if item["theorem_id"] != load(LIDT_STATE)["theorems"][name]["theorem_id"]:
            problems.append(f"{name}: theorem_id differs from upload state")
    qpbt_payload_by_name = {
        row["definition_name"]: row for row in load(QPBT_PAYLOADS)["definitions"]
    }
    qpbt_state = load(QPBT_STATE)["definitions"]
    for name, item in qpbt.items():
        if not item.get("definition_id"):
            problems.append(f"{name}: missing definition_id")
        expected_id = qpbt_state[name].get("definition_id") or qpbt_state[name]["theorem_id"]
        if item.get("definition_id") != expected_id:
            problems.append(f"{name}: definition_id differs from upload state")
        original = qpbt_payload_by_name[name]["natural_language_statement"]
        tail = original[original.index("**Formalization Credit.**"):].strip()
        if not item["natural_language_statement"].endswith(tail):
            problems.append(f"{name}: credit/source tail changed")
    return problems


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--check", action="store_true", help="check existing outputs only")
    args = parser.parse_args()
    if not args.check:
        write_json(LIDT_OUTPUT, build_lidt())
        write_json(QPBT_OUTPUT, build_qpbt())
    problems = self_check()
    result = {
        "lidtTheorems": len(load(LIDT_OUTPUT)),
        "qpbtDefinitions": len(load(QPBT_OUTPUT)),
        "problems": problems,
    }
    print(json.dumps(result, indent=2, sort_keys=True))
    return int(bool(problems))


if __name__ == "__main__":
    raise SystemExit(main())
