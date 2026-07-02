/-
Copyright (c) 2026 Dhruv Gupta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dhruv Gupta
-/
import NN.MLTheory.SelfSupervised.JEPA
import NN.MLTheory.SelfSupervised.PredictiveView
import ZPM.Probability.FintypePMF.TransferPrinciple
import Batteries.Tactic.Alias

/-!
# Matched-invariance draft: Appendix-B wrapper theorems

The five citation-stable names the draft's Appendix B requests, as aliases of the existing
verified declarations (mechanical by construction; the content lives upstream). Each alias
carries the exact type of its source.
-/

namespace WMSpec

open NN.MLTheory.SelfSupervised ProbabilityTheory.FintypePMF

/-- Draft Appendix B: JEPA is invariant to target-index order (= `jepaLoss_reverse`). -/
alias jepa_target_order_symmetry := NN.MLTheory.SelfSupervised.jepaLoss_reverse

/-- Draft Appendix B: JEPA is additive over mask concatenation (= `jepaLoss_append`). -/
alias jepa_two_component_mask_decomposition := NN.MLTheory.SelfSupervised.jepaLoss_append

/-- Draft Appendix B: structure outside the selected targets is invisible to the JEPA loss
(= `jepaLoss_target_ext`, the invisibility theorem). -/
alias jepa_unselected_target_structure_invisible := NN.MLTheory.SelfSupervised.jepaLoss_target_ext

/-- Draft Appendix B: JEPA is the zero-geometry predictive-view objective
(= `jepa_is_predictive_view_objective`). -/
alias jepa_is_zero_geometry_predictive_view :=
  NN.MLTheory.SelfSupervised.jepa_is_predictive_view_objective

/-- Draft Appendix B: the finite Boolean OOD gap is controlled by TV
(= `expectation_approx_of_tv`; see `WMSpec.finite_fisherRao_risk_bound` for the Fisher–Rao
form at the tight constant). -/
alias finite_bool_ood_gap_of_tv := ProbabilityTheory.FintypePMF.expectation_approx_of_tv

end WMSpec
