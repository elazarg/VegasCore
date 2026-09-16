/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.DecisionObservation

/-! # Observation erasure across two decisions

The second retained observation includes the first observation and the agent's
own first action. The transition to the second observation and the final
continuation are fixed independently of the response policies. Under their
factorization hypotheses, conditioning the two policies in order preserves the
outcome law, including any correlations retained by the final kernel.

This is a finite decision experiment, not a multi-player game simulation. In an
application, the fixed kernels must describe the same environment and unchanged
opponents for every deviation. The theorem does not establish that premise.
-/

noncomputable section

namespace GameTheory.Math.Probability.FinDist

variable {NativeInfo LogicalInfo FirstAction NativeNext LogicalNext SecondAction Outcome : Type*}

/-- Two successive information erasures compose when the intermediate law
factors through the first retained observation and action, and the final law
factors through the retained history and second action. Native policies may
use all of their observations and remember their own first action.

The factorization assumptions concern the fixed transition kernels, not
constancy of the policies on observation fibers. The returned second policy
may depend on the first policy through the induced history law. -/
theorem exists_two_decision_policy_law
    (initial : FinDist NativeInfo) (observe : NativeInfo → LogicalInfo)
    (observeNext : NativeNext → LogicalNext)
    (next : NativeInfo → FirstAction → FinDist NativeNext)
    (logicalNext : LogicalInfo → FirstAction → FinDist LogicalNext)
    (hnext : ∀ info ∈ initial.support, ∀ action,
      (next info action).map observeNext = logicalNext (observe info) action)
    (finish : NativeInfo × FirstAction × NativeNext → SecondAction → FinDist Outcome)
    (logicalFinish : LogicalInfo × FirstAction × LogicalNext →
      SecondAction → FinDist Outcome)
    (hfinish : ∀ info ∈ initial.support, ∀ action,
      ∀ later ∈ (next info action).support, ∀ response,
        finish (info, action, later) response =
          logicalFinish (observe info, action, observeNext later) response)
    (first : NativeInfo → FinDist FirstAction)
    (second : NativeInfo × FirstAction × NativeNext → FinDist SecondAction) :
    ∃ logicalFirst : LogicalInfo → FinDist FirstAction,
      ∃ logicalSecond : LogicalInfo × FirstAction × LogicalNext → FinDist SecondAction,
        (initial.bind fun info => (first info).bind fun action =>
          (next info action).bind fun later =>
            (second (info, action, later)).bind (finish (info, action, later))) =
        ((initial.map observe).bind fun info => (logicalFirst info).bind fun action =>
          (logicalNext info action).bind fun later =>
            (logicalSecond (info, action, later)).bind
              (logicalFinish (info, action, later))) := by
  let histories := initial.bind fun info => (first info).bind fun action =>
    (next info action).map fun later => (info, action, later)
  let retain : NativeInfo × FirstAction × NativeNext →
      LogicalInfo × FirstAction × LogicalNext :=
    fun history => (observe history.1, history.2.1, observeNext history.2.2)
  let logicalFirst := initial.conditionedPolicy observe first
  let logicalSecond := histories.conditionedPolicy retain second
  have hhistories : histories.map retain =
      (initial.map observe).bind (fun info => (logicalFirst info).bind fun action =>
        (logicalNext info action).map fun later => (info, action, later)) := by
    calc
      histories.map retain = initial.bind (fun info => (first info).bind fun action =>
          (logicalNext (observe info) action).map fun later =>
            (observe info, action, later)) := by
        simp only [histories, map_bind]
        apply bind_congr
        intro info hinfo
        apply bind_congr
        intro action _
        rw [← hnext info hinfo action]
        simp only [map_comp, retain, Function.comp_def]
      _ = _ := initial.bind_policy_logicalKernel_eq_bind_conditionedPolicy observe first
        (fun info action => (logicalNext info action).map fun later => (info, action, later))
  have hfactor : ∀ history ∈ histories.support, ∀ response,
      finish history response = logicalFinish (retain history) response := by
    intro history hhistory response
    simp only [histories, support_bind, Set.mem_iUnion, support_map,
      Set.mem_image] at hhistory
    obtain ⟨info, hinfo, action, _haction, later, hlater, rfl⟩ := hhistory
    exact hfinish info hinfo action later hlater response
  have hlaw := histories.bind_policy_nativeKernel_eq_bind_conditionedPolicy
    retain second finish logicalFinish hfactor
  rw [hhistories] at hlaw
  refine ⟨logicalFirst, logicalSecond, ?_⟩
  simpa only [histories, logicalSecond, bind_bind, bind_map] using hlaw

end GameTheory.Math.Probability.FinDist
