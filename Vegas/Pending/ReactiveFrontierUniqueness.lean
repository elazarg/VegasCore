/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFrontier
import Vegas.EventGraph.ConfigRestriction

/-! # Unique sampled frontier semantics for genuine private memories -/

noncomputable section
namespace Vegas.EventGraphRuntime
open Interaction EventGraph GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Actual memories and the physical execution determine a unique full
semantic frontier key, including outputs still awaiting settlement. -/
theorem ReactiveFrontier.semanticKey_unique (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (execution : (runtime.reactiveApplication leaks).Execution)
    (stable : runtime.EntryEventStable leaks execution)
    (memories : Player → List (Option graph.Completion)) (left right : graph.Config)
    (leftRelated : runtime.ReactiveFrontier leaks execution memories left)
    (rightRelated : runtime.ReactiveFrontier leaks execution memories right)
    (profile : graph.BehavioralProfile)
    (consistent : ∀ owner, (runtime.prescribedReactivePolicy leaks owner (profile owner)).Consistent
      (execution.recall owner))
    (supported : ∀ owner, memories owner ∈
      ((runtime.prescribedReactiveImplementation leaks owner (profile owner)).posterior
        (execution.recall owner)).support) : graph.semanticKey left = graph.semanticKey right := by
  have cuts : left.cut = right.cut := by
    apply EventOrder.Cut.ext
    apply Finset.ext
    intro event
    exact (leftRelated.domain event).trans (rightRelated.domain event).symm
  have outputs : left.outputs = right.outputs := by
    funext event
    by_cases physical : event ∈ execution.application.config.cut.completed
    · exact (leftRelated.settled event physical).symm.trans (rightRelated.settled event physical)
    · by_cases completed : event ∈ left.cut.completed
      · obtain ⟨owner, remembered, retained, named⟩ :=
          (leftRelated.domain event).mp completed |>.resolve_left physical
        subst event
        have ready := runtime.prescribedReactivePosterior_pending_ready leaks execution stable owner
          (profile owner) (consistent owner) (memories owner) (supported owner)
          remembered retained physical
        have actor := runtime.prescribedReactivePosterior_owned leaks owner (profile owner)
          (consistent owner) (memories owner) (supported owner) remembered retained
        obtain ⟨value, pureEval⟩ :=
          (graph.nodes remembered.event).eval?_eq_pure_of_actor owner actor
          remembered.action execution.application.config.store
          (fun _ read => execution.application.config.read_available ready read)
        have stored (frontier : graph.Config)
            (related : runtime.ReactiveFrontier leaks execution memories frontier) :
            frontier.outputs remembered.event = some value := by
          have recorded : remembered ∈ frontier.history := by
            have owned : remembered ∈ graph.ownCompletions owner frontier.history := by
              rw [related.intentions owner]
              exact List.mem_filterMap.mpr ⟨some remembered, retained, rfl⟩
            exact (List.mem_filter.mp owned).1
          obtain ⟨law, written, output, evaluates, positive⟩ :=
            related.reachable.history_output_semantics remembered recorded
          have sameEval := related.settled.ready_eval _ _ related.inputs.symm
            remembered.event ready remembered.action
          have sameLaw : law = PMF.pure value :=
            Option.some.inj (evaluates.symm.trans (sameEval.symm.trans pureEval))
          rw [sameLaw, PMF.mem_support_pure_iff] at positive
          subst written
          exact output
        exact (stored left leftRelated).trans (stored right rightRelated).symm
      · have absentOutput (config : graph.Config)
            (absent : event ∉ config.cut.completed) : config.outputs event = none := by
          cases output : config.outputs event with
          | none => rfl
          | some value =>
              exact (absent ((config.output_available event).mp
                (by simp only [output, Option.isSome_some]))).elim
        have rightAbsent : event ∉ right.cut.completed := by
          rw [← cuts]
          exact completed
        exact (absentOutput left completed).trans (absentOutput right rightAbsent).symm
  unfold semanticKey storeRecall
  apply Prod.ext cuts
  apply Prod.ext
  · funext field
    cases field with
    | inl input =>
        exact congrArg (fun values : graph.Inputs => some (values input))
          (leftRelated.inputs.trans rightRelated.inputs.symm)
    | inr event => exact congrArg (fun values => values event) outputs
  · funext owner
    exact (leftRelated.intentions owner).trans (rightRelated.intentions owner).symm

end Vegas.EventGraphRuntime
