/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveServiceRecall
import Vegas.Pending.ReactivePlayerWindow

/-! # Retained windows before their first submission

A retained response at a served event is either transport or a submission
by that event's owner. Thus an actual prefix with no recorded owner submission
is also supported by the ordinary replay policy, with its complete private
recall and passive samples preserved.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Every nontransport retained response names the sender's own turn, the least
ready event it owns. -/
theorem MessageBounds.compiled_current_response (bounds : MessageBounds graph)
    (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    response ∈ ((runtime.reactiveApplication leaks).replayPolicy past view).support ∨
      ∃ event, view.application.publicView.ownTurn? who = some event ∧
        graph.actor? event = some who ∧ runtime.submittedEvent? leaks response = some event := by
  classical
  have silent : (⟨none⟩ : (runtime.reactiveApplication leaks).Action) ∈
      ((runtime.reactiveApplication leaks).replayPolicy past view).support :=
    (runtime.reactiveApplication leaks).replayPolicy_support past view none
      (Finset.mem_insert_self _ _)
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | replay
  · have chosen := (Finset.mem_filter.mp decision).1
    cases selected : view.application.publicView.ownTurn? who with
    | none =>
        simp only [MessageBounds.decisionActions, selected] at chosen
        cases Finset.mem_singleton.mp chosen
        exact Or.inl silent
    | some event =>
        refine (Or.imp_right fun current => ⟨event, rfl, current⟩ : _ → _) ?_
        simp only [MessageBounds.decisionActions, selected] at chosen
        split at chosen
        · rename_i active
          cases node : nodeView graph event with
          | sample payload law outputEq codeEq =>
              rw [node] at chosen
              cases Finset.mem_singleton.mp chosen
              exact Or.inl silent
          | bind owner payload outputEq codeEq =>
              have actor := congrArg EventCode.actor codeEq
              rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
              change graph.actor? event = some owner at actor
              cases Option.some.inj (actor.symm.trans active.1)
              rw [node] at chosen
              obtain ⟨value, _, rfl⟩ := Finset.mem_image.mp chosen
              cases slot : reactiveFreshSlot view.application with
              | none =>
                  left
                  simpa only [serviceDecision, reactiveDecision, node, slot, Option.map_none,
                    ReactiveApplication.SubmissionNormalization.action]
                    using silent
              | some serial =>
                  right
                  refine ⟨active.1, ?_⟩
                  rw [runtime.serviceDecision_binding leaks who past view event payload outputEq
                    codeEq node serial slot (.success value), runtime.submittedEvent_normalization]
                  rfl
          | resolve owner payload binding checks outputEq codeEq =>
              rw [node] at chosen
              obtain ⟨choice, _, rfl⟩ := Finset.mem_image.mp chosen
              rcases runtime.serviceDecision_resolution_cases leaks who past view event owner
                  payload binding checks outputEq codeEq node choice with zero |
                  ⟨candidate, value, evidence, _, _, _, physical⟩
              · exact Or.inl (zero ▸ silent)
              · exact Or.inr ⟨active.1, by rw [physical]; rfl⟩
        · cases Finset.mem_singleton.mp chosen
          exact Or.inl silent
  · exact Or.inl (((runtime.reactiveApplication leaks).mem_replayActions_iff _ _ _).mp replay)

/-- An actual retained prefix with no owner submission is an actual replay
window. This retains the exact execution, including all local observations. -/
theorem compiled_unsubmitted_window (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks) (event : graph.EventId) (owner : Player)
    (owned : graph.actor? event = some owner) (visits : List Player)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (unsent : runtime.eventRecorded leaks (final.recall owner) event = false) :
    final ∈ (runtime.runInteractionPlan leaks
      (fun _ => (runtime.reactiveApplication leaks).replayPolicy) network
        (visits.map ServiceInstruction.player) initial).support := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil => exact reached
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map,
        PMF.bind_bind, Function.comp_def] at reached ⊢
      obtain ⟨sample, sampled, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨response, chosen, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      let activated := initial.sampledActivation app actor sample
      have transport : response ∈ (app.replayPolicy (activated.recall actor)
          (activated.observe app actor)).support := by
        rcases bounds.compiled_current_response runtime leaks actor _ _ response
            (lawful actor _ _ response chosen) with replay | ⟨named, selected, acting, submitted⟩
        · exact replay
        · have ready := (PublicView.ownTurn?_spec _ actor named selected).1
          change initial.application.publicView.EventReady named at ready
          cases sole.2 named ready
          have same : actor = owner := Option.some.inj (acting.symm.trans owned)
          subst actor
          have recorded := runtime.eventRecorded_respond leaks activated owner response event
            submitted
          obtain ⟨entry, present, action⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
          have kept := runtime.interactionPlan_recall_mono leaks players network
            (rest.map ServiceInstruction.player) (activated.respond app owner response)
            final reached owner
          have impossible := (runtime.eventRecorded_iff leaks _ event).mpr
            ⟨entry, kept present, action⟩
          rw [unsent] at impossible
          cases impossible
      rw [PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨sample, sampled, ?_⟩
      rw [PMF.support_bind]
      refine Set.mem_iUnion₂.mpr ⟨response, transport, ?_⟩
      apply ih (activated.respond app actor response) ?_ reached
      rw [(runtime.reactive_respond_application leaks activated actor response).2]
      exact sole

end Vegas.EventGraphRuntime
