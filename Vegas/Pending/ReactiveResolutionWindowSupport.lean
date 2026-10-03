/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledResolution
import Vegas.Pending.ReactiveSilentSettlement
import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveServiceRecall

/-! # Protected inclusion for every retained disclosure policy

A retained resolution window contains at most one fresh decision. Later visits
still permit passive observation while the decision remains pending. Protected inclusion
restores the published-network boundary for every
retained policy, whether the player opens, withholds, or continues waiting.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Once the current decision has been submitted, every retained response is
transport. No assertion about successful guards or source play is required. -/
theorem MessageBounds.compiled_resolution_recorded_transport (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (who owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (sole : execution.application.publicView.SoleReady event)
    (recorded : runtime.eventRecorded leaks (execution.recall owner) event = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)) :
    response = ⟨none⟩ := by
  rcases bounds.compiled_resolution_cases runtime leaks who _ _ event owner payload binding checks
    outputEq codeEq node sole response member with rfl | ⟨acting, _, first, shape⟩ |
      ⟨candidate, value, evidence, acting, _, _, _, _, first, shape⟩
  · rfl
  · have owned : graph.actor? event = some owner := by
      have actor := congrArg EventCode.actor codeEq
      rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
      exact actor
    have equal : who = owner := Option.some.inj (acting.symm.trans owned)
    have recordedWho : runtime.eventRecorded leaks (execution.recall who) event = true := by
      rw [equal]
      exact recorded
    rw [shape] at first
    simp only [firstSubmission, submittedEvent?, Payload.event?, recordedWho,
      Bool.not_true, Bool.false_eq_true] at first
  · have owned : graph.actor? event = some owner := by
      have actor := congrArg EventCode.actor codeEq
      rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
      exact actor
    have equal : who = owner := Option.some.inj (acting.symm.trans owned)
    have recordedWho : runtime.eventRecorded leaks (execution.recall who) event = true := by
      rw [equal]
      exact recorded
    rw [shape] at first
    simp only [firstSubmission, submittedEvent?, Payload.event?, recordedWho,
      Bool.not_true, Bool.false_eq_true] at first

/-- Recorded submissions stay recorded through the actual recall. The
transport conclusion is therefore available at every later roster visit. -/
theorem compiled_resolution_tail_transport (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (initial : (runtime.reactiveApplication leaks).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (sole : initial.application.publicView.SoleReady event)
    (recorded : runtime.eventRecorded leaks (initial.recall owner) event = true)
    (current : (runtime.reactiveApplication leaks).Execution)
    (same : current.application = initial.application)
    (recalled : initial.recall owner ⊆ current.recall owner)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈ (players who (current.recall who)
      (current.observe (runtime.reactiveApplication leaks) who)).support) :
    response = ⟨none⟩ := by
  obtain ⟨entry, member, submitted⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
  exact bounds.compiled_resolution_recorded_transport runtime leaks current who owner event payload
    binding checks outputEq codeEq node (by rw [same]; exact sole)
    ((runtime.eventRecorded_iff leaks _ event).mpr ⟨entry, recalled member, submitted⟩)
    response (lawful who _ _ response supported)

/-- An arbitrary retained resolution roster followed by its reserved inclusion
publishes every pending, known, and remembered input envelope. No guard-success,
prescribed opening time, or chosen source strategy is assumed. -/
theorem MessageBounds.compiled_resolution_inclusion_published (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (visits : List Player)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (sole : initial.application.publicView.SoleReady event)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (serials : initial.network.SerialsBeforeNext)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    final.network.Satisfies fun message => message.id ∈ final.network.ledger.map Message.id := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      simp only [List.map_nil, List.nil_append, runInteractionPlan, PMF.bind_pure] at reached
      rw [runtime.interaction_includeLatest_of_pending_published leaks players network
        initial owner event published.pending] at reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact published
  | cons who rest ih =>
      obtain ⟨middle, step, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at step
      change middle ∈ ((initial.environmentStep app (.activate who)).bind
        (app.invoke players who)).support at step
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at step
      obtain ⟨sample, _, step⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ step)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ step
      let activated := initial.sampledActivation app who sample
      have activePublished : activated.network.Satisfies fun message =>
          message.id ∈ activated.network.ledger.map Message.id := published.learn who sample
      have activeSerials : activated.network.SerialsBeforeNext := serials.learn who sample
      have allowed := lawful who _ _ response chosen
      have transportCase (transport : response = ⟨none⟩) :
          (final.network.Satisfies fun message =>
            message.id ∈ final.network.ledger.map Message.id) := by
        have preserved := runtime.silent_response_preserves leaks _ activated
          (published.learn who sample) who response transport
        exact ih (activated.respond app who response) (by rw [preserved.1]; exact sole)
          (by rw [preserved.2.1]; exact preserved.2.2.2.2.1)
          ((app.serialsBeforeNextInvariant (fun _ _ => PMF.pure .wait)).respond
            activated who response (serials.learn who sample)) tail
      rcases bounds.compiled_resolution_cases runtime leaks who _ _ event owner payload binding
        checks outputEq codeEq node sole response allowed with silent |
          ⟨acting, _, _, shape⟩ |
          ⟨candidate, value, evidence, acting, _, _, _, candidateOwned, _, shape⟩
      · exact transportCase silent
      · have owned : graph.actor? event = some owner := by
          have actor := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
          exact actor
        have equal : who = owner := Option.some.inj (acting.symm.trans owned)
        subst who
        subst response
        let submission : WitnessedSubmission graph :=
          ⟨⟨.withhold event, none⟩, .none⟩
        let submitted := activated.respond app owner ⟨some submission⟩
        have recorded : runtime.eventRecorded leaks (submitted.recall owner) event = true :=
          runtime.eventRecorded_respond leaks activated owner _ event rfl
        exact runtime.submission_silent_settled_published leaks players network owner activated
          submission event rfl activePublished activeSerials
          (fun current actor action same recalled supported =>
            runtime.compiled_resolution_tail_transport leaks bounds players lawful submitted owner
              event payload binding checks outputEq codeEq node sole recorded current same
                recalled actor action supported) rest final tail
      · have owned : graph.actor? event = some owner := by
          have actor := congrArg EventCode.actor codeEq
          rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
          exact actor
        have equal : who = owner := Option.some.inj (acting.symm.trans owned)
        clear candidateOwned
        subst who
        subst response
        let submission : WitnessedSubmission graph :=
          ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩
        let submitted := activated.respond app owner ⟨some submission⟩
        have recorded : runtime.eventRecorded leaks (submitted.recall owner) event = true :=
          runtime.eventRecorded_respond leaks activated owner _ event rfl
        exact runtime.submission_silent_settled_published leaks players network owner activated
          submission event rfl activePublished activeSerials
          (fun current actor action same recalled supported =>
            runtime.compiled_resolution_tail_transport leaks bounds players lawful submitted owner
              event payload binding checks outputEq codeEq node sole recorded current same
                recalled actor action supported) rest final tail

end Vegas.EventGraphRuntime
