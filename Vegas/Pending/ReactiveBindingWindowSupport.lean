/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingReplay
import Vegas.Pending.ReactiveServiceRecall

/-! # Unsubmitted prefixes of retained binding windows

Before the first binding, every actual response is silence or a known replay.
The application, allocator, ledger and serial counter therefore remain exactly
at the completed boundary. This covers every permitted policy and arbitrary
passive samples, not just a prescribed source strategy.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem compiled_binding_unsubmitted_prefix (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (owned : graph.actor? event = some owner)
    (serial : Nat) (visits : List Player)
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (ready : initial.application.config.cut.Ready event)
    (selected : reactiveFreshSlot
      (initial.observe (runtime.reactiveApplication leaks) owner).application = some serial)
    (fresh : initial.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (unsent : runtime.eventRecorded leaks (final.recall owner) event = false) :
    final.application = initial.application ∧ final.network.ledger = initial.network.ledger ∧
      final.receipts = initial.receipts ∧ final.network.nextSerial = initial.network.nextSerial ∧
      final.network.Satisfies
        (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases FinDist.mem_support_pure.mp reached
      exact ⟨rfl, rfl, rfl, rfl, published⟩
  | cons actor rest ih =>
      obtain ⟨middle, step, tail⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at step
      change middle ∈ ((initial.environmentStep app (.activate actor)).bind
        (app.invoke players actor)).support at step
      rw [ReactiveApplication.Execution.activation_samples, FinDist.bind_map] at step
      obtain ⟨sample, _, step⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ step)
      obtain ⟨response, chosen, rfl⟩ := FinDist.support_map .. ▸ step
      let activated := initial.sampledActivation app actor sample
      have transport : response ∈ (app.replayPolicy (activated.recall actor)
          (activated.observe app actor)).support := by
        by_cases acting : actor = owner
        · subst actor
          rcases bounds.ordinary_binding_cases runtime leaks owner (activated.recall owner)
              (activated.observe app owner) event payload outputEq codeEq node granted owned
              ((initial.application.publicView_eventReady event).mpr ready) serial selected response
              (lawful owner _ _ response chosen) with replay | ⟨value, _, _, physical⟩
          · exact replay
          · have recorded : runtime.eventRecorded leaks
                ((activated.respond app owner response).recall owner) event = true := by
              apply runtime.eventRecorded_respond leaks activated owner response event
              rw [physical, runtime.submittedEvent_normalization]
              rfl
            obtain ⟨entry, member, action⟩ := (runtime.eventRecorded_iff leaks _ event).mp recorded
            have recalled := runtime.interactionPlan_recall_mono leaks players network
              (rest.map ServiceInstruction.player) (activated.respond app owner response) final
                tail owner
            have finalRecorded := (runtime.eventRecorded_iff leaks (final.recall owner) event).mpr
              ⟨entry, recalled member, action⟩
            rw [unsent] at finalRecorded
            cases finalRecorded
        · exact bounds.compiled_foreign_transport runtime leaks actor _ _ event granted
            (fun equal => acting (Option.some.inj (owned.symm.trans equal)).symm)
            response (lawful actor _ _ response chosen)
      have preserved := runtime.replay_response_preserves leaks _ activated
        (published.learn actor sample) actor response
          (app.replayPolicy_cases _ _ response transport)
      have nextSelected : reactiveFreshSlot
          ((activated.respond app actor response).observe app owner).application = some serial := by
        change reactiveFreshSlot (app.observePlayer
          (activated.respond app actor response).application owner) = _
        rw [preserved.1]
        exact selected
      obtain ⟨application, ledger, receipts, counters, packets⟩ :=
        ih (activated.respond app actor response) (by rw [preserved.1]; exact granted)
          (by rw [preserved.1]; exact ready) nextSelected
          (by rw [preserved.1]; exact fresh)
          (by rw [preserved.2.1]; exact preserved.2.2.2.2.1) tail
      exact ⟨application.trans preserved.1, ledger.trans preserved.2.1,
        receipts.trans preserved.2.2.1, counters.trans preserved.2.2.2.1, packets⟩

end Vegas.EventGraphRuntime
