/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingWindow
import Vegas.Pending.ReactiveBindingReplay

/-! # Binding provenance for every permitted service policy

The first typed binding may occur at any owner opportunity. Before it all
responses transport known envelopes; after it the menu forbids another fresh
binding. The required final opportunity rules out omission. This proof covers
all permitted policies and retains actual passive samples and replay copies.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every supported binding roster endpoint is a real successful typed
submission followed by protected inclusion, up to the exact application and
public allocation records. No particular source strategy is assumed. -/
theorem sourceService_binding_roster_support
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (covered : bounds.CoversBindingValues)
    (players : Player → (application setup leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who past view)
    (network : (runtime setup).NetworkPolicy leaks)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (owned : (graph setup).actor? event = some owner)
    (serial : Nat) (capacity : serial < bounds.candidateCount)
    (visits : List Player) (initial final : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (ready : initial.application.config.cut.Ready event)
    (selected : reactiveFreshSlot (initial.observe
      (application setup leaks) owner).application = some serial)
    (candidate : initial.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (serials : initial.network.SerialsBeforeNext)
    (unsent : (runtime setup).eventRecorded leaks (initial.recall owner) event = false)
    (opportunity : owner ∈ visits)
    (ends : (initial.recall owner).length + visits.count owner =
      rosterOffset setup rosters owner event + (rosters event).count owner)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    ∃ before immediate : (application setup leaks).Execution,
      ∃ value ∈ bounds.typedValues payload,
      before.application = initial.application ∧ before.network.ledger = initial.network.ledger ∧
      before.receipts = initial.receipts ∧ before.network.nextSerial = initial.network.nextSerial ∧
      before.network.SerialsBeforeNext ∧
      immediate ∈ ((runtime setup).interactionStep leaks players network
        (.includeLatest event owner)
        (before.respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload (.success value)
            serial))).support ∧
      final.application = immediate.application ∧ final.network.ledger = immediate.network.ledger ∧
      final.receipts = immediate.receipts ∧
      final.network.nextSerial = immediate.network.nextSerial ∧
      final.network.Satisfies
        (fun message => message.id ∈ final.network.ledger.map Message.id) := by
  let app := application setup leaks
  have ordinary : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions (runtime setup) leaks who past view :=
    fun who past view response supported =>
      sourceServiceMenu_in_compiled setup leaks bounds rosters who past view
        (lawful who past view response supported)
  induction visits generalizing initial with
  | nil => cases opportunity
  | cons actor rest ih =>
      simp only [List.map_cons, List.cons_append, runInteractionPlan] at reached
      obtain ⟨middle, step, tail⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, FinDist.pure_bind] at step
      change middle ∈ ((initial.environmentStep app (.activate actor)).bind
        (app.invoke players actor)).support at step
      rw [ReactiveApplication.Execution.activation_samples, FinDist.bind_map] at step
      obtain ⟨sample, _, step⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ step)
      obtain ⟨response, chosen, rfl⟩ := FinDist.support_map .. ▸ step
      let activated := initial.sampledActivation app actor sample
      have casesResponse : response ∈ (app.replayPolicy (activated.recall actor)
          (activated.observe app actor)).support ∨
          actor = owner ∧ ∃ value ∈ bounds.typedValues payload,
            response = (runtime setup).reactiveBinding leaks owner event payload
              (.success value) serial := by
        by_cases acting : actor = owner
        · subst actor
          rcases bounds.ordinary_binding_cases (runtime setup) leaks owner
              (activated.recall owner) (activated.observe app owner) event payload
              outputEq codeEq node granted owned
              ((initial.application.publicView_eventReady event).mpr ready) serial selected response
              (ordinary owner _ _ response chosen) with transport | ⟨value, admitted, _, physical⟩
          · exact Or.inl transport
          · refine Or.inr ⟨rfl, value, admitted, physical.trans ?_⟩
            exact (runtime setup).reactiveBinding_normal_of_fresh leaks owner _ _ event payload
              (.success value) serial candidate
        · exact Or.inl (bounds.compiled_foreign_transport (runtime setup) leaks actor _ _ event
            granted (fun equal => acting (Option.some.inj (owned.symm.trans equal)).symm)
              response (ordinary actor _ _ response chosen))
      rcases casesResponse with transport | ⟨acting, value, admitted, physical⟩
      · have shape := app.replayPolicy_cases _ _ response transport
        have restOpportunity : owner ∈ rest := by
          by_contra absent
          have acting : actor = owner := (List.mem_cons.mp opportunity).resolve_right absent |>.symm
          subst actor
          have last : (activated.recall owner).length + 1 =
              rosterOffset setup rosters owner event + (rosters event).count owner := by
            change (initial.recall owner).length + 1 = _
            simpa only [List.count_cons_self, List.count_eq_zero.mpr absent, Nat.zero_add]
              using ends
          obtain ⟨value, _, physical⟩ :=
            sourceService_final_binding_cases setup leaks bounds rosters
            covered owner (activated.recall owner) (activated.observe app owner)
              event payload outputEq codeEq node granted owned
              ((initial.application.publicView_eventReady event).mpr ready) unsent last serial
                selected capacity response (lawful owner _ _ response chosen)
          rw [(runtime setup).reactiveBinding_normal_of_fresh leaks owner _ _ event payload
            (.success value) serial candidate] at physical
          rcases shape with rfl | ⟨id, rfl⟩ <;> cases physical
        have preserved := (runtime setup).replay_response_preserves leaks _ activated
          (published.learn actor sample) actor response shape
        have nextUnsent : (runtime setup).eventRecorded leaks
            ((activated.respond app actor response).recall owner) event = false := by
          rw [(runtime setup).eventRecorded_respond_other leaks activated actor owner response
            event (fun _ => by
              rcases shape with rfl | ⟨id, rfl⟩ <;> intro impossible <;> cases impossible)]
          exact unsent
        have nextSelected : reactiveFreshSlot
            ((activated.respond app actor response).observe app owner).application =
              some serial := by
          change reactiveFreshSlot (app.observePlayer
            (activated.respond app actor response).application owner) = _
          rw [preserved.1]
          exact selected
        have nextEnds : ((activated.respond app actor response).recall owner).length +
            rest.count owner = rosterOffset setup rosters owner event +
              (rosters event).count owner := by
          rw [app.respond_recall_length]
          change (initial.recall owner).length + (if actor = owner then 1 else 0) + _ = _
          by_cases same : actor = owner <;> simp [same] at ends ⊢
          all_goals omega
        have nextSerials : (activated.respond app actor response).network.SerialsBeforeNext :=
          (app.serialsBeforeNextInvariant (fun _ _ => FinDist.pure .wait)).respond activated actor
            response (serials.learn actor sample)
        obtain ⟨before, immediate, value, admitted, beforeApp, beforeLedger, beforeReceipts,
          beforeCounters, beforeSerials, immediateSupport, finalApp, finalLedger, finalReceipts,
          finalCounters, finalPublished⟩ := ih (activated.respond app actor response)
            (by rw [preserved.1]; exact granted) (by rw [preserved.1]; exact ready)
            nextSelected (by rw [preserved.1]; exact candidate)
            (by rw [preserved.2.1]; exact preserved.2.2.2.2.1) nextSerials nextUnsent
            restOpportunity nextEnds tail
        exact ⟨before, immediate, value, admitted, beforeApp.trans preserved.1,
          beforeLedger.trans preserved.2.1, beforeReceipts.trans preserved.2.2.1,
          beforeCounters.trans preserved.2.2.2.1, beforeSerials, immediateSupport, finalApp,
          finalLedger, finalReceipts, finalCounters, finalPublished⟩
      · subst actor
        rw [physical] at tail
        obtain ⟨immediate, included, finalApp, finalLedger, finalReceipts, finalCounters,
          finalPublished⟩ :=
          (runtime setup).rawBinding_delayed_support leaks bounds players ordinary
            network activated owner event payload outputEq codeEq node granted owned ready
              (published.learn owner sample) (serials.learn owner sample) serial
              (some ⟨payload, value⟩) rest final tail
        exact ⟨activated, immediate, value, admitted, rfl, rfl, rfl, rfl,
          serials.learn owner sample, included, finalApp, finalLedger, finalReceipts, finalCounters,
          finalPublished⟩

end Vegas.SourceProgram.RevealService
