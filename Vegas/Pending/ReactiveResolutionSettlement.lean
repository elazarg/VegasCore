/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveResolutionWindowSupport
import Vegas.Pending.ReactiveResolutionWindowState
import Vegas.Pending.ReactiveDisclosureStability
import Vegas.EventGraph.ResolutionProvenance
import Interaction.ReactiveSubmissionSerial

/-! # Settlement of arbitrary retained disclosure windows

Every retained policy either leaves the current resolution for expiry or
includes an authenticated withholding or successful guarded opening. The
result retains the actual response and observation branches and restores
every player's public serial
accounting. No source strategy or opening schedule is fixed in the premise.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- Reserved inclusion after any retained disclosure roster either waits or
performs an actual Boolean graph completion, with no outstanding serial debt. -/
theorem MessageBounds.compiled_resolution_settlement (bounds : MessageBounds graph)
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
    (valid : initial.application.BindingInvariant)
    (unremembered : initial.application.remembered event = none)
    (ready : initial.application.config.cut.Ready event)
    (timely : initial.application.WithinDeadline runtime event)
    (sole : initial.application.publicView.SoleReady event)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (serials : initial.network.SerialsBeforeNext)
    (accounted : ∀ who, initial.network.nextSerial who =
      Message.distinctAuthoredCount initial.network.ledger who)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) initial).support) :
    ((final.application = initial.application ∧
      runtime.eventRecorded leaks (final.recall owner) event =
        runtime.eventRecorded leaks (initial.recall owner) event) ∨ ∃ disclose result,
      EventCode.resolveOutput? binding checks disclose initial.application.config.store =
        some result ∧
      (disclose = false ∨ ∃ value, result = PublicationResult.success value) ∧
      final.application = initial.application.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm) result)) ∧
    (∀ who, final.network.nextSerial who =
      Message.distinctAuthoredCount final.network.ledger who) := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      simp only [List.map_nil, List.nil_append, runInteractionPlan, PMF.bind_pure] at reached
      rw [runtime.interaction_includeLatest_of_pending_published leaks players network
        initial owner event published.pending] at reached
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨Or.inl ⟨rfl, rfl⟩, accounted⟩
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
          ((final.application = initial.application ∧
            runtime.eventRecorded leaks (final.recall owner) event =
              runtime.eventRecorded leaks (initial.recall owner) event) ∨ ∃ disclose result,
            EventCode.resolveOutput? binding checks disclose initial.application.config.store =
              some result ∧
            (disclose = false ∨ ∃ value, result = PublicationResult.success value) ∧
            final.application = initial.application.complete event ready
              (cast (congrArg EventField.Action outputEq.symm) disclose)
              (cast (congrArg EventField.Value outputEq.symm) result)) ∧
          (∀ observer, final.network.nextSerial observer =
            Message.distinctAuthoredCount final.network.ledger observer) := by
        have preserved := runtime.silent_response_preserves leaks _ activated
          activePublished who response transport
        have nextAccounted : ∀ observer,
            (activated.respond app who response).network.nextSerial observer =
              Message.distinctAuthoredCount (activated.respond app who response).network.ledger
                observer := by
          rw [preserved.2.1, preserved.2.2.2.1]
          exact accounted
        obtain ⟨result, counters⟩ := ih (activated.respond app who response)
          (by rw [preserved.1]; exact valid) (by rw [preserved.1]; exact unremembered)
          (by rw [preserved.1]; exact ready)
          (by rw [preserved.1]; exact timely) (by rw [preserved.1]; exact sole)
          (by rw [preserved.2.1]; exact preserved.2.2.2.2.1)
          ((app.serialsBeforeNextInvariant (fun _ _ => PMF.pure .wait)).respond
            activated who response activeSerials) nextAccounted tail
        have same : (activated.respond app who response).application =
            initial.application := preserved.1
        dsimp only [app] at result same
        rcases result with ⟨applicationEq, recordedEq⟩ | completed
        · refine ⟨Or.inl ⟨applicationEq.trans same, ?_⟩, counters⟩
          rw [recordedEq, runtime.eventRecorded_respond_transport leaks activated who owner
            response transport event]
          rfl
        · exact ⟨Or.inr (by simpa only [same] using completed), counters⟩
      have submittedCase (submission : WitnessedSubmission graph)
          (addressed : submission.call.packet.event? graph = some event)
          (ownerEq : who = owner) (responseEq : response = ⟨some submission⟩)
          (completed : State graph)
          (handled : app.handle (activated.respond app owner ⟨some submission⟩).application
            ⟨(owner, initial.network.nextSerial owner),
              app.packet (app.submit activated.application owner submission) owner
                (activated.network.known owner) submission⟩ = some completed) :
          final.application = completed ∧
            ∀ observer, final.network.nextSerial observer =
              Message.distinctAuthoredCount final.network.ledger observer := by
        subst who
        subst response
        let submitted := activated.respond app owner ⟨some submission⟩
        let packet := app.packet (app.submit activated.application owner submission) owner
          (activated.network.known owner) submission
        let message : Message Player (WitnessedPacket graph) :=
          ⟨(owner, initial.network.nextSerial owner), packet⟩
        have sameApplication : submitted.application = initial.application :=
          bounds.compiled_resolution_application runtime leaks owner activated event owner payload
            binding checks outputEq codeEq node sole _ allowed
        have submittedSole : submitted.application.publicView.SoleReady event := by
          rw [sameApplication]
          exact sole
        have recorded : runtime.eventRecorded leaks (submitted.recall owner) event = true :=
          runtime.eventRecorded_respond leaks activated owner _ event addressed
        have transport := fun current actor action same recalled supported =>
          runtime.compiled_resolution_tail_transport leaks bounds players lawful submitted owner
            event payload binding checks outputEq codeEq node submittedSole recorded current same
              recalled actor action supported
        have packets : submitted.network.Satisfies fun other =>
            other.id ∈ submitted.network.ledger.map Message.id ∨ other = message := by
          change (activated.network.submit owner packet).2.Satisfies _
          exact (activePublished.mono (fun _ prior => Or.inl prior)).submit
            owner packet (Or.inr rfl)
        have pending : message ∈ submitted.network.pending :=
          List.mem_append_right _ (List.mem_singleton_self _)
        have law := runtime.silent_window_settlement leaks players network owner submitted
          transport event message rfl addressed packets pending
            (serials.next_unpublished owner) rest
        have mapped : (final.application, final.network.ledger,
            final.receipts, final.network.nextSerial) ∈
            ((runtime.runInteractionPlan leaks players network
              (rest.map ServiceInstruction.player ++ [.includeLatest event owner]) submitted).map
              fun result => (result.application, result.network.ledger,
                result.receipts, result.network.nextSerial)).support :=
          PMF.support_map .. ▸ ⟨final, tail, rfl⟩
        rw [law, handled, Option.getD_some, Option.isSome_some,
            PMF.mem_support_pure_iff _ _] at mapped
        refine ⟨congrArg Prod.fst mapped, ?_⟩
        have ledger := congrArg (fun result => result.2.1) mapped
        have counters := congrArg (fun result => result.2.2.2) mapped
        dsimp only at ledger counters
        intro observer
        rw [counters, ledger]
        change (activated.network.submit owner packet).2.nextSerial observer =
          Message.distinctAuthoredCount
            (@List.append (Message Player (WitnessedPacket graph)) initial.network.ledger
              [message]) observer
        have counted := activeSerials.submit_include_serials_match_ledger
          accounted owner packet observer
        rw [MessageNetwork.includePending, activeSerials.lookup_submit owner packet] at counted
        exact counted
      have owned : graph.actor? event = some owner := by
        have actor := congrArg EventCode.actor codeEq
        rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
        exact actor
      rcases bounds.compiled_resolution_cases runtime leaks who _ _ event owner payload binding
        checks outputEq codeEq node sole response allowed with silent |
          ⟨acting, _, _, shape⟩ |
          ⟨candidate, value, evidence, acting, _, resolved, associated, candidateOwned, _, shape⟩
      · exact transportCase silent
      · let submission : WitnessedSubmission graph := ⟨⟨.withhold event, none⟩, .none⟩
        have resolved : EventCode.resolveOutput? binding checks false
            initial.application.config.store = some .failure := by
          apply EventCode.resolveOutput?_false_eq_failure binding checks
            initial.application.config.store
          intro field read
          apply initial.application.config.read_available ready
          rw [resolution_readFields event owner payload binding checks outputEq codeEq]
          exact read
        have baseHandled := runtime.handle_withhold_unremembered_eq
          initial.application (owner, initial.network.nextSerial owner) event owner payload
          binding checks outputEq codeEq node ready timely rfl unremembered
        let completed := initial.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) false)
          (cast (congrArg EventField.Value outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)))
        have handled : app.handle (activated.respond app owner ⟨some submission⟩).application
            ⟨(owner, initial.network.nextSerial owner),
              app.packet (app.submit activated.application owner submission) owner
                (activated.network.known owner) submission⟩ = some completed :=
          (reactiveApplication_handle_of_tokenValid runtime leaks _ _
            (tokenFor_tokenValid_of_handle runtime initial.application _ _ _ _
              baseHandled)).trans baseHandled
        obtain ⟨applicationEq, counters⟩ := submittedCase submission rfl
          (Option.some.inj (acting.symm.trans owned)) shape completed handled
        exact ⟨Or.inr ⟨false, .failure, resolved, Or.inl rfl, applicationEq⟩, counters⟩
      · have equal : who = owner := Option.some.inj (acting.symm.trans owned)
        have candidateOwner : candidate.1 = owner := candidateOwned.trans equal
        change EventCode.resolveOutput? binding checks true
          (graph.playerStore who initial.application.config.store) = _ at resolved
        rw [equal, EventCode.resolveOutput?_playerStore] at resolved
        change initial.application.accepted binding.field = some candidate at associated
        have stored := EventCode.binding_success_of_resolve_success binding checks true
          initial.application.config.store value resolved
        obtain ⟨selected, accepted, _, fixed⟩ := valid.success_provenance binding value stored
        have selectedEq : selected = candidate := Option.some.inj (accepted.symm.trans associated)
        subst selected
        let submission : WitnessedSubmission graph :=
          ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩
        let completed := initial.application.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (.success value))
        have baseHandled := runtime.handle_opening_eq initial.application
          (owner, initial.network.nextSerial owner) event candidate owner payload binding
            checks outputEq codeEq node ready timely rfl candidateOwner associated value fixed
              stored (.success value) resolved
        have handled : app.handle (activated.respond app owner ⟨some submission⟩).application
            ⟨(owner, initial.network.nextSerial owner),
              app.packet (app.submit activated.application owner submission) owner
                (activated.network.known owner) submission⟩ = some completed :=
          (reactiveApplication_handle_of_tokenValid runtime leaks _ _
            (tokenFor_tokenValid_of_handle runtime initial.application _ _ _ _
              baseHandled)).trans baseHandled
        obtain ⟨applicationEq, counters⟩ := submittedCase submission rfl equal shape
          completed handled
        exact ⟨Or.inr ⟨true, .success value, resolved, Or.inr ⟨value, rfl⟩,
          applicationEq⟩, counters⟩

end Vegas.EventGraphRuntime
