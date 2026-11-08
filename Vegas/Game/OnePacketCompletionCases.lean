/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCompletion
import Vegas.Game.SourceServiceFacts
import Vegas.Pending.ExclusionEvidence

/-! # Accepted, expired and automatic owned completion records

A new owned record comes from an accepted packet, a due expiry, or automatic
service of a defaulted owner. Expiry preserves the complete accepted table;
automatic records retain their actual native origin and silent metadata even
when the command's primary acceptance changed another event's table entry.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

/-- Accepted packets supply the decoded actual decision. Both expiry and
automatic service have failing decoded records; only expiry asserts global
accepted-table equality across the complete physical command. -/
theorem completion_cases
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (execution next : (application setup timeouts leaks).Execution)
    (command : (application setup timeouts leaks).Command)
    (reached : next ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (record : (graph setup).Completion) (fresh : record ∉ execution.application.config.history)
    (present : record ∈ next.application.config.history)
    {actor : Player} (acts : (graph setup).actor? record.event = some actor) :
    (∃ message ∈ next.network.ledger, message.sender = actor ∧
      message.payload.call.event? (graph setup) = some record.event ∧
      record.decision.bind (decodeEventAction setup.program record.event) =
        callContent setup execution.application message.payload.call ∧
      (∀ named candidate, message.payload.call = .commitment named candidate →
        candidate.1 = actor) ∧
      ∀ owner payload, (graph setup).outputLayout record.event = .binding owner payload →
        next.application.accepted (.inr record.event) ≠ none) ∨
    (next.application.accepted = execution.application.accepted ∧
      Failing (record.decision.bind (decodeEventAction setup.program record.event))) ∨
    (Failing (record.decision.bind (decodeEventAction setup.program record.event)) ∧
      ∃ native, native.drain = next.application ∧ record ∉ native.config.history ∧
        ((∃ message ∈ execution.network.pending, command = .include message.id ∧
            handle timeouts execution.application ⟨message.id, message.payload.call⟩ = some
              native) ∨
          ∃ operation, command = .application operation ∧
            native ∈ (environmentStep timeouts execution.application operation).support) ∧
        record.decision = none ∧ record.defaultEvent = none ∧ actor ∈ native.config.defaulted) := by
  rcases owned_completion_cases execution next command reached record fresh present acts with
    accepted | expired | automatic
  · rcases accepted with ⟨accepted⟩
    exact Or.inl ⟨accepted.message, accepted.ledger,
      accepted.sender, accepted.named,
      accepted.content, accepted.candidateOwner,
        accepted.bindingAccepted⟩
  · obtain ⟨expiredCommand, entered, activated, due, action, value, expired, recorded⟩ := expired
    have table : next.application.accepted = execution.application.accepted := by
      rw [expiredCommand] at reached
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
      obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
      exact (reactiveApplication_environment_tables timeouts leaks execution.application state
        (.expire record.event) changed).1
    have decision := eq_of_heq (EventCompletion.mk.inj recorded).2.1
    have failed : Failing
        (record.decision.bind (decodeEventAction setup.program record.event)) := by
      rw [decision]
      exact expired_record_failing execution.application.config expired
    exact Or.inr (Or.inl ⟨table, failed⟩)
  · have silent : record.decision = none := by
      obtain ⟨native, drained, freshNative, trigger, silent, unchanged, inactive⟩ := automatic
      exact silent
    have failed : Failing
        (record.decision.bind (decodeEventAction setup.program record.event)) := by
      rw [silent, Option.bind_none]
      simp [Failing, OwnAction.disclosure]
    exact Or.inr (Or.inr ⟨failed, automatic⟩)

section History

open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability EventGraph

variable {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}

private theorem completeFailure_publication_failed
    (state : EventGraphRuntime.State (graph setup)) (event : (graph setup).EventId)
    (ready : state.config.cut.Ready event) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publication payload) :
    (⟨.inr event, outputEq⟩ : FieldRef (graph setup).layout (.publication payload)).get?
      (state.completeFailure event ready).config.store = some .failure := by
  cases node : nodeView (graph setup) event with
  | bind owner bindingPayload bindingEq codeEq =>
      rw [bindingEq] at outputEq
      cases outputEq
  | sample sampled law sampleEq codeEq =>
      rw [sampleEq] at outputEq
      cases outputEq
  | resolve owner resolved binding checks publicationEq codeEq =>
      have same := EventGraph.EventField.publication.inj (publicationEq.symm.trans outputEq)
      subst resolved
      simp only [State.completeFailure, node, State.complete, FieldRef.get?, Config.store,
        Config.complete, Function.update_self]
      have castSome {A B : Type} (same : A = B) (value : B) :
          cast (congrArg Option same) (some (cast same.symm value)) = some value := by
        cases same
        rfl
      exact castSome (congrArg EventGraph.EventField.Value outputEq) .failure

private theorem drain_publication_failed
    (state : EventGraphRuntime.State (graph setup)) (record : (graph setup).Completion)
    (fresh : record ∉ state.config.history) (present : record ∈ state.drain.config.history)
    (payload : L.Ty)
    (outputEq : (graph setup).outputLayout record.event = .publication payload) :
    (⟨.inr record.event, outputEq⟩ : FieldRef (graph setup).layout (.publication payload)).get?
      state.drain.config.store = some .failure := by
  have allFailed : ∀ completion, completion ∉ state.config.history →
      completion ∈ state.drain.config.history → ∀ valueType
      (layout : (graph setup).outputLayout completion.event = .publication valueType),
      (⟨.inr completion.event, layout⟩ :
        FieldRef (graph setup).layout (.publication valueType)).get?
          state.drain.config.store = some .failure := by
    apply State.drainFuel_induction (fun after => ∀ completion,
      completion ∉ state.config.history → completion ∈ after.config.history → ∀ valueType
      (layout : (graph setup).outputLayout completion.event = .publication valueType),
      (⟨.inr completion.event, layout⟩ :
        FieldRef (graph setup).layout (.publication valueType)).get?
          after.config.store = some .failure) ?_ state.config.remaining state ?_
    · intro before event eligible retained completion absent inside valueType layout
      rw [before.completeAutomatic_history event eligible] at inside
      rcases List.mem_append.mp inside with earlier | current
      · exact FieldRef.get?_preserved _ _ _
          (before.completeAutomatic_store_of_some event eligible) _
          (retained completion absent earlier valueType layout)
      · cases List.mem_singleton.mp current
        exact completeFailure_publication_failed before event eligible.1 valueType layout
    · exact fun completion absent inside => (absent inside).elim
  exact allFailed record fresh present payload outputEq

private theorem expired_owner_defaulted
    {remaining : Nat} {before after : (application setup timeouts leaks).Execution}
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace
      (some ⟨remaining, none, before⟩))
    (event : (graph setup).EventId) (actor : Player)
    (owned : (graph setup).actor? event = some actor)
    (unfinished : event ∉ before.application.config.cut.completed)
    (completed : event ∈ after.application.config.cut.completed)
    (entered : Nat) (activated : before.application.activatedAt event = some entered)
    (due : timeouts.duration event ≤ before.application.clock - entered)
    (reached : after ∈ (before.environmentStep (application setup timeouts leaks)
      (.application (.expire event))).support) :
    actor ∈ after.application.config.defaulted ∧ ∀ payload
      (outputEq : (graph setup).outputLayout event = .publication payload),
      (⟨.inr event, outputEq⟩ : FieldRef (graph setup).layout (.publication payload)).get?
        after.application.config.store = some .failure := by
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have nativeTrace := trace
  have initialEq : initialLaw setup = (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := graph setup)) :=
    serviceInitialLaw_eq_inputs (mode := .sequential) setup
  rw [initialEq] at nativeTrace
  have valid : ExclusionEvidence 0 ∅ before.application :=
    ExclusionEvidence.history timeouts leaks (setup.initialLaw.map setup.eventInputs)
      horizon scheduler nativeTrace
  obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ reached
  obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ supported
  change state ∈ ((environmentStep timeouts before.application (.expire event)).map
    State.drain).support at changed
  obtain ⟨native, moved, rfl⟩ := PMF.support_map .. ▸ changed
  change actor ∈ native.drain.config.defaulted ∧ _
  change event ∈ native.drain.config.cut.completed at completed
  by_cases ready : before.application.config.cut.Ready event
  · have same : native = before.application.completeFailure event ready := by
      cases node : nodeView (graph setup) event with
      | sample payload law outputEq codeEq =>
          rw [nodeView_sample_actor outputEq codeEq] at owned
          cases owned
      | bind owner payload outputEq codeEq =>
          rw [environmentStep_expire_bind_eq timeouts before.application event ready entered
            activated due owner payload outputEq codeEq node, PMF.mem_support_pure_iff] at moved
          simpa only [EventGraphRuntime.State.completeFailure, node] using moved
      | resolve owner payload binding checks outputEq codeEq =>
          rw [environmentStep_expire_resolve_eq timeouts before.application event ready entered
            activated due owner payload binding checks outputEq codeEq node,
            PMF.mem_support_pure_iff] at moved
          simpa only [EventGraphRuntime.State.completeFailure, node] using moved
    rw [same]
    refine ⟨?_, ?_⟩
    · rw [State.drain_defaulted]
      exact ((valid.completeFailure event ready actor owned).defaulted_zero actor).mpr
        ⟨event, owned, State.completeFailure_publicFailure _ valid.receipts event ready owned⟩
    · intro payload outputEq
      exact FieldRef.get?_preserved _ _ _
        ((before.application.completeFailure event ready).drain_store_of_some) _
        (completeFailure_publication_failed before.application event ready payload outputEq)
  · rw [environmentStep_expire_of_not_ready timeouts before.application event ready,
      PMF.mem_support_pure_iff] at moved
    subst native
    rw [before.application.drain_eq_of_clear facts.quiescent] at completed
    exact (unfinished completed).elim


private theorem ledger_transition {current next : (application setup timeouts leaks).Control}
    (joint : Player → Option (application setup timeouts leaks).Action)
    (realized : some next ∈ ((application setup timeouts leaks).transition (initialLaw setup)
      horizon
      scheduler (some current) joint).support) :
    ∀ message ∈ current.execution.network.ledger, message ∈ next.execution.network.ledger := by
  let app := application setup timeouts leaks
  cases acting : current.actor with
  | some actor =>
      rw [ReactiveApplication.transition, acting, PMF.mem_support_pure_iff]
        at realized
      cases Option.some.inj realized
      intro message member
      rw [app.respond_ledger]
      exact member
  | none =>
      have casesIdle : next.execution = current.execution ∨ ∃ command,
          next.execution ∈ (current.execution.environmentStep app command).support := by
        rcases current with ⟨remaining, actor, execution⟩
        cases acting
        cases remaining with
        | zero =>
            cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
            exact Or.inl rfl
        | succ remaining =>
            obtain ⟨command, _, moved⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
            obtain ⟨updated, supported, same⟩ := PMF.support_map .. ▸ moved
            cases Option.some.inj same
            exact Or.inr ⟨command, supported⟩
      rcases casesIdle with same | ⟨command, moved⟩
      · rw [same]; exact fun _ member => member
      · apply app.environmentStep_cases current.execution next.execution command moved
          (predicate := fun _ after => current.execution.network.ledger ⊆ after.network.ledger)
        · exact List.Subset.refl _
        · intros; exact List.Subset.refl _
        · intro id
          change current.execution.network.ledger ⊆
            (current.execution.includePending app id).network.ledger
          rw [app.includePending_network]
          cases found : current.execution.network.lookup id with
          | none =>
              simp only [MessageNetwork.includePending, found]
              exact List.Subset.refl _
          | some message =>
              simp only [MessageNetwork.includePending, found]
              exact List.subset_append_left _ _
        · intros; exact List.Subset.refl _

/-- Every completed owned event of an initialized native history has an owner packet
on the ledger or a publicly defaulted owner. In the latter case, a publication
output retains its exact failed value. -/
theorem completed_packet_or_defaulted : ∀ {state}
    (_ : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace state)
    (control : (application setup timeouts leaks).Control), state = some control →
    ∀ event ∈ control.execution.application.config.cut.completed, ∀ actor,
      (graph setup).actor? event = some actor →
      (∃ message ∈ control.execution.network.ledger, message.sender = actor ∧
        message.payload.call.event? (graph setup) = some event) ∨
      (actor ∈ control.execution.application.config.defaulted ∧ ∀ payload
        (outputEq : (graph setup).outputLayout event = .publication payload),
        (⟨.inr event, outputEq⟩ : FieldRef (graph setup).layout (.publication payload)).get?
          control.execution.application.config.store = some .failure)
  | _, .start, _, current => by cases current
  | _, .extend (source := before) prior joint _ realized, control, current => by
      have recursive := fun next same => completed_packet_or_defaulted prior next same
      subst current
      change some control ∈ ((application setup timeouts leaks).transition (initialLaw setup)
        horizon scheduler before joint).support at realized
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state => some
            (⟨horizon, none, ReactiveApplication.Execution.initial (application setup timeouts
              leaks)
              state⟩ : (application setup timeouts leaks).Control)).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          intro event completed
          exact (Finset.notMem_empty event completed).elim
      | some current =>
          intro event completed actor acts
          by_cases earlier : event ∈ current.execution.application.config.cut.completed
          · rcases recursive current rfl event earlier actor acts with
                ⟨message, onLedger, sender, named⟩ | inactive
            · exact Or.inl ⟨message, ledger_transition joint realized message onLedger,
                sender, named⟩
            · right
              refine ⟨(reactive_protocol_defaulted_mono timeouts) leaks (initialLaw setup)
                horizon scheduler current control joint realized inactive.1, ?_⟩
              intro payload outputEq
              exact FieldRef.get?_preserved _ _ _
                ((keepsStore_step timeouts leaks).transition (initialLaw setup) horizon scheduler
                  current control joint realized) _ (inactive.2 payload outputEq)
          · have idle : current.actor = none := by
              cases acting : current.actor with
              | none => rfl
              | some responder =>
                  exfalso
                  rw [ReactiveApplication.transition, acting, PMF.mem_support_pure_iff] at realized
                  cases Option.some.inj realized
                  apply earlier
                  simpa only [((reactive_respond_application timeouts) leaks current.execution
                    responder _).1] using completed
            have casesIdle : control.execution = current.execution ∨ ∃ command,
                control.execution ∈ (current.execution.environmentStep
                  (application setup timeouts leaks) command).support := by
              rcases current with ⟨remaining, actor, execution⟩
              cases idle
              cases remaining with
              | zero =>
                  cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp realized)
                  exact Or.inl rfl
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ realized)
                  obtain ⟨updated, supported, same⟩ := PMF.support_map .. ▸ moved
                  cases Option.some.inj same
                  exact Or.inr ⟨command, supported⟩
            rcases casesIdle with sameExecution | ⟨command, moved⟩
            · rw [sameExecution] at completed
              exact (earlier completed).elim
            obtain ⟨record, present, eventEq⟩ :=
              List.mem_map.mp ((control.execution.application.config.history_exact event).mpr
                completed)
            have fresh : record ∉ current.execution.application.config.history := by
              intro old
              apply earlier
              rw [← eventEq]
              exact (current.execution.application.config.history_exact record.event).mp
                (List.mem_map_of_mem (f := EventCompletion.event) old)
            subst event
            rcases owned_completion_cases current.execution control.execution command moved
                record fresh present acts with accepted | expired | automatic
            · obtain ⟨accepted⟩ := accepted
              exact Or.inl ⟨accepted.message, accepted.ledger, accepted.sender, accepted.named⟩
            · obtain ⟨commandEq, entered, activated, due, _action, _value, _expired, _recorded⟩ :=
                expired
              right
              have rawPrior := prior
              have idleTrace : ((application setup timeouts leaks).protocol (initialLaw setup)
                  horizon scheduler).Trace
                    (some ⟨current.remaining, none, current.execution⟩) := by
                rcases current with ⟨remaining, actor, execution⟩
                change actor = none at idle
                cases idle
                exact rawPrior
              rw [commandEq] at moved
              exact expired_owner_defaulted idleTrace record.event actor acts earlier completed
                entered activated due moved
            · obtain ⟨native, drained, freshNative, _, _, _, inactive⟩ := automatic
              right
              refine ⟨?_, ?_⟩
              · rw [← drained, State.drain_defaulted]
                exact inactive
              · intro payload outputEq
                rw [← drained]
                exact drain_publication_failed native record
                  freshNative (by rw [drained]; exact present) payload outputEq


end History

end Vegas
