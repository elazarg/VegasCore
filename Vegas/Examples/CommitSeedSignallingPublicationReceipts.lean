/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalReceipts
import Vegas.Examples.CommitSeedSignallingOpeningTransfer
import Vegas.Pending.EventResolutionEnvironment
import Vegas.Pending.PhaseStoredCheckpoint
import Vegas.Pending.ExclusionAcceptedOutput
import Interaction.ReactiveRoundBoundary

/-! # Successful publications retain the original binding receipt -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem no_publication_success_iff (native : EventGraphRuntime.State graph)
    (owner : Player) :
    (¬ OutputSucceeded native.config.store (revealEvent owner)) ↔
      ∀ value : Bool,
        cast (congrArg Option (congrArg EventField.Value (revealEvent_layout owner)))
          (native.config.outputs (revealEvent owner)) ≠ some (.success value) := by
  fin_cases owner
  all_goals first
    | change (¬ ∃ result : PublicationResult Bool,
        native.config.outputs aliceReveal = some result ∧ result ≠ .failure) ↔ _
    | change (¬ ∃ result : PublicationResult Bool,
        native.config.outputs bobReveal = some result ∧ result ≠ .failure) ↔ _
  all_goals
    constructor
    · intro absent value read
      exact absent ⟨.success value, read, by intro impossible; cases impossible⟩
    · intro absent ⟨result, read, good⟩
      cases result with
      | failure => exact good rfl
      | success value => exact absent value read

private theorem complete_failure_no_publication_success
    (native : EventGraphRuntime.State graph) (event : graph.EventId)
    (ready : native.config.cut.Ready event) (owner : Player)
    (before : ¬ OutputSucceeded native.config.store (revealEvent owner)) :
    ¬ OutputSucceeded (native.completeFailure event ready).config.store (revealEvent owner) := by
  by_cases same : event = revealEvent owner
  · subst event
    fin_cases owner
    all_goals
      change ¬ ∃ result : PublicationResult Bool,
        some PublicationResult.failure = some result ∧ result ≠ .failure
      rintro ⟨result, equal, good⟩
      exact good (Option.some.inj equal).symm
  · rintro ⟨result, read, good⟩
    have output : (native.completeFailure event ready).config.outputs (revealEvent owner) =
        native.config.outputs (revealEvent owner) := by
      cases viewed : nodeView graph event <;>
        simp only [State.completeFailure, viewed, State.complete,
          Config.complete_output_of_ne _ _ _ _ _ _ (Ne.symm same)]
    have retained : native.config.outputs (revealEvent owner) = some result :=
      output.symm.trans read
    exact before ⟨result, retained, good⟩

private theorem drain_no_publication_success (phase : RuntimePhase graph)
    (state : RecoveryState graph) (owner : Player)
    (before : ¬ OutputSucceeded state.native.config.store (revealEvent owner)) :
    ¬ OutputSucceeded (phase.drain state).native.config.store (revealEvent owner) := by
  have fuel : ∀ count (current : RecoveryState graph),
      (¬ OutputSucceeded current.native.config.store (revealEvent owner)) →
        ¬ OutputSucceeded (phase.drainFuel count current).native.config.store
          (revealEvent owner) := by
    intro count
    induction count with
    | zero => exact fun _ absent => absent
    | succ count induction =>
        intro current absent
        unfold RuntimePhase.drainFuel
        split
        · apply induction
          exact complete_failure_no_publication_success current.native _ _ owner absent
        · exact absent
  exact fuel _ state before

private theorem settle_no_publication_success
    (phases : List (RuntimePhase graph)) (generation : Nat) (entry current : RecoveryState graph)
    (retired : List (RetiredCommitAttempt graph)) (owner : Player)
    (saved : ¬ OutputSucceeded entry.native.config.store (revealEvent owner))
    (active : ¬ OutputSucceeded current.native.config.store (revealEvent owner)) :
    ¬ OutputSucceeded
      (PhaseRuntimeState.settle phases generation entry current retired).current.native.config.store
        (revealEvent owner) := by
  induction phases generalizing generation entry current retired with
  | nil => exact active
  | cons phase remaining induction =>
      have drained := drain_no_publication_success phase current owner active
      have rebuilt := drain_no_publication_success phase
        (PhaseRuntimeState.restore entry (phase.drain current)) owner saved
      simp only [PhaseRuntimeState.settle]
      split
      · split
        · split
          · exact rebuilt
          · exact induction _ _ _ _ rebuilt rebuilt
        · exact induction _ _ _ _ drained drained
      · exact drained

private theorem environment_no_publication_success
    (state next : PhaseRuntimeState graph) (command : EnvironmentCommand graph) (owner : Player)
    (stored : state.StoredCheckpoint)
    (before : ¬ OutputSucceeded state.current.native.config.store (revealEvent owner))
    (moved : next ∈ (state.environment runtime command).support) :
    ¬ OutputSucceeded next.current.native.config.store (revealEvent owner) := by
  classical
  have saved : ¬ OutputSucceeded state.entry.native.config.store (revealEvent owner) :=
    fun success => before (success.mono stored)
  unfold PhaseRuntimeState.environment at moved
  split at moved
  · obtain ⟨native, stepped, rfl⟩ := PMF.support_map .. ▸ moved
    have absent : ¬ OutputSucceeded native.config.store (revealEvent owner) := by
      apply (no_publication_success_iff native owner).mpr
      fin_cases owner
      · exact environmentStep_resolution_no_success runtime state.current.native native
          aliceReveal alice .bool _ _ rfl rfl rfl command
            ((no_publication_success_iff state.current.native alice).mp before) stepped
      · exact environmentStep_resolution_no_success runtime state.current.native native
          bobReveal bob .bool _ _ rfl rfl rfl command
            ((no_publication_success_iff state.current.native bob).mp before) stepped
    exact settle_no_publication_success state.phases state.generation state.entry
      (state.current.environmentResult command native) state.retired owner saved absent
  · cases (PMF.mem_support_pure_iff _ _).mp moved
    exact before

private theorem initial_no_publication_success (owner : Player) :
    ¬ OutputSucceeded initialExecution.application.current.native.config.store
      (revealEvent owner) := by
  change ¬ OutputSucceeded initialState.current.native.config.store (revealEvent owner)
  rw [initialState_eq]
  rintro ⟨result, read, _good⟩
  change none = some result at read
  cases read

private theorem respond_no_publication_success (execution : app.Execution)
    (actor owner : Player) (action : app.Action)
    (before : ¬ OutputSucceeded execution.application.current.native.config.store
      (revealEvent owner)) :
    ¬ OutputSucceeded (execution.respond app actor action).application.current.native.config.store
      (revealEvent owner) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact before
  | some material =>
      change ¬ OutputSucceeded
        (submitStep (material.call.register execution.application.current.native actor) actor
          material.call.packet).config.store (revealEvent owner)
      rw [submitStep_config, (material.call.register_facts actor
        execution.application.current.native).1]
      exact before

private theorem successful_inclusion_finished_owner
    (control : app.Control) (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (next : PhaseRuntimeState graph)
    (handled : app.handle control.execution.application message = some next)
    (before : ¬ OutputSucceeded control.execution.application.current.native.config.store
      (revealEvent owner))
    (after : OutputSucceeded next.current.native.config.store (revealEvent owner)) :
    next.phases <:+ [publicationPhase] ∧
      (∀ event, graph.actor? event = some owner →
        event ∈ next.current.native.config.cut.completed) ∧ owner ∉ next.current.excluded := by
  classical
  have saved := phaseStoredCheckpoint_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler trace
  have savedAbsent : ¬ OutputSucceeded control.execution.application.entry.native.config.store
      (revealEvent owner) := fun success => before (success.mono saved)
  change control.execution.application.handle runtime message = some next at handled
  unfold PhaseRuntimeState.handle at handled
  split at handled
  · rename_i permitted
    obtain ⟨native, accepted, normalized⟩ := Option.map_eq_some_iff.mp handled
    have success : OutputSucceeded native.config.store (revealEvent owner) := by
      by_contra absent
      apply settle_no_publication_success control.execution.application.phases
        control.execution.application.generation control.execution.application.entry
        (control.execution.application.current.inclusionResult message.payload.packet.call native)
        control.execution.application.retired owner savedAbsent absent
      rw [← normalized] at after
      exact after
    obtain ⟨event, addressed, ready, action, stepped⟩ := handle_config_mem_step runtime
      control.execution.application.current.native native
        ⟨message.id, message.payload.packet.call⟩ accepted
    have named : event = revealEvent owner := by
      by_contra different
      rw [Config.step, PMF.support_map] at stepped
      obtain ⟨value, _legal, equal⟩ := stepped
      obtain ⟨result, read, good⟩ := success
      have unchanged := control.execution.application.current.native.config.complete_output_of_ne
        event (revealEvent owner) ready action value (Ne.symm different)
      have changedRead : (control.execution.application.current.native.config.complete
          event ready action value).outputs (revealEvent owner) = some result := equal ▸ read
      exact before ⟨result, unchanged.symm.trans changedRead, good⟩
    subst event
    have predecessors : graph.order.predecessors (revealEvent owner) =
        {aliceBinding, bobBinding} := by
      fin_cases owner
      · exact reveal_predecessors.1
      · exact reveal_predecessors.2
    have aliceDone : aliceBinding ∈
        control.execution.application.current.native.config.cut.completed :=
      ready.2 (by rw [predecessors]; exact Finset.mem_insert_self _ _)
    have bobDone : bobBinding ∈
        control.execution.application.current.native.config.cut.completed :=
      ready.2 (by rw [predecessors]
                  exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    have tail := completed_bindings_publication_tail scheduler control trace aliceDone bobDone
    have nativeKeeps : KeepsStore native next.current.native := by
      rw [← normalized]
      exact settle_publication_keepsStore control.execution.application.phases
        control.execution.application.generation control.execution.application.entry
        (control.execution.application.current.inclusionResult message.payload.packet.call native)
        control.execution.application.retired tail
    have nextTail : next.phases <:+ [publicationPhase] := by
      rw [← normalized]
      exact (PhaseRuntimeState.settle_suffix _ _ _ _ _).trans tail
    obtain ⟨result, read, _good⟩ := success
    change native.config.outputs (revealEvent owner) = some result at read
    have completed : revealEvent owner ∈ native.config.cut.completed :=
      (native.config.output_available (revealEvent owner)).mp (by rw [read]; rfl)
    have finished : ∀ event, graph.actor? event = some owner →
        event ∈ next.current.native.config.cut.completed := by
      intro event acting
      exact completed_of_keepsStore native next.current.native nativeKeeps event
        (own_events_completed_of_reveal native.config owner completed event acting)
    have notExcluded : control.execution.application.current.excludedCall
        message.payload.packet.call = false := by
      have parts := Bool.and_eq_true_iff.mp permitted
      exact Bool.eq_false_of_not_eq_true' parts.2
    have acting : graph.actor? (revealEvent owner) = some owner := by
      fin_cases owner <;> rfl
    have active : owner ∉ control.execution.application.current.excluded := by
      have encoded : decide (owner ∈ control.execution.application.current.excluded) = false := by
        simpa only [RecoveryState.excludedCall, addressed, RecoveryState.excludedEvent,
          acting, Option.any_some] using notExcluded
      exact of_decide_eq_false encoded
    have valid := (phaseBindingRecord_history runtime leaks plan
      (setup.initialLaw.map encodeInputs) horizon scheduler trace).active
    have nativeValid := handle_bindingInvariant runtime
      control.execution.application.current.native native
      ⟨message.id, message.payload.packet.call⟩ valid accepted
    have noFailure := (show OutputSucceeded native.config.store (revealEvent owner) from
      ⟨result, read, _good⟩).not_publicFailure nativeValid
    have nextActive : owner ∉ next.current.excluded := by
      rw [← normalized, PhaseRuntimeState.normalize]
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
      cases call : message.payload.packet.call with
      | commitment event candidate => exact active
      | malformed _raw => exact active
      | opening event candidate raw =>
          have same : event = revealEvent owner := by
            simpa only [call, Payload.event?, Option.some.injEq] using addressed
          subst event
          have failed : RecoveryState.publicationFailed native (revealEvent owner) = false := by
            cases flag : RecoveryState.publicationFailed native (revealEvent owner) with
            | false => rfl
            | true => exact (noFailure (Or.inr flag)).elim
          simpa only [call, RecoveryState.inclusionResult, failed, Bool.false_eq_true,
            ite_false] using active
    exact ⟨nextTail, finished, nextActive⟩
  · cases handled

/-- A successful final publication is traced to its first actual successful
inclusion. Automatic closure and expiry cannot create that success. -/
theorem initialized_successful_publication_survives (players : Player → app.Policy)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler players horizon initialExecution).support)
    (owner : Player)
    (success : OutputSucceeded final.application.current.native.config.store (revealEvent owner)) :
    owner ∉ final.application.current.excluded := by
  classical
  let absent : app.Execution → Prop := fun execution =>
    ¬ OutputSucceeded execution.application.current.native.config.store (revealEvent owner)
  obtain ⟨used, remaining, prior, middle, resumed, command, budget, priorReached, before,
      _selected, moved, after, resumedSupport, continued⟩ :=
    app.runRounds_environment_boundary scheduler players absent
      (fun execution actor action no => respond_no_publication_success execution actor owner
        action no) horizon initialExecution final (initial_no_publication_success owner) reached
          (fun no => no success)
  have rounds : prior ∈ (app.roundsFrom initial scheduler players used).support := by
    simpa only [ReactiveApplication.roundsFrom, initial_eq_pure, PMF.pure_bind,
      initialExecution] using priorReached
  obtain ⟨priorTrace⟩ := app.raw_trace_roundsFrom initial horizon scheduler players used
    (by omega) prior rounds
  have stored := phaseStoredCheckpoint_history runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon scheduler priorTrace
  have afterSuccess : OutputSucceeded middle.application.current.native.config.store
      (revealEvent owner) := Classical.not_not.mp after
  cases command with
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      exact (before afterSuccess).elim
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      obtain ⟨sample, _possible, rfl⟩ := PMF.support_map .. ▸ supported
      exact (before afterSuccess).elim
  | application operation =>
      obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
      change updated ∈ ((app.environment prior.application operation).map
        (fun state => {prior with application := state})).support at supported
      obtain ⟨state, stateSupport, rfl⟩ := PMF.support_map .. ▸ supported
      exact (environment_no_publication_success prior.application state operation owner stored
        before stateSupport afterSuccess).elim
  | «include» identifier =>
      simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      cases found : prior.network.lookup identifier with
      | none =>
          simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
            found] at afterSuccess
          exact (before afterSuccess).elim
      | some message =>
          cases handled : app.handle prior.application message with
          | none =>
              simp only [ReactiveApplication.Execution.includePending,
                MessageNetwork.includePending, found, handled, Option.getD_none] at afterSuccess
              exact (before afterSuccess).elim
          | some next =>
              have application : (prior.includePending app identifier).application = next := by
                simp only [ReactiveApplication.Execution.includePending,
                  MessageNetwork.includePending, found, handled, Option.getD_some]
              have finished := successful_inclusion_finished_owner
                ⟨horizon - used, none, prior⟩ priorTrace owner message next handled before
                  (application ▸ afterSuccess)
              let included : app.Execution :=
                {prior.includePending app identifier with environmentRecall :=
                  prior.environmentRecall ++
                    [⟨prior.observeEnvironment app, .include identifier⟩]}
              change resumed ∈ (PMF.pure included).support at resumedSupport
              have resumedEq := (PMF.mem_support_pure_iff _ _).mp resumedSupport
              subst resumed
              apply finished_owner_run_survives scheduler players remaining included final owner
              · simpa only [included, application] using finished.1
              · simpa only [included, application] using finished.2.1
              · simpa only [included, application] using finished.2.2
              · exact continued

/-- A missing original receipt forces the actual terminal failed-publication
bit. Permanent exclusion is not substituted for that semantic readout. -/
theorem initialized_missing_original_binding_publication_failed
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds scheduler players horizon initialExecution).support)
    (complete : final.application.current.native.config.cut.Terminal) (owner : Player)
    (missing : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      final) :
    RecoveryState.publicationFailed final.application.current.native (revealEvent owner) =
      true := by
  classical
  by_contra notFailed
  have success : OutputSucceeded final.application.current.native.config.store
      (revealEvent owner) := by
    have available := (final.application.current.native.config.output_available
      (revealEvent owner)).mpr (by rw [complete]; exact Finset.mem_univ _)
    obtain ⟨result, read⟩ := Option.isSome_iff_exists.mp available
    refine ⟨result, read, ?_⟩
    intro failed
    fin_cases owner
    all_goals
      change result = PublicationResult.failure at failed
      subst result
      apply notFailed
    · change RecoveryState.publicationFailed final.application.current.native aliceReveal = true
      change final.application.current.native.config.outputs aliceReveal =
          some PublicationResult.failure at read
      cases node : nodeView graph aliceReveal with
      | bind author payload kind code => cases kind.symm.trans reveal_layouts.1
      | sample payload law kind code => cases kind.symm.trans reveal_layouts.1
      | resolve author payload binding checks kind code =>
          have same := EventField.publication.inj (kind.symm.trans reveal_layouts.1)
          subst payload
          rw [RecoveryState.publicationFailed, node, read]
          rfl
    · change RecoveryState.publicationFailed final.application.current.native bobReveal = true
      change final.application.current.native.config.outputs bobReveal =
          some PublicationResult.failure at read
      cases node : nodeView graph bobReveal with
      | bind author payload kind code => cases kind.symm.trans reveal_layouts.2
      | sample payload law kind code => cases kind.symm.trans reveal_layouts.2
      | resolve author payload binding checks kind code =>
          have same := EventField.publication.inj (kind.symm.trans reveal_layouts.2)
          subst payload
          rw [RecoveryState.publicationFailed, node, read]
          rfl
  have surviving := initialized_successful_publication_survives players final reached owner success
  exact missing (initialized_survivor_original_binding_accepted players final reached owner
    surviving)

end Vegas.Examples.CommitSeedSignalling
