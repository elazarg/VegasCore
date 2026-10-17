/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTail

/-! # Retirement of the actual survivor retry -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

private theorem survivor_eq (excluded : Finset Player) (nonempty : excluded.Nonempty)
    (owner : Player) (survives : owner ∉ excluded) :
    (if alice ∈ excluded then bob else alice) = owner := by
  classical
  obtain ⟨failed, failedMem⟩ := nonempty
  fin_cases owner <;> fin_cases failed <;> simp_all [alice, bob]

private theorem surviving_owner_unique (excluded : Finset Player)
    (nonempty : excluded.Nonempty) (first second : Player)
    (firstSurvives : first ∉ excluded) (secondSurvives : second ∉ excluded) : first = second := by
  classical
  obtain ⟨failed, failedMem⟩ := nonempty
  fin_cases first <;> fin_cases second <;> fin_cases failed <;> simp_all

private theorem binding_event_owner (event : graph.EventId)
    (inside : event ∈ commitmentPhase.events) :
    ∃ owner, graph.actor? event = some owner ∧ event = bindingEvent owner := by
  have interval := (RuntimePhase.mem_events commitmentPhase event).mp inside
  change 0 ≤ event.val ∧ event.val < 2 at interval
  change Fin 4 at event
  fin_cases event
  · exact ⟨alice, binding_actors.1, rfl⟩
  · exact ⟨bob, binding_actors.2, rfl⟩
  · change 0 ≤ 2 ∧ 2 < 2 at interval
    omega
  · change 0 ≤ 3 ∧ 3 < 2 at interval
    omega

private theorem retry_excluded_nonempty (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (retired : current.execution.application.attempt ≠ originalAttempt)
    (installed : current.execution.application.phases.head? = some commitmentPhase) :
    current.execution.application.current.excluded.Nonempty := by
  have budget := (phaseApplication_seedBudget runtime leaks).history initial horizon
    (family seeds) (by
      intro state supported
      rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
      subst state
      exact PhaseRuntimeState.initial_seedBudget plan originalInput) trace
  have positive : 0 < current.execution.application.generation := by
    by_contra notPositive
    have zero : current.execution.application.generation = 0 := by omega
    apply retired
    simp only [PhaseRuntimeState.attempt, installed, Option.map_some, Option.getD_some, zero]
    rfl
  exact Finset.card_pos.mp (lt_of_lt_of_le positive budget.current_generation)

/-- The survivor retry really leaves its full namespace at its expiry slot.
A second active owner is excluded by the original generation budget and actual
quiescent readiness, rather than supplied as a service hypothesis. -/
theorem retry_expiry_exits (seeds : Seeds) (before after : app.Control)
    (beforeTrace : (app.protocol initial horizon (family seeds)).Trace (some before))
    (afterTrace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (retired : before.execution.application.attempt ≠ originalAttempt)
    (installed : before.execution.application.phases.head? = some commitmentPhase)
    (index : tailIndex before.execution.environmentRecall
      (before.execution.observeEnvironment app) = 8)
    (moved : after.execution ∈ (before.execution.environmentStep app
      (.application (.expire (bindingEvent
        (survivor (before.execution.observeEnvironment app)))))).support) :
    before.execution.application.attempt ≠ after.execution.application.attempt := by
  classical
  intro same
  have beforeGeometry := raw_phase_geometry (family seeds) before beforeTrace
  have afterGeometry := raw_phase_geometry (family seeds) after afterTrace
  have valid := raw_native_valid (family seeds) before beforeTrace
  have excluded := retry_excluded_nonempty seeds before beforeTrace retired installed
  obtain ⟨event, inside, unfinished⟩ : ∃ event ∈ commitmentPhase.events,
      event ∉ before.execution.application.current.native.config.cut.completed := by
    by_contra absent
    apply beforeGeometry.2.1 commitmentPhase installed
    intro event inside
    by_contra unfinished
    exact absent ⟨event, inside, unfinished⟩
  obtain ⟨owner, actor, named⟩ := binding_event_owner event inside
  have requested := raw_phase_event_request (family seeds) before beforeTrace commitmentPhase
    installed (Or.inl rfl) event inside owner actor unfinished
  have chosen : survivor (before.execution.observeEnvironment app) = owner := by
    exact survivor_eq before.execution.application.current.excluded excluded owner
      requested.2.2.2.2
  rw [chosen, ← named] at moved
  have resolved := tail_expiry_resolves seeds before beforeTrace retired commitmentPhase installed
    (Or.inl rfl) owner event inside actor (Or.inl ⟨rfl, index⟩) after.execution moved
  obtain ⟨ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).environmentStep
    before.execution after.execution (.application (.expire event)) moved originalInput valid
      beforeGeometry.1.adjacent same
  have completed : event ∈ after.execution.application.current.native.config.cut.completed := by
    rcases resolved with generation | phase | ⟨_same, done⟩
    · rw [← same] at generation
      dsimp only at generation
      omega
    · rw [← same] at phase
      dsimp only at phase
      omega
    · exact done
  have phases := raw_same_attempt_phases (family seeds) before after beforeTrace afterTrace same
  have installedAfter : after.execution.application.phases.head? = some commitmentPhase := by
    rw [← phases]
    exact installed
  apply afterGeometry.2.1 commitmentPhase installedAfter
  intro other otherInside
  by_cases done : other ∈ before.execution.application.current.native.config.cut.completed
  · exact progress.completed done
  · obtain ⟨otherOwner, otherActor, otherNamed⟩ := binding_event_owner other otherInside
    have otherRequest := raw_phase_event_request (family seeds) before beforeTrace commitmentPhase
      installed (Or.inl rfl) other otherInside otherOwner otherActor done
    have sameOwner := surviving_owner_unique before.execution.application.current.excluded excluded
      owner otherOwner requested.2.2.2.2 otherRequest.2.2.2.2
    have sameEvent : other = event := by rw [otherNamed, ← sameOwner, ← named]
    rw [sameEvent]
    exact completed

/-- No actual raw history remains in a nonoriginal commitment block after
its nine scheduler decisions. Player responses are arbitrary throughout. -/
theorem retry_index_bound (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current =>
        current.execution.application.attempt ≠ originalAttempt →
        current.execution.application.phases.head? = some commitmentPhase →
        tailIndex current.execution.environmentRecall (current.execution.observeEnvironment app) <
          9) := by
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      have targetTrace := prior.extend joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
          subst state
          intro impossible
          exact (impossible initialState_attempt).elim
      | some current =>
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some owner =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              let action := (joint owner).getD (⟨none⟩ : app.Action)
              have same : (execution.respond app owner action).application.attempt =
                  execution.application.attempt := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              have phases : (execution.respond app owner action).application.phases =
                  execution.application.phases := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              intro retired installed
              have beforeRetired : execution.application.attempt ≠ originalAttempt := by
                rw [same] at retired
                exact retired
              have beforeInstalled : execution.application.phases.head? = some commitmentPhase := by
                rw [phases] at installed
                exact installed
              have index := ih beforeRetired beforeInstalled
              rw [app.respond_environmentRecall,
                tailIndex_congr_attempt _ _ (execution.observeEnvironment app) same]
              exact index
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro retired installed
                  by_cases same : execution.application.attempt = next.application.attempt
                  · have phases := raw_same_attempt_phases (family seeds)
                      ⟨remaining + 1, none, execution⟩ _ prior targetTrace same
                    have beforeRetired : execution.application.attempt ≠ originalAttempt :=
                      fun original => retired (same.symm.trans original)
                    have beforeInstalled : execution.application.phases.head? =
                        some commitmentPhase := by
                      rw [phases]
                      exact installed
                    have index := ih beforeRetired beforeInstalled
                    change tailIndex execution.environmentRecall
                      (execution.observeEnvironment app) < 9 at index
                    change tailIndex next.environmentRecall (next.observeEnvironment app) < 9
                    have afterIndex := tailIndex_after_same_attempt execution next command
                      supported same.symm
                    by_cases earlier : tailIndex execution.environmentRecall
                        (execution.observeEnvironment app) < 8
                    · omega
                    · have last : tailIndex execution.environmentRecall
                          (execution.observeEnvironment app) = 8 := by omega
                      have chosen : command = .application (.expire (bindingEvent
                          (survivor (execution.observeEnvironment app)))) := by
                        have selectedEq : command = choose seeds execution.environmentRecall
                            (execution.observeEnvironment app) :=
                          (PMF.mem_support_pure_iff _ _).mp selected
                        have retiredView : (execution.observeEnvironment app).application.attempt ≠
                            originalAttempt := beforeRetired
                        have phaseView : (execution.observeEnvironment app).application.phase =
                            some (.commitment, commitmentPhase.low, commitmentPhase.high) := by
                          change execution.application.phases.head?.map
                            (fun phase => (phase.kind, phase.low, phase.high)) = _
                          rw [beforeInstalled]
                          rfl
                        rw [selectedEq, choose, ite_eq_right retiredView, phaseView]
                        rw [last]
                        rfl
                      rw [chosen] at supported
                      exact (retry_expiry_exits seeds ⟨remaining + 1, none, execution⟩ _ prior
                        targetTrace beforeRetired beforeInstalled last supported same).elim
                  · have reset := tailIndex_after_retirement seeds
                      ⟨remaining + 1, none, execution⟩ prior next command supported same
                    rw [reset]
                    decide

end Vegas.Examples.CommitSeedSignalling
