/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingCompletion

/-! # Completion of both actual concurrent publication deadlines -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private abbrev originalInput : graph.Inputs :=
  encodeInputs (Env.empty (CellVal simpleExpr))

private theorem resolved_same_event (coordinate : CommitAttemptEvent graph)
    (state : PhaseRuntimeState graph) (same : coordinate.attempt = state.attempt)
    (resolved : coordinate.Resolved state) :
    coordinate.event ∈ state.current.native.config.cut.completed := by
  rcases resolved with generation | phase | ⟨_same, completed⟩
  · rw [same] at generation
    omega
  · rw [same] at phase
    omega
  · exact completed

/-- A publication remains completed after its actual expiry slot, throughout
the same full namespace. Namespace retirement restarts the command index. -/
theorem publication_expired_history (seeds : Seeds) (owner : Player)
    (event : graph.EventId) (expiryPosition : Nat)
    (position : (event = aliceReveal ∧ expiryPosition = 10) ∨
      (event = bobReveal ∧ expiryPosition = 11))
    (actor : graph.actor? event = some owner) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current =>
        current.execution.application.attempt ≠ originalAttempt →
        current.execution.application.phases.head? = some publicationPhase →
        expiryPosition + 1 ≤ tailIndex current.execution.environmentRecall
          (current.execution.observeEnvironment app) →
        event ∈ current.execution.application.current.native.config.cut.completed) := by
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
          have valid := raw_native_valid (family seeds) ⟨remaining, active, execution⟩ prior
          have geometry := raw_phase_geometry (family seeds) ⟨remaining, active, execution⟩ prior
          have ordered : execution.application.Ordered := geometry.1.adjacent
          cases active with
          | some owner =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              let action := (joint owner).getD (⟨none⟩ : app.Action)
              let after := execution.respond app owner action
              have same : execution.application.attempt = after.application.attempt := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              have phases : execution.application.phases = after.application.phases := by
                rcases action with ⟨submission⟩
                cases submission <;> rfl
              intro retired installed enough
              have beforeRetired : execution.application.attempt ≠ originalAttempt :=
                fun original => retired (same.symm.trans original)
              have beforeInstalled :
                  execution.application.phases.head? = some publicationPhase := by
                rw [phases]
                exact installed
              have index : tailIndex after.environmentRecall (after.observeEnvironment app) =
                  tailIndex execution.environmentRecall (execution.observeEnvironment app) := by
                rw [app.respond_environmentRecall]
                exact tailIndex_congr_attempt _ _ _ same.symm
              rw [index] at enough
              have done := ih beforeRetired beforeInstalled enough
              obtain ⟨_ticks, progress⟩ := (phaseApplication_serviceProgress runtime leaks).respond
                execution owner action originalInput valid ordered same
              exact progress.completed done
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  intro retired installed enough
                  change expiryPosition + 1 ≤ tailIndex next.environmentRecall
                    (next.observeEnvironment app) at enough
                  by_cases same : execution.application.attempt = next.application.attempt
                  · have phases := raw_same_attempt_phases (family seeds)
                      ⟨remaining + 1, none, execution⟩ _ prior targetTrace same
                    have beforeRetired : execution.application.attempt ≠ originalAttempt :=
                      fun original => retired (same.symm.trans original)
                    have beforeInstalled : execution.application.phases.head? =
                        some publicationPhase := by
                      rw [phases]
                      exact installed
                    have index := tailIndex_after_same_attempt execution next command supported
                      same.symm
                    obtain ⟨_ticks, progress⟩ :=
                      (phaseApplication_serviceProgress runtime leaks).environmentStep
                        execution next command supported originalInput valid ordered same
                    by_cases earlier : expiryPosition + 1 ≤ tailIndex execution.environmentRecall
                        (execution.observeEnvironment app)
                    · exact progress.completed (ih beforeRetired beforeInstalled earlier)
                    · have last : tailIndex execution.environmentRecall
                          (execution.observeEnvironment app) = expiryPosition := by omega
                      have chosen : command = .application (.expire event) := by
                        have selectedEq : command = choose seeds execution.environmentRecall
                            (execution.observeEnvironment app) :=
                          (PMF.mem_support_pure_iff _ _).mp selected
                        have viewPhase : (execution.observeEnvironment app).application.phase =
                            some (.reveal, publicationPhase.low, publicationPhase.high) := by
                          change execution.application.phases.head?.map
                            (fun phase => (phase.kind, phase.low, phase.high)) = _
                          rw [beforeInstalled]
                          rfl
                        rw [selectedEq, choose_reveal seeds execution.environmentRecall
                          (execution.observeEnvironment app) beforeRetired
                          ⟨publicationPhase.low, publicationPhase.high, viewPhase⟩, last]
                        rcases position with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rfl
                      rw [chosen] at supported
                      have inside : event ∈ publicationPhase.events := by
                        rcases position with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> decide
                      have resolved := tail_expiry_resolves seeds
                        ⟨remaining + 1, none, execution⟩ prior beforeRetired publicationPhase
                        beforeInstalled (Or.inr rfl) owner event inside actor
                        (Or.inr ⟨rfl, position.elim
                          (fun row => Or.inl (last.trans row.2))
                          (fun row => Or.inr (last.trans row.2))⟩) next supported
                      exact resolved_same_event ⟨execution.application.attempt, event⟩
                        next.application same resolved
                  · have reset := tailIndex_after_retirement seeds
                      ⟨remaining + 1, none, execution⟩ prior next command supported same
                    rw [reset] at enough
                    rcases position with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> omega

/-- The actual reveal routine has left its namespace after twelve commands,
including when a raw opening fails and automatically drains another event. -/
theorem publication_index_bound (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (retired : current.execution.application.attempt ≠ originalAttempt)
    (installed : current.execution.application.phases.head? = some publicationPhase) :
    tailIndex current.execution.environmentRecall (current.execution.observeEnvironment app) <
      12 := by
  by_contra enough
  have firstDone := publication_expired_history seeds alice aliceReveal 10
    (Or.inl ⟨rfl, rfl⟩) reveal_actors.1 trace retired installed (by omega)
  have secondDone := publication_expired_history seeds bob bobReveal 11
    (Or.inr ⟨rfl, rfl⟩) reveal_actors.2 trace retired installed (by omega)
  have geometry := raw_phase_geometry (family seeds) current trace
  apply geometry.2.1 publicationPhase installed
  intro event inside
  have interval := (RuntimePhase.mem_events publicationPhase event).mp inside
  change 2 ≤ event.val ∧ event.val < 4 at interval
  change Fin 4 at event
  fin_cases event
  · change 2 ≤ 0 ∧ 0 < 4 at interval
    omega
  · change 2 ≤ 1 ∧ 1 < 4 at interval
    omega
  · exact firstDone
  · exact secondDone

end Vegas.Examples.CommitSeedSignalling
