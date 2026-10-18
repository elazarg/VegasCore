/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastTail

/-! # Completion of both actual concurrent publication deadlines -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

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

/-- Each original tail deadline remains completed through the same full
namespace, for both the retry and the publication block. -/
private theorem tail_event_expired_history (seeds : Seeds) (owner : Player)
    (phase : RuntimePhase graph) (event : graph.EventId)
    (position : (phase = commitmentPhase ∧ event = bindingEvent owner) ∨
      (phase = publicationPhase ∧ event = revealEvent owner))
    (actor : graph.actor? event = some owner) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current =>
        current.execution.application.attempt ≠ originalAttempt →
        current.execution.application.phases.head? = some phase →
        13 + owner.val ≤ tailIndex current.execution.environmentRecall
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
          rw [initial, PMF.mem_support_pure_iff] at supported
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
                  execution.application.phases.head? = some phase := by
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
                  change 13 + owner.val ≤ tailIndex next.environmentRecall
                    (next.observeEnvironment app) at enough
                  by_cases same : execution.application.attempt = next.application.attempt
                  · have phases := raw_same_attempt_phases (family seeds)
                      ⟨remaining + 1, none, execution⟩ _ prior targetTrace same
                    have beforeRetired : execution.application.attempt ≠ originalAttempt :=
                      fun original => retired (same.symm.trans original)
                    have beforeInstalled : execution.application.phases.head? =
                        some phase := by
                      rw [phases]
                      exact installed
                    have index := tailIndex_after_same_attempt execution next command supported
                      same.symm
                    obtain ⟨_ticks, progress⟩ :=
                      (phaseApplication_serviceProgress runtime leaks).environmentStep
                        execution next command supported originalInput valid ordered same
                    by_cases earlier : 13 + owner.val ≤ tailIndex execution.environmentRecall
                        (execution.observeEnvironment app)
                    · exact progress.completed (ih beforeRetired beforeInstalled earlier)
                    · have last : tailIndex execution.environmentRecall
                          (execution.observeEnvironment app) = 12 + owner.val := by omega
                      have chosen : command = .application (.expire event) := by
                        have selectedEq : command = choose seeds execution.environmentRecall
                            (execution.observeEnvironment app) :=
                          (PMF.mem_support_pure_iff _ _).mp selected
                        have viewPhase : (execution.observeEnvironment app).application.phase =
                            some (phase.kind, phase.low, phase.high) := by
                          change execution.application.phases.head?.map
                            (fun phase => (phase.kind, phase.low, phase.high)) = _
                          rw [beforeInstalled]
                          rfl
                        change command = _ at selectedEq
                        have retiredView : (execution.observeEnvironment app).application.attempt ≠
                            originalAttempt := beforeRetired
                        rw [selectedEq, choose, ite_eq_right retiredView, viewPhase, last]
                        rcases position with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        all_goals fin_cases owner <;> rfl
                      rw [chosen] at supported
                      have inside : event ∈ phase.events := by
                        rcases position with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                        · exact (RuntimePhase.mem_events commitmentPhase _).mpr
                            ⟨Nat.zero_le _, owner.isLt⟩
                        · apply (RuntimePhase.mem_events publicationPhase _).mpr
                          change 3 ≤ owner.val + 3 ∧ owner.val + 3 < 6
                          have bound := owner.isLt
                          omega
                      have block : phase = commitmentPhase ∨ phase = publicationPhase :=
                        position.elim (fun row => Or.inl row.1) (fun row => Or.inr row.1)
                      have resolved := tail_expiry_resolves seeds
                        ⟨remaining + 1, none, execution⟩ prior beforeRetired phase beforeInstalled
                        block owner event inside actor (by
                          change 12 ≤ tailIndex execution.environmentRecall
                            (execution.observeEnvironment app)
                          omega) next supported
                      exact resolved_same_event ⟨execution.application.attempt, event⟩
                        next.application same resolved
                  · have reset := tailIndex_after_retirement seeds
                      ⟨remaining + 1, none, execution⟩ prior next command supported same
                    rw [reset] at enough
                    omega

/-- A genuine nonoriginal phase cannot retain fifteen completed command slots. -/
theorem tail_index_bound (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (retired : current.execution.application.attempt ≠ originalAttempt)
    (phase : RuntimePhase graph)
    (installed : current.execution.application.phases.head? = some phase)
    (block : phase = commitmentPhase ∨ phase = publicationPhase) :
    tailIndex current.execution.environmentRecall (current.execution.observeEnvironment app) <
      15 := by
  by_contra enough
  have geometry := raw_phase_geometry (family seeds) current trace
  apply geometry.2.1 phase installed
  intro event inside
  have interval := (RuntimePhase.mem_events phase event).mp inside
  rcases block with rfl | rfl
  · change 0 ≤ event.val ∧ event.val < 3 at interval
    let owner : Player := ⟨event.val, interval.2⟩
    have named : event = bindingEvent owner := Fin.ext rfl
    rw [named]
    have bound := owner.isLt
    exact tail_event_expired_history seeds owner commitmentPhase (bindingEvent owner)
      (Or.inl ⟨rfl, rfl⟩) (binding_actor owner) trace retired installed (by omega)
  · change 3 ≤ event.val ∧ event.val < 6 at interval
    let owner : Player := ⟨event.val - 3, by omega⟩
    have named : event = revealEvent owner := by
      apply Fin.ext
      change event.val = event.val - 3 + 3
      omega
    rw [named]
    have bound := owner.isLt
    exact tail_event_expired_history seeds owner publicationPhase (revealEvent owner)
      (Or.inr ⟨rfl, rfl⟩) (reveal_actor owner) trace retired installed (by omega)

end Vegas.Examples.CommitSeedBroadcast
