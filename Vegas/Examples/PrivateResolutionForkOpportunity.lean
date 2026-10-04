/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PrivateResolutionForkCompletionBounds

/-! # Actual owner service in the public resolution fork

Every current ready owner has a recorded activation from that readiness
episode before its delay is overdue. The proof covers all initialized raw
responses and derives the recorded public witness from actual command support.
-/

noncomputable section

namespace Vegas.PrivateResolutionFork

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory.Protocol

def opportunityEnd (event : nativeGraph.EventId) : Nat :=
  if event = aliceResolution then 3 else if event = bobResolution then 11 else 1

def opportunityWitnessInvariant : app.ProtocolState → Prop
  | none => True
  | some control => ∀ event owner entered, nativeGraph.actor? event = some owner →
      control.execution.application.config.cut.Ready event →
      control.execution.application.activatedAt event = some entered →
      opportunityEnd event ≤ control.execution.environmentRecall.length →
      OwnerActivatedSince (runtime setup) leaks control.execution.environmentRecall event
        owner entered

private theorem opportunity_ready_before (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (next : app.Execution) (command : app.Command)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (query : nativeGraph.EventId) (owner : Player)
    (owned : nativeGraph.actor? query = some owner)
    (ready : next.application.config.cut.Ready query)
    (visited : opportunityEnd query ≤ next.environmentRecall.length) :
    control.execution.application.config.cut.Ready query ∧
      next.application.activatedAt = control.execution.application.activatedAt := by
  rcases environment_graph_or_tick control.execution next command moved with
    ⟨_, same, entered, _⟩ | graphStep
  · exact ⟨same ▸ ready, entered⟩
  rcases graphStep with ⟨same, _, entered⟩ | ⟨event, current, action, supported, _, _⟩
  · exact ⟨same ▸ ready, entered⟩
  obtain ⟨rank, low, high, ordered⟩ := (completionBounds_history trace).ordered
  have eventRank := (ready_iff_rank setup _ rank ordered event).mp current
  have nextOrdered : next.application.config.cut.IsPrefix (rank + 1) := by
    rw [control.execution.application.config.step_cut event current action
      next.application.config supported]
    exact ordered.complete_at event current eventRank
  have successor := (ready_iff_rank setup _ (rank + 1) nextOrdered query).mp ready
  have appended := environmentStep_recall_append control.execution next command moved
  rw [appended, List.length_append, List.length_singleton] at visited
  change Fin 4 at query
  fin_cases query
  · change none = some owner at owned
    cases owned
  · change none = some owner at owned
    cases owned
  · change 2 = rank + 1 at successor
    change 3 ≤ control.execution.environmentRecall.length + 1 at visited
    have one : rank = 1 := by omega
    rw [one] at low high
    simp only [lowerRank, upperRank] at low high
    split_ifs at low high <;> omega
  · change 3 = rank + 1 at successor
    change 11 ≤ control.execution.environmentRecall.length + 1 at visited
    have two : rank = 2 := by omega
    rw [two] at low
    unfold lowerRank at low
    split_ifs at low <;> omega

private theorem opportunity_environment (control : app.Control)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace (some control))
    (valid : opportunityWitnessInvariant (some control))
    (next : app.Execution) (command : app.Command)
    (selected : command ∈ (scheduler control.execution.environmentRecall
      (control.execution.observeEnvironment app)).support)
    (moved : next ∈ (control.execution.environmentStep app command).support)
    (remaining : Nat) :
    opportunityWitnessInvariant (some ⟨remaining, command.actor? app, next⟩) := by
  intro event owner entered owned ready activated visited
  obtain ⟨before, activationEq⟩ := opportunity_ready_before control trace next command
    moved event owner owned ready visited
  have priorActivated : control.execution.application.activatedAt event = some entered :=
    activationEq ▸ activated
  have appended := environmentStep_recall_append control.execution next command moved
  rw [appended] at visited ⊢
  by_cases old : opportunityEnd event ≤ control.execution.environmentRecall.length
  · exact ownerActivatedSince_append (valid event owner entered owned before priorActivated old) _
  have fresh : control.execution.environmentRecall.length + 1 = opportunityEnd event := by
    rw [List.length_append, List.length_singleton] at visited
    omega
  have chosen : command = .activate owner := by
    change Fin 4 at event
    fin_cases event
    · change none = some owner at owned
      cases owned
    · change none = some owner at owned
      cases owned
    · have same : owner = alice := (Option.some.inj owned).symm
      have stage : control.execution.environmentRecall.length = 2 := by
        change control.execution.environmentRecall.length + 1 = 3 at fresh
        omega
      have actual := scheduler_support_other _ _ command (by omega) (by omega) selected
      simpa only [stage, stageCommand, same] using actual
    · have same : owner = bob := (Option.some.inj owned).symm
      have stage : control.execution.environmentRecall.length = 10 := by
        change control.execution.environmentRecall.length + 1 = 11 at fresh
        omega
      have actual := scheduler_support_other _ _ command (by omega) (by omega) selected
      simpa only [stage, stageCommand, same] using actual
  refine ⟨⟨control.execution.observeEnvironment app, command⟩,
    List.mem_append_right _ (List.mem_singleton_self _), chosen, priorActivated, ?_⟩
  exact (control.execution.application.publicView_eventReady event).mpr before

private theorem opportunity_transition (before after : app.ProtocolState)
    (trace : (app.protocol (initialLaw setup) horizon scheduler).Trace before)
    (valid : opportunityWitnessInvariant before) (joint : Player → Option app.Action)
    (reached : after ∈
      (app.transition (initialLaw setup) horizon scheduler before joint).support) :
    opportunityWitnessInvariant after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      intro event owner entered _ _ _ visited
      have positive : 0 < opportunityEnd event := by
        unfold opportunityEnd
        split_ifs <;> omega
      change opportunityEnd event ≤ 0 at visited
      omega
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          intro event owner entered owned ready activated visited
          obtain ⟨configEq, publicEq⟩ :=
            (runtime setup).reactive_respond_application leaks execution who _
          have activatedEq := congrArg PublicView.activatedAt publicEq
          dsimp only [State.publicView] at activatedEq
          rw [configEq] at ready
          rw [activatedEq] at activated
          rw [app.respond_environmentRecall] at visited ⊢
          exact valid event owner entered owned ready activated visited
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact valid
          | succ remaining =>
              obtain ⟨command, selected, realized⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ realized
              exact opportunity_environment _ trace valid next command selected moved remaining

theorem opportunityWitness_history : ∀ {state}
    (_trace : (app.protocol (initialLaw setup) horizon scheduler).Trace state),
    opportunityWitnessInvariant state
  | _, .start => trivial
  | _, .extend prior joint _ reached =>
      opportunity_transition _ _ prior (opportunityWitness_history prior) joint reached

theorem opportunity :
    Opportunity (runtime setup) leaks (initialLaw setup) horizon scheduler delay := by
  intro control trace event owner entered owned ready activated due
  have clock : ClockPhase control := clockPhase_history trace
  have visited : opportunityEnd event ≤ control.execution.environmentRecall.length := by
    rw [clock.clock] at due
    change Fin 4 at event
    fin_cases event
    · change none = some owner at owned
      cases owned
    · change none = some owner at owned
      cases owned
    · change 3 ≤ control.execution.environmentRecall.length
      change entered + 0 < stageClock control.execution.environmentRecall at due
      by_contra early
      dsimp only [stageClock] at due
      split_ifs at due <;> omega
    · change 11 ≤ control.execution.environmentRecall.length
      change entered + 3 < stageClock control.execution.environmentRecall at due
      by_contra early
      dsimp only [stageClock] at due
      split_ifs at due <;> omega
  exact opportunityWitness_history trace event owner entered owned
    ((control.execution.application.publicView_eventReady event).mp ready) activated visited

end Vegas.PrivateResolutionFork
