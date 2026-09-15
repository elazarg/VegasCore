/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageServiceCompletion
import Vegas.Graph.MessagePolicyFreshness
import Vegas.Graph.MessageHistoryExtension

/-! # Immutable graph data within a phase

Pending traffic, private preparation, and clock ticks can change the native
execution without changing its graph cursor. While that cursor stays fixed,
the typed environment, public values, and accepted binding addresses stay fixed
as well. This fact applies to arbitrary native policies, not only compiled play.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

private theorem tick_running_eq_of_phase_eq
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (ideal : VEnv L Γ) (values : Graph.PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat)
    (next : State Player L Δ)
    (supported : next ∈ (runtime.tick
      (.running graph ideal values bindings candidates pc clock enteredAt)).support)
    (same : next.phase = pc) :
    ∃ candidates' clock' enteredAt',
      next = .running graph ideal values bindings candidates' pc clock' enteredAt' := by
  cases graph with
  | ret outcome =>
      simp only [tick, FinDist.mem_support_pure] at supported
      subst next
      exact ⟨candidates, clock + 1, enteredAt, rfl⟩
  | sample name fresh law tail =>
      simp only [tick, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      simp [State.phase] at same
  | bind name owner fresh tail =>
      simp only [tick] at supported
      split at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        simp [advanceBindFailure, State.phase] at same
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        exact ⟨candidates, clock + 1, enteredAt, rfl⟩
  | resolve output owner binding fresh source checks tail =>
      simp only [tick] at supported
      split at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        simp [advanceResolve, State.phase] at same
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        exact ⟨candidates, clock + 1, enteredAt, rfl⟩

/-- If an arbitrary native run ends at its starting graph phase, its typed
graph, ideal environment, public values, and accepted addresses are unchanged.
Only candidate preparation and clock bookkeeping may have changed inside the
application; message pools, receipts, and policy histories are not constrained. -/
theorem runPolicies_running_eq_of_phase_eq
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    (ideal : VEnv L Γ) (values : Graph.PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock enteredAt : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (initial : execution.native.application =
      .running graph ideal values bindings candidates pc clock enteredAt)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support)
    (same : next.native.application.phase = pc) :
    ∃ candidates' clock' enteredAt', next.native.application =
      .running graph ideal values bindings candidates' pc clock' enteredAt' := by
  let invariant : State Player L Δ → Prop := fun current =>
    pc < current.phase ∨ ∃ candidates' clock' enteredAt',
      current = .running graph ideal values bindings candidates' pc clock' enteredAt'
  have preserved : invariant next.native.application := by
    apply runtime.application.runPolicies_application_invariant invariant
      (players := players) (environment := environment) (schedule := schedule)
      (execution := execution) (next := next)
    · intro current actor command holds
      rcases holds with advanced | ⟨catalog, time, entered, rfl⟩
      · left
        change pc < (runtime.privateStep current actor command).phase
        rwa [runtime.privateStep_phase]
      · right
        cases command
        · exact ⟨_, time, entered, rfl⟩
        · exact ⟨catalog, time, entered, rfl⟩
    · intro current message after holds accepted
      have progressed := runtime.handle_phase current after message accepted
      left
      rcases holds with advanced | ⟨catalog, time, entered, rfl⟩
      · omega
      · simpa using progressed ▸ Nat.lt_succ_self pc
    · intro current command after holds happened
      cases command
      have monotone := runtime.tick_phase_mono current after happened
      rcases holds with advanced | ⟨catalog, time, entered, rfl⟩
      · left
        exact advanced.trans_le monotone
      · change pc ≤ after.phase at monotone
        rcases monotone.eq_or_lt with atPhase | advanced
        · right
          exact tick_running_eq_of_phase_eq runtime graph ideal values bindings
            catalog pc time entered after happened atPhase.symm
        · exact Or.inl advanced
    · exact Or.inr ⟨candidates, clock, enteredAt, initial⟩
    · exact supported
  rcases preserved with advanced | unchanged
  · omega
  · exact unchanged

/-- Actual own histories cannot acquire new disclosure markers for an already
passed site. The observation argument is fixed: changes in observed graph
values are a separate question from extension of authenticated command history.
Neither player policies nor the environment are restricted here. -/
theorem runPolicies_projectLogicalHistory_before
    (runtime : GraphRuntime Player L Δ) (graph : Graph Player L Γ Δ)
    {observed : VCtx Player L} (who : Player)
    (observation : Observation L who observed) (site fuel : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (passed : site + fuel ≤ execution.native.application.phase)
    (supported : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    projectLogicalHistory who observation (next.principalHistory who) graph site fuel =
      projectLogicalHistory who observation (execution.principalHistory who) graph site fuel := by
  let invariant : runtime.application.PolicyExecution → Prop := fun current =>
    site + fuel ≤ current.native.application.phase ∧
      projectLogicalHistory who observation (current.principalHistory who) graph site fuel =
        projectLogicalHistory who observation (execution.principalHistory who) graph site fuel
  have preserved : invariant next := by
    apply runtime.application.runPolicies_execution_invariant invariant players environment
    · intro current actor command after holds _commandMem stepMem
      refine ⟨holds.1.trans (runtime.playerStep_phase_mono actor current after command stepMem), ?_⟩
      by_cases same : actor = who
      · subst actor
        rw [runtime.application.playerStep_history_self who current command after stepMem]
        rw [projectLogicalHistory_append_of_no_disclosure_range]
        · exact holds.2
        · intro scanned _lower upper
          have different : current.native.application.publicView.pc ≠ scanned := by
            rw [State.publicView_pc]
            omega
          cases command with
          | privateCommand command =>
              cases command with
              | prepare => rfl
              | rememberDisclosure disclose =>
                  have observedPhase :
                      (MessageApplication.State.observe runtime.application
                        current.native who).application.publicState.pc =
                          current.native.application.publicView.pc := by
                    change (State.playerView current.native.application who).publicState.pc = _
                    cases current.native.application
                    rfl
                  simp only [entryDisclosureAt, observedPhase, different, ↓reduceIte]
          | submit | replay | wait => rfl
      · rw [runtime.application.playerStep_other_history actor who
          (Ne.symm same) current command after stepMem]
        exact holds.2
    · intro current command after holds _commandMem stepMem
      refine ⟨holds.1.trans
        (runtime.environmentPolicyStep_phase_mono current after command stepMem), ?_⟩
      rw [runtime.application.environmentStep_principalHistory current command after stepMem]
      exact holds.2
    · exact ⟨passed, rfl⟩
    · exact supported
  exact preserved.2

end Vegas.GraphRuntime
