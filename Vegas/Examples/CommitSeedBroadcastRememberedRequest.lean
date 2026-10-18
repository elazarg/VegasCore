/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastTailExhaustion

/-! # Actual own request recall at positive service age -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability GameTheory.Enforcement

/-- A positive readiness-relative age identifies an earlier actual own
response whose original before-view requests this same full coordinate. -/
theorem positive_age_own_request (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app)) :
    ∃ entry ∈ execution.recall owner,
      PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate := by
  classical
  obtain ⟨entry, member, callback⟩ := positive_age_callback countedMenu seed remaining execution
    trace coordinate owner request positive
  have clockMember : PhaseSeedScheduler.elapsed runtime leaks coordinate entry.beforeView ∈
      clockWord coordinate owner execution.environmentRecall := by
    exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr
      ⟨member, decide_eq_true_eq.mpr callback⟩, rfl⟩
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
    horizon (family seed) remaining execution trace owner coordinate
  have nonempty : (execution.recall owner).filter (fun entry => decide
      (PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)) ≠ [] := by
    intro empty
    have clockEmpty : clockWord coordinate owner execution.environmentRecall = [] := by
      rw [← word_clock_projection coordinate owner execution.environmentRecall
        (execution.observeEnvironment app), words]
      simp only [PhaseSeedScheduler.ownerWord, empty, List.map_nil]
    rw [clockEmpty] at clockMember
    exact (List.not_mem_nil clockMember).elim
  cases filtered : (execution.recall owner).filter (fun entry => decide
      (PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)) with
  | nil => exact (nonempty filtered).elim
  | cons first rest =>
      have present : first ∈ (execution.recall owner).filter (fun entry => decide
          (PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate)) := by
        rw [filtered]
        exact List.mem_cons_self
      exact ⟨first, (List.mem_filter.mp present).1,
        of_decide_eq_true (List.mem_filter.mp present).2⟩

end Vegas.Examples.CommitSeedBroadcast
