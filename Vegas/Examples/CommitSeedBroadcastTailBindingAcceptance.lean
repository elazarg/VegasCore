/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBindingSuccess
import Vegas.Examples.CommitSeedBroadcastBindingReceipts

/-! # Receipt retention after a counted continuation declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- After a genuine counted continuation declaration, any actual later prefix
already retains its true receipt or is literally the unchanged postresponse
control awaiting the immediately selected include. -/
theorem tail_counted_binding_after_submission (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (sourceTrace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (event : graph.EventId) (binding : graph.outputLayout event = .binding owner .bool)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe app owner))
    (postTrace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some final))
    (kept : TracePrefix postTrace trace) :
    PhaseService.BindingAccepted runtime leaks ⟨execution.application.attempt, event⟩ owner
        final.execution ∨
      final = ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩ := by
  classical
  let coordinate : CommitAttemptEvent graph := ⟨execution.application.attempt, event⟩
  let after := execution.respond app owner ⟨some material⟩
  let start : app.Control := ⟨remaining, none, after⟩
  have along : ∀ {state}
      {later : (countedMenu.protocol initial horizon (family seeds)).Trace state},
      TracePrefix postTrace later → ∃ current : app.Control, state = some current ∧
        (PhaseService.BindingAccepted runtime leaks coordinate owner current.execution ∨
          current = start) := by
    intro state later retained
    induction retained with
    | refl => exact ⟨start, rfl, Or.inr rfl⟩
    | @extend source target earlier retained joint legal realized ih =>
        obtain ⟨current, rfl, previous⟩ := ih
        have moved : target ∈ (app.transition initial horizon (family seeds)
            (some current) joint).support := realized
        obtain ⟨next, same, _recalled⟩ := app.transition_recall_prefix initial horizon
          (family seeds) current target joint moved
        subst target
        refine ⟨next, rfl, Or.inl ?_⟩
        rcases previous with accepted | pending
        · exact bindingAccepted_transition seeds current next
            (countedMenu.toRawTrace initial horizon (family seeds) earlier)
            (countedMenu.toRawTrace initial horizon (family seeds)
              (earlier.extend joint legal realized)) coordinate owner accepted joint moved
        · subst current
          cases remaining with
          | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
          | succ remaining =>
              obtain ⟨command, selected, commandMoved⟩ :=
                Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
              obtain ⟨result, supported, exactControl⟩ := PMF.support_map .. ▸ commandMoved
              cases Option.some.inj exactControl
              change command ∈ (family seeds after.environmentRecall
                (after.observeEnvironment app)).support at selected
              rw [family, PMF.mem_support_pure_iff] at selected
              rw [selected] at supported
              exact tail_counted_binding_submission_accepted seeds (remaining + 1) execution
                owner sourceTrace retired event binding request material offered result supported
  obtain ⟨current, same, alternatives⟩ := along kept
  cases Option.some.inj same
  exact alternatives

/-- A genuine counted continuation declaration receives an actual true receipt
before its coordinate can resolve, including through retries and exhausted restore. -/
theorem tail_counted_binding_submission_resolved_accepted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution) (owner : Player)
    (sourceTrace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (retired : execution.application.attempt ≠ originalAttempt)
    (event : graph.EventId) (binding : graph.outputLayout event = .binding owner .bool)
    (request : execution.application.SeedRequest owner ⟨execution.application.attempt, event⟩)
    (material : WitnessedSubmission graph)
    (offered : (⟨some material⟩ : app.Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner
        (execution.recall owner) (execution.observe app owner))
    (postTrace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution.respond app owner ⟨some material⟩⟩))
    (final : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some final))
    (kept : TracePrefix postTrace trace)
    (resolved : (⟨execution.application.attempt, event⟩ : CommitAttemptEvent graph).Resolved
      final.execution.application) :
    PhaseService.BindingAccepted runtime leaks ⟨execution.application.attempt, event⟩ owner
      final.execution := by
  obtain accepted | unchanged := tail_counted_binding_after_submission seeds remaining execution
    owner sourceTrace retired event binding request material offered postTrace final trace kept
  · exact accepted
  · subst final
    exact (resolved.not_request _ _ owner (respond_request runtime leaks execution owner
      ⟨some material⟩ owner _ request)).elim
end Vegas.Examples.CommitSeedBroadcast
