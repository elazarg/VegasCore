/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastService
import Interaction.ReactiveTrafficIdentity
import Interaction.ReactiveRecallInvariant
import Interaction.ReactiveReceipts

/-! # Actual accepting receipt retention along initialized histories -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem bindingAccepted_transition (seeds : Seeds) (before after : app.Control)
    (prior : (app.protocol initial horizon (family seeds)).Trace (some before))
    (trace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks coordinate owner before.execution)
    (joint : Player → Option app.Action)
    (moved : some after ∈
      (app.transition initial horizon (family seeds) (some before) joint).support) :
    PhaseService.BindingAccepted runtime leaks coordinate owner after.execution := by
  obtain ⟨message, input, authored, tag, named, receipt⟩ := accepted
  obtain ⟨next, same, recalled⟩ := app.transition_recall_prefix initial horizon (family seeds)
    before (some after) joint moved
  cases Option.some.inj same
  have output : message ∈ app.outputs (before.execution.recall owner) := by
    rw [← app.history_inputRecall initial horizon (family seeds) prior owner]
    exact List.mem_filter.mpr ⟨input, decide_eq_true authored⟩
  obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
  have laterOutput : message ∈ app.outputs (after.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, (recalled owner).subset member, emitted⟩
  rw [← app.history_inputRecall initial horizon (family seeds) trace owner] at laterOutput
  obtain ⟨next, same, receipts⟩ := app.transition_receipts_prefix initial horizon (family seeds)
    before (some after) joint moved
  cases Option.some.inj same
  exact ⟨message, (List.mem_filter.mp laterOutput).1, authored, tag, named, receipts.subset receipt⟩

/-- Actual accepting packets and their true receipts persist along the same
raw initialized trace, including normalization and every later reset. -/
theorem bindingAccepted_prefix (seeds : Seeds) (before after : app.Control)
    (prior : (app.protocol initial horizon (family seeds)).Trace (some before))
    (trace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (kept : TracePrefix prior trace) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks coordinate owner before.execution) :
    PhaseService.BindingAccepted runtime leaks coordinate owner after.execution := by
  have along : ∀ {state} {later : (app.protocol initial horizon (family seeds)).Trace state},
      TracePrefix prior later → ∃ current : app.Control, state = some current ∧
        PhaseService.BindingAccepted runtime leaks coordinate owner current.execution := by
    intro state later retained
    induction retained with
    | refl => exact ⟨before, rfl, accepted⟩
    | @extend source target earlier retained joint legal realized ih =>
        obtain ⟨current, rfl, valid⟩ := ih
        have moved : target ∈ (app.transition initial horizon (family seeds)
            (some current) joint).support := realized
        obtain ⟨next, same, _recalled⟩ := app.transition_recall_prefix initial horizon
          (family seeds) current target joint moved
        subst target
        exact ⟨next, rfl, bindingAccepted_transition seeds current next earlier
          (earlier.extend joint legal realized) coordinate owner valid joint moved⟩
  obtain ⟨current, same, valid⟩ := along kept
  cases Option.some.inj same
  exact valid

end Vegas.Examples.CommitSeedBroadcast
