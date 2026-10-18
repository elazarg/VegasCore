/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastBindingReceipts
import Interaction.ReactiveServiceInvariant

/-! # Accepting original receipts persist through actual continuations -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem original_binding_accepted_runRounds (selected : app.Scheduler)
    (players : Player → app.Policy) (count : Nat) (before after : app.Execution)
    (reached : after ∈ (app.runRounds selected players count before).support)
    (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      before) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner after := by
  let property : app.Execution → Prop := fun current =>
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner current
  have invariant : app.ServiceInvariant selected property := by
    constructor
    · intro execution actor action valid
      obtain ⟨message, member, sender, attempt, event, receipt⟩ := valid
      refine ⟨message, ?_, sender, attempt, event, ?_⟩
      · rcases action with ⟨transmission⟩
        cases transmission with
        | none => exact member
        | some material => exact List.mem_append_left _ member
      · rwa [app.respond_receipts]
    · intro execution next command valid _selected moved
      obtain ⟨message, member, sender, attempt, event, receipt⟩ := valid
      refine ⟨message, ?_, sender, attempt, event, ?_⟩
      · rwa [app.environmentStep_inputs execution next command moved]
      · exact (app.environmentStep_receipts_prefix execution next command moved).subset receipt
  exact invariant.runRounds players count before after accepted reached

end Vegas.Examples.CommitSeedBroadcast
