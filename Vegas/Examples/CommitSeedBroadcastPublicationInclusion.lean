/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFinishedOwner

/-! # Inclusion cannot exclude the owner of a successful Boolean binding -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every accepted opening of this owner's successful binding has a
successful TRUE-guard publication. Foreign calls cannot exclude this owner,
and declarations themselves do not change exclusions. -/
theorem native_inclusion_keeps_successful_binding_owner
    (state : RecoveryState graph) (native : EventGraphRuntime.State graph)
    (message : Message Player (CommitAttemptPacket graph)) (owner : Player)
    (value : Bool)
    (stored : state.native.config.store (.inr (bindingEvent owner)) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (active : owner ∉ state.excluded)
    (accepted : handle runtime state.native
      ⟨message.id, message.payload.packet.call⟩ = some native) :
    owner ∉ (state.inclusionResult message.payload.packet.call native).excluded := by
  cases call : message.payload.packet.call with
  | malformed raw => simpa only [call, RecoveryState.inclusionResult] using active
  | commitment event candidate => simpa only [call, RecoveryState.inclusionResult] using active
  | opening event candidate raw =>
      have actual : handle runtime state.native
          ⟨message.id, .opening event candidate raw⟩ = some native := by
        simpa only [call] using accepted
      obtain ⟨_ready, _timely, _author, _payload, _binding, _checks, outputEq, _rest⟩ :=
        runtime.handle_opening_conditions state.native native message.id event candidate raw actual
      by_cases own : event = revealEvent owner
      · subst event
        have output := handle_successful_binding_opening state.native native message.id owner
          candidate raw value stored actual
        have noFailure := successful_opening_not_failed native owner value output
        simpa only [call, RecoveryState.inclusionResult, noFailure, Bool.false_eq_true, ite_false]
          using active
      · have foreign : graph.actor? event ≠ some owner := by
          intro acting
          rcases owned_event_cases event owner acting with binding | publication
          · rw [binding] at outputEq
            cases (bindingEvent_layout owner).symm.trans outputEq
          · exact own publication
        dsimp only [RecoveryState.inclusionResult]
        split
        · exact excludeEvent_keeps_foreign state.excluded owner active event foreign
        · exact active

/-- The same owner protection holds for the actual admitted phase handler,
including the real normalization and any immediately completed suffix. -/
theorem phase_handle_keeps_successful_binding_owner
    (state next : PhaseRuntimeState graph)
    (message : Message Player (CommitAttemptPacket graph)) (owner : Player)
    (value : Bool)
    (stored : state.current.native.config.store (.inr (bindingEvent owner)) = some
      (cast (congrArg EventField.Value (bindingEvent_layout owner).symm)
        (PublicationResult.success value)))
    (active : owner ∉ state.current.excluded)
    (accepted : state.handle runtime message = some next) :
    owner ∉ next.current.excluded := by
  unfold PhaseRuntimeState.handle at accepted
  split at accepted
  · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
    change owner ∉ (PhaseRuntimeState.settle _ _ _ _ _).current.excluded
    rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).1]
    exact native_inclusion_keeps_successful_binding_owner state.current native message owner value
      stored active handled
  · cases accepted

end Vegas.Examples.CommitSeedBroadcast
