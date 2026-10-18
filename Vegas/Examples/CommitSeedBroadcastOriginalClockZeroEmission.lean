/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalEarlyAdmission
import Vegas.Pending.PhaseSeedHistoryInput
import Interaction.ReactiveRecordedResponse

/-! # Clock-zero service emissions retain their actual original declaration -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- An original service emission at relative clock zero has its actual retained
own declaration at physical clock zero. This reads the genuine native stamp,
without a clean endpoint, truthful preparation or supplied earlier callback. -/
theorem original_clock_zero_emission_recorded (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (message : Message Player (CommitAttemptPacket graph))
    (emitted : (0, message) ∈ (PhaseSeedScheduler.localInput runtime leaks
      (originalCoordinate owner) owner execution.environmentRecall
        (execution.observeEnvironment app)).emissions) :
    ∃ entry ∈ execution.recall owner, entry.emitted = some message ∧
      entry.beforeView.application.1.publicView.clock = 0 := by
  classical
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
    (family seeds) remaining execution trace
  rw [PhaseSeedScheduler.localInput_word, words owner (originalCoordinate owner)] at emitted
  obtain ⟨record, recordMember, packetMember⟩ := List.mem_flatMap.mp emitted
  obtain ⟨packet, packetMember, pairEq⟩ := List.mem_map.mp packetMember
  have samePacket : packet = message := congrArg Prod.snd pairEq
  subst packet
  obtain ⟨entry, entryMember, recordEq⟩ := List.mem_map.mp recordMember
  obtain ⟨member, requested⟩ := List.mem_filter.mp entryMember
  have publicRequest : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner) := of_decide_eq_true requested
  have entryPacket : message ∈ entry.emitted.toList.filter
      (PhaseSeedScheduler.ownPacket (originalCoordinate owner) owner) := by
    simpa only [← recordEq] using packetMember
  have actualEmission := Option.mem_toList.mp (List.mem_filter.mp entryPacket).1
  have age : entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock = 0 :=
    (congrArg Prod.fst recordEq).trans (congrArg Prod.fst pairEq)
  obtain ⟨before, prior, _kept, _acting, viewed, _offered, _later, _recalled⟩ :=
    menu.recorded_response_prefix initial horizon (family seeds) _ trace owner entry member
  have raw := menu.toRawTrace initial horizon (family seeds) prior
  have valid := raw_native_valid (family seeds) _ raw
  rw [viewed] at publicRequest age
  change PhaseRuntimeState.requests before.execution.application.publicView owner
    (originalCoordinate owner) at publicRequest
  have request := (before.execution.application.requests_publicView valid owner _).mp publicRequest
  have original : before.execution.application.attempt = originalAttempt := request.1.symm
  have stamp := original_timer (family seeds) _ raw original owner request.2.2.1.1
  change before.execution.application.current.native.activatedAt (bindingEvent owner) = some 0
    at stamp
  change before.execution.application.current.native.clock -
    (before.execution.application.current.native.activatedAt (bindingEvent owner)).getD
      before.execution.application.current.native.clock = 0 at age
  rw [stamp, Option.getD_some, Nat.sub_zero] at age
  refine ⟨entry, member, actualEmission, ?_⟩
  rw [viewed]
  exact age

end Vegas.Examples.CommitSeedBroadcast
