/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingAcceptance
import Vegas.Examples.CommitSeedBroadcastProperPolicy
import Vegas.Examples.CommitSeedBroadcastProtected
import Vegas.Pending.PhaseCountedSurvivor
import Interaction.ReactiveReceiptBoundary

/-! # Counted original clock-zero packets are accepted before expiry -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- A genuine original clock-zero declaration has already been accepted at the
queries after its marker inclusion and before expiry. An unresolved counted packet
would still be pending,
which contradicts the actual early-submission receipt already recorded there. -/
theorem original_clock_zero_recorded_accepted (seeds : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ current.execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (authored : message.sender = owner) (tagged : message.payload.attempt = originalAttempt)
    (named : message.payload.packet.call.event? graph = some (bindingEvent owner))
    (zero : entry.beforeView.application.1.publicView.clock = 0)
    (early : current.execution.environmentRecall.length ≤ 26)
    (late : earlyPosition seeds owner < current.execution.environmentRecall.length) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      current.execution := by
  classical
  by_contra unaccepted
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have request := original_request_of_unaccepted_before_expiry seeds _ raw owner unaccepted
    (by omega)
  have original : current.execution.application.attempt = originalAttempt := request.1.symm
  have input : message ∈ current.execution.network.inputs := by
    have output : message ∈ app.outputs (current.execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, member, emitted⟩
    rw [← app.history_inputRecall initial horizon (family seeds) raw owner] at output
    exact (List.mem_filter.mp output).1
  have stamp := original_timer (family seeds) _ raw original owner request.2.2.1.1
  change current.execution.application.current.native.activatedAt (bindingEvent owner) = some 0
    at stamp
  have timely : current.execution.application.current.native.WithinDeadline runtime
      (bindingEvent owner) := by
    rw [State.WithinDeadline, stamp]
    change current.execution.application.current.native.clock - 0 < 6
    rw [Nat.sub_zero, original_clock_index seeds _ raw original]
    generalize indexEq : current.execution.environmentRecall.length = index at early ⊢
    interval_cases index <;> decide
  have packetRequest : current.execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, bindingEvent owner⟩ := by
    rw [authored, tagged]
    change current.execution.application.SeedRequest owner (originalCoordinate owner)
    exact request
  have compiledTrace := trace
  rw [initial_eq_compiled] at compiledTrace
  have pending := PhaseCount.survivor_pending runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (compiledRuntimePhasePlan_maximal program .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon (family seeds) _ compiledTrace message input
      (bindingEvent owner) named packetRequest timely
  obtain ⟨accepted, receipted⟩ := original_early_submission_receipt seeds _ raw owner entry member
    message emitted authored tagged zero original late
  exact app.pending_identifier_not_receipted initial horizon (family seeds) _ raw message pending
    accepted receipted

end Vegas.Examples.CommitSeedBroadcast
