/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalBindingAcceptance
import Vegas.Examples.CommitSeedSignallingProtected
import Vegas.Pending.PhaseCountedSurvivor
import Interaction.ReactiveReceiptBoundary

/-! # Counted original clock-zero packets are accepted before expiry -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

/-- A genuine original clock-zero declaration has already been accepted at the
last predeadline query. An unresolved counted packet would still be pending,
which contradicts the actual early-submission receipt already recorded there. -/
theorem original_clock_zero_recorded_accepted (seeds : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player) (entry : app.PlayerEntry) (member : entry ∈ execution.recall owner)
    (message : Message Player (CommitAttemptPacket graph)) (emitted : entry.emitted = some message)
    (authored : message.sender = owner) (tagged : message.payload.attempt = originalAttempt)
    (named : message.payload.packet.call.event? graph = some (bindingEvent owner))
    (zero : entry.beforeView.application.1.publicView.clock = 0)
    (position : execution.environmentRecall.length = 19) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner execution := by
  classical
  by_contra unaccepted
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have request := original_request_of_unaccepted_before_expiry seeds _ raw owner unaccepted
    (by rw [position]; decide)
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have input : message ∈ execution.network.inputs := by
    have output : message ∈ app.outputs (execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, member, emitted⟩
    rw [← app.history_inputRecall initial horizon (family seeds) raw owner] at output
    exact (List.mem_filter.mp output).1
  have stamp := original_timer (family seeds) _ raw original (bindingEvent owner)
    (by fin_cases owner <;> simp [bindingEvent, aliceBinding, bobBinding]) request.2.2.1.1
  change execution.application.current.native.activatedAt (bindingEvent owner) = some 0 at stamp
  have timely : execution.application.current.native.WithinDeadline runtime
      (bindingEvent owner) := by
    rw [State.WithinDeadline, stamp]
    change execution.application.current.native.clock - 0 < 6
    rw [Nat.sub_zero, original_clock_index seeds _ raw original, position]
    decide
  have packetRequest : execution.application.SeedRequest message.sender
      ⟨message.payload.attempt, bindingEvent owner⟩ := by
    rw [authored, tagged]
    change execution.application.SeedRequest owner (originalCoordinate owner)
    exact request
  have pending := PhaseCount.survivor_pending runtime leaks bounds plan
    (serviceGraph_revealRelaxedOrdered setup .concurrentReveals)
    (compiledRuntimePhasePlan_maximal program .concurrentReveals)
    (setup.initialLaw.map encodeInputs) horizon (family seeds) _ trace message input
      (bindingEvent owner) named packetRequest timely
  obtain ⟨accepted, receipted⟩ := original_early_submission_receipt seeds _ raw owner entry member
    message emitted authored tagged zero original (by
      change (if owner = alice then 13 else 5) < execution.environmentRecall.length
      rw [position]
      fin_cases owner <;> decide)
  exact app.pending_identifier_not_receipted initial horizon (family seeds) _ raw message pending
    accepted receipted

end Vegas.Examples.CommitSeedSignalling
