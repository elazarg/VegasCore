/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingOriginalEarlyAdmission
import Vegas.Examples.CommitSeedSignallingHelperPacketPermission

/-! # A counted early helper has a true binding receipt after its inclusion turn -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- Before Bob's late polls, a recognized early helper on a counted history
has really completed Bob's original binding once its marker turn has passed.
Its hidden preparation, evidence and both players' later policies are arbitrary. -/
theorem counted_helper_bob_binding_accepted (seed : Seeds) (current : app.Control)
    (mixed : countedProtocol.Trace (some current))
    (fixed : (countedMenu.protocol initial horizon (family seed)).Trace (some current))
    (request : current.execution.application.SeedRequest alice (originalCoordinate alice))
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ current.execution.recall alice)
    (early : current.execution.environmentRecall.length ≤ 12)
    (late : 6 ≤ current.execution.environmentRecall.length)
    (marker : Message Player (CommitAttemptPacket graph))
    (input : marker ∈ current.execution.network.inputs) (sender : marker.sender = bob) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate bob) bob current.execution := by
  let included := PhaseCount.onePacketMenu_in_raw runtime leaks bounds
  have rawMixed := included.trace initial horizon scheduler mixed
  have rawFixed := included.trace initial horizon (family seed) fixed
  have permitted := (observed_helper_packet_permission seed current mixed rawFixed request early
    marker input sender).2
  obtain ⟨entry, recorded, emitted, original, zero⟩ := bob_packet_before_late_origin seed current
    rawFixed request early marker input sender
  obtain ⟨first, _viewed, _allowed, materialized, _aliceRecorded⟩ :=
    bob_original_record_materialization current rawMixed entry recorded original zero
  have materializedSome := emitted
  rw [materialized] at materializedSome
  obtain ⟨material, transmitted, envelope⟩ := Option.map_eq_some_iff.mp materializedSome
  obtain ⟨_viewed, serial, preparation, evidence, shape, _bounded, _fresh⟩ :=
    bob_helper_record_binding_shape current rawMixed quiet entry recorded original zero material
      transmitted marker emitted permitted
  have called : marker.payload.packet.call = material.call.packet := by
    rw [← envelope]
    change (PhaseCount.maskPacket _ _).call = _
    exact PhaseCount.maskPacket_call _ _
  have named : marker.payload.packet.call.event? graph = some (bindingEvent bob) := by
    rw [called, shape]
    rfl
  have stamp := phase_recalled_emission_attempt runtime leaks initial horizon (family seed)
    (countedMenu.toRawTrace initial horizon (family seed) fixed) bob entry recorded marker emitted
  have tagged : marker.payload.attempt = originalAttempt := stamp.trans original
  exact original_clock_zero_recorded_accepted seed current fixed bob entry recorded marker emitted
    sender tagged named zero (by omega) (by change 5 < _; omega)

end Vegas.Examples.CommitSeedSignalling
