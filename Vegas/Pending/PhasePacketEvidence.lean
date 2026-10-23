/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseCountVerdict
import Vegas.Pending.ReactivePacketEvidence
import Vegas.Pending.ReactiveSignedCommitments

/-! # Authentic carried opening facts across all physical attempts

Semantic rollback never rolls back the physical candidate catalogue. Therefore
owned issuance and forwarding retain the original immutable opening meaning,
including certificates carried by packets of voided or retired attempts.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- A certified candidate meaning persists through every actual phase command,
including automatic archive, restore and next-phase installation. -/
theorem phaseOpeningFactInvariant (fact : OpeningFact graph) :
    (app).Invariant (fun state => fact.Holds state.current.native) where
  submit state who material valid := by
    have fixed : state.current.native.candidates.lookup fact.handle ≠ .fresh := by
      rw [valid]
      simp
    have registered := material.call.register_lookup_of_not_fresh state.current.native who
      fact.handle fixed
    exact (submitStep_lookup_of_not_fresh _ who material.call.packet fact.handle
      (by rwa [registered])).trans (registered.trans valid)
  handle state message next valid accepted := by
    change state.handle runtime message = some next at accepted
    unfold PhaseRuntimeState.handle at accepted
    split at accepted
    · obtain ⟨native, handled, rfl⟩ := Option.map_eq_some_iff.mp accepted
      change (PhaseRuntimeState.settle _ _ _ _ _).current.native.candidates.lookup fact.handle = _
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      have fixed : state.current.native.candidates.lookup fact.handle ≠ .fresh := by
        rw [valid]
        simp
      exact (handle_lookup_of_not_fresh runtime state.current.native native
        ⟨message.id, message.payload.packet.call⟩ fact.handle fixed handled).trans valid
    · cases accepted
  environment state command next valid reached := by
    change next ∈ (state.environment runtime command).support at reached
    unfold PhaseRuntimeState.environment at reached
    split at reached
    · rw [PMF.support_map] at reached
      obtain ⟨native, supported, rfl⟩ := reached
      change (PhaseRuntimeState.settle _ _ _ _ _).current.native.candidates.lookup fact.handle = _
      rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
      change native.candidates.lookup fact.handle = _
      rw [(environmentStep_tables runtime _ _ command supported).2]
      exact valid
    · rw [PMF.mem_support_pure_iff] at reached
      subst next
      exact valid

/-- Token masks alter authorization without altering the signed opening fact. -/
theorem phase_emit_evidence (state : PhaseRuntimeState graph) (who : Player)
    (known : List (Message Player (CommitAttemptPacket graph)))
    (material : WitnessedSubmission graph) :
    (state.emit who known material).packet.evidence =
      (material.emit state.current.native who (known.map PhaseCount.nativeMessage)).evidence := by
  dsimp only [PhaseRuntimeState.emit, RecoveryState.emit, PhaseCount.nativeMessage]
  split <;> split <;> rfl

/-- The ordinary generic all-history evidence theorem applies to actual tagged
packets; its truth is the current physical immutable candidate catalogue. -/
def phasePacketEvidence : (app).PacketEvidence where
  Fact := OpeningFact graph
  valid state fact := fact.Holds state.current.native
  decode packet := packet.packet.evidence.toList
  persists := phaseOpeningFactInvariant runtime leaks
  issued state who known material received fact certified := by
    change fact ∈ (state.emit who known material).packet.evidence.toList at certified
    rw [phase_emit_evidence] at certified
    apply material.emit_sound state.current.native who (known.map PhaseCount.nativeMessage)
      _ fact (by simpa using certified)
    intro message member evidence carried
    obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
    change original.payload.packet.evidence = some evidence at carried
    exact received original present evidence (by
      rw [carried]
      exact List.mem_singleton_self _)

end Vegas.EventGraphRuntime
