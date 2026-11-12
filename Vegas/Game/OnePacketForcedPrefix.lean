module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketIntendedProjection
public import Vegas.Game.OnePacketFactorization
public import Vegas.Game.OnePacketPrescribedSupport

@[expose] public section

/-! # Forced states along native histories

Public default membership, failed reveals and owed failures persist under every
source step. Thus a source point reaching a point forced for `who` is itself
forced (`Vegas.forcedPoint_of_step`). The native finite-path transport of
step-closed source properties then shows that every initialized state along a
history ending in a forced state of `who` is forced for `who`
(`Vegas.forcedState_of_transition`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}

/-- **Forcedness reaches back over a source step.** A source point from which a
step reaches a point forced for `who` is forced for `who`. -/
theorem forcedPoint_of_step {who : Player} {point target : ProtocolState setup.program}
    {joint : Player → Option (OwnAction Player L)}
    (reached : target ∈ (ProtocolState.step setup.program point joint).support)
    (forced : ForcedPoint setup who target) : ForcedPoint setup who point := by
  refine ⟨fun failed => forced.1 (ProtocolState.revealFailed_step who setup.program point joint
    target failed reached), fun other different => ⟨fun excluded => (forced.2 other different).1
      (ProtocolState.defaulted_step setup.program point target joint reached excluded),
    fun owed => (forced.2 other different).2
      (ProtocolState.owesFailure_step other setup.program point joint target owed reached)⟩⟩

/-- A forced state of `who` is an initialized state whose decoded point is
forced for `who`. -/
theorem forcedState_iff_decodedPoint
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {who : Player} (control : (application setup timeouts leaks).Control) :
    ForcedState setup timeouts leaks who (some control) ↔
      ∃ point, decodedPoint setup control.execution.application.config = some point ∧
        ForcedPoint setup who point := by
  constructor
  · rintro ⟨rank, point, ordered, decoded, forced⟩
    have exists_ : ∃ rank, control.execution.application.config.cut.IsPrefix rank :=
      ⟨rank, ordered⟩
    refine ⟨point, ?_, forced⟩
    unfold decodedPoint
    rw [dite_eq_left_of_eq_true (eq_true exists_), show exists_.choose = rank from
      EventOrder.Cut.IsPrefix.unique exists_.choose_spec ordered]
    exact decoded
  · rintro ⟨point, decoded, forced⟩
    unfold decodedPoint at decoded
    split at decoded
    · rename_i ordered
      exact ⟨_, point, ordered.choose_spec, decoded, forced⟩
    · cases decoded

variable [Fintype Player]
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- **Forced states reach back along native transitions.** If a native
transition of the one-packet game from an initialized state reaches a forced
state of `who`, that initialized state is forced for `who`. -/
theorem forcedState_of_transition {who : Player} {before : (application setup timeouts
  leaks).Control}
    {after : (application setup timeouts leaks).ProtocolState}
    (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some before))
    (joint : Player → Option (application setup timeouts leaks).Action)
    (realized : after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
      scheduler
      (some before) joint).support)
    (forced : ForcedState setup timeouts leaks who after) :
    ForcedState setup timeouts leaks who (some before) := by
  cases after with
  | none => exact forced.elim
  | some next =>
      obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (timeouts := timeouts) (failureProfile
        setup.program)
        (bounds.onePacketMenu timeouts leaks) horizon scheduler prior before rfl
      obtain ⟨target, decoded, forcedTarget⟩ := (forcedState_iff_decodedPoint (timeouts := timeouts)
        next).mp forced
      refine (forcedState_iff_decodedPoint (timeouts := timeouts) before).mpr ?_
      by_contra denied
      have closed : StepClosed setup (fun point => ¬ ForcedPoint setup who point) := by
        intro point joint target notForced reached forced
        exact notForced (forcedPoint_of_step reached forced)
      have beforeHolds : DecodedState setup timeouts leaks (failureProfile setup.program)
          (fun point => ¬ ForcedPoint setup who point) (some before) := by
        refine ⟨rank, ⟨residual⟩, fun point read forced => ?_⟩
        rw [residual.decode, Option.some.injEq] at read
        subst read
        exact denied ⟨_, decodedPoint_eq residual, forced⟩
      obtain ⟨nextRank, ⟨nextResidual⟩, afterHolds⟩ := decodedHolds_transition closed
        (initialLaw setup) horizon scheduler (some before) (some next) joint beforeHolds realized
      rw [decodedPoint_eq nextResidual, Option.some.injEq] at decoded
      subst decoded
      exact afterHolds _ nextResidual.decode forcedTarget

end Vegas
