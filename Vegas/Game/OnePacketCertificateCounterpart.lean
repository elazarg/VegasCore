module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketResponseBound
public import Vegas.Game.OnePacketInitialFloor

@[expose] public section

/-! # The comparison factor of honest counterparts

At stage `n`, a counterpart's reach is compared through the largest of one, the
inverse initial floor, the inverse content floor and the response ratio
(`Vegas.counterpartFactor`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  [(application setup timeouts leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  [DecidableEq (CellTy Player L)]

variable (setup timeouts leaks bounds horizon scheduler) in
/-- **The comparison factor of a counterpart** at stage `n`: the largest of one,
the inverse initial floor, the inverse content floor and the response ratio. -/
def counterpartFactor (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale floor : ℕ → ℝ) (n : ℕ) : ℝ :=
  max 1 (max (max (1 / initialFloor setup timeouts leaks bounds horizon scheduler)
    (1 / contentFloor setup timeouts leaks bounds horizon scheduler (sequence n)))
    ((1 / floor n + slotError (scale n) (floor n) (trembleSlots setup bounds).card) *
      (1 + slotError (scale n) (floor n) (trembleSlots setup bounds).card)))

end Vegas
