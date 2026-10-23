/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotTrembles
import Vegas.Game.OnePacketPrescribedSupport

/-! # Late-delivery options

A late option waits or sends now at one of the first prepared slots
(`Vegas.LateOption`); sending takes the slot tier's response at that slot with
the as-if-honest source choice: the value committed at that slot at a binding,
the canonical decision at a reveal, which has no slot (`Vegas.lateResponse`). A
scheduler may treat slots differently for late packets, so a late option
chooses both the time and the slot. Its law over one-packet choices is
`Vegas.lateChoice`. Each option has a fully supported slot-trembled component
(`Vegas.lateComponent`, `Vegas.lateComponent_fullSupport`) keeping all but
three times the scale of the option's mass (`Vegas.lateComponent_ge`).

For the one-packet game, the file also names the late-delivery key of a played
agent (`Vegas.agentLateKey`), the late-delivery agents
(`Vegas.LateDeliveryAgent`), and the typed readout of a native history
(`Vegas.nativeReadout`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

section LateRule

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A late-delivery option among the first `slots` prepared slots: wait, or
send now at a slot. A reveal has no slot, and every slot sends its opening. -/
abbrev LateOption (slots : Nat) := Option (Fin slots)

/-- **A late response.** Waiting is silence. Sending at a slot draws the
as-if-honest source choice and, at the player's turn, takes the slot tier's
response at that slot (`Vegas.slotResponse`): at a binding the encoded value
committed at the slot, normalized as a canonical decision is, and at any other
event the canonical decision. It is silence away from the player's turn. -/
def lateResponse (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    LateOption slots → PMF (application setup leaks).Action
  | none => PMF.pure ⟨none⟩
  | some slot =>
      match view.application.publicView.ownTurn? who with
      | none => PMF.pure ⟨none⟩
      | some event => (asIfHonestProfile setup leaks assessment who (some (past, view))).map
          (slotResponse setup leaks who past view event slot.val)

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- A late option as a law over one-packet choices. -/
def lateChoice (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (who : Player) :
    (info : (application setup leaks).Info) → LateOption slots →
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)
  | none, _ => PMF.pure ⟨none, rfl⟩
  | some (past, view), option => (lateResponse setup leaks assessment who past view option).map
      (responseChoice setup leaks bounds initial horizon scheduler who (some (past, view)))

/-- **The late component of an option.** The late option slot-trembled, with
silence as its timing deviation and the value-preserving slot tier. -/
def lateComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots) :
    PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :=
  slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one who info
    (lateChoice setup leaks bounds initial horizon scheduler assessment who info option)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
    (slotChoice setup leaks bounds initial horizon scheduler assessment who info)

theorem lateComponent_fullSupport (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots) :
    FullSupport (lateComponent setup leaks bounds initial horizon scheduler assessment scale
      positive.le le_one who info option) :=
  slotTrembledChoice_fullSupport setup leaks bounds initial horizon scheduler positive le_one who
    info _ _ _

/-- The late component of an option keeps at least `1 - 3 scale` of the mass
of the option's late choice. -/
theorem lateComponent_ge (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup leaks).Info) (option : LateOption slots)
    (choice : (onePacketModel setup leaks bounds initial horizon scheduler).Choice who info) :
    (1 - 3 * scale) *
        (lateChoice setup leaks bounds initial horizon scheduler assessment who info option
          choice).toReal ≤
      (lateComponent setup leaks bounds initial horizon scheduler assessment scale nonnegative
        le_one who info option choice).toReal := by
  have main := slotTrembledChoice_ge_main setup leaks bounds initial horizon scheduler
    nonnegative le_one who info
    (lateChoice setup leaks bounds initial horizon scheduler assessment who info option)
    (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
    (slotChoice setup leaks bounds initial horizon scheduler assessment who info) choice
  have factor := slotFactor_ge nonnegative le_one
  have mass : 0 ≤ (lateChoice setup leaks bounds initial horizon scheduler assessment who info
      option choice).toReal := ENNReal.toReal_nonneg
  exact (mul_le_mul_of_nonneg_right factor mass).trans main

variable
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

end LateRule

section Pools

variable [Fintype Player]
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

/-- The late-delivery key of a played agent of the one-packet game. -/
def agentLateKey (agent : (onePacketModel setup leaks bounds initial horizon
    scheduler).InformationAgent (onePacketModel setup leaks bounds initial horizon
    scheduler).playedInformation) : Option (LateKey setup leaks) :=
  lateKey setup leaks agent.1 agent.2.1

end Pools

section Obligations

variable [Fintype Player]
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
  [Fintype ((bounds.onePacketMenu (runtime setup) leaks).protocol initial horizon
    scheduler).History]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds initial horizon scheduler).InfoState who)]

local notation "onePacketN" => onePacketModel setup leaks bounds initial horizon scheduler

/-- The late-delivery agents of the one-packet game: the agents at late
deliveries (`Vegas.LateDelivery`). -/
def LateDeliveryAgent (agent : (onePacketN).InformationAgent (onePacketN).playedInformation) :
    Prop :=
  LateDelivery setup leaks agent.1 agent.2.1

/-- The typed readout of a native history. -/
abbrev nativeReadout (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol initial
    horizon scheduler).History) : Option (State L setup.program.terminalCtx) :=
  sourceReadout setup leaks history.state

end Obligations

end Vegas
