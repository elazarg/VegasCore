/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketRevealMasses
import Vegas.Game.OnePacketDelivery

/-! # Mixtures of slot-trembled components

A mixture of slot-trembled components sharing their scale, alternative and slot
tier is the slot-trembled component of the mixed main law
(`Vegas.bind_slotTrembledChoice`). So the late component of a weighted late
option is the slot-trembled component of the weighted late choice
(`Vegas.bind_lateComponent`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

/-- A mixture of mixtures sharing their first law is the mixture of the mixed
second laws. -/
theorem bind_mix_right {α β : Type} (weights : PMF α) (t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (fixed : PMF β) (varying : α → PMF β) :
    weights.bind (fun option => mix t h0 h1 fixed (varying option)) =
      mix t h0 h1 fixed (weights.bind varying) := by
  ext b
  rw [PMF.bind_apply]
  change ∑' option, weights option * (ENNReal.ofReal t * fixed b +
      ENNReal.ofReal (1 - t) * varying option b) =
    ENNReal.ofReal t * fixed b + ENNReal.ofReal (1 - t) * (weights.bind varying) b
  rw [PMF.bind_apply]
  simp only [mul_add]
  rw [ENNReal.tsum_add, ← ENNReal.tsum_mul_left]
  congr 1
  · rw [show (fun option => weights option * (ENNReal.ofReal t * fixed b)) =
        fun option => weights option * (ENNReal.ofReal t * fixed b) from rfl,
      ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  · refine tsum_congr fun option => ?_
    ring

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

/-- **Mixed slot-trembled components.** A mixture of slot-trembled components
sharing their scale, alternative and slot tier is the slot-trembled component
of the mixed main law. -/
theorem bind_slotTrembledChoice {α : Type} (weights : PMF α) (scale : ℝ) (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup leaks).Info)
    (main : α → PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info))
    (alternative slot :
      PMF ((onePacketModel setup leaks bounds initial horizon scheduler).Choice who info)) :
    weights.bind (fun option => slotTrembledChoice setup leaks bounds initial horizon scheduler
        scale nonnegative le_one who info (main option) alternative slot) =
      slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one
        who info (weights.bind main) alternative slot := by
  unfold slotTrembledChoice
  rw [bind_mix_right, bind_mix_right, bind_mix_right]

/-- **The weighted late component** is the slot-trembled component of the
weighted late choice. -/
theorem bind_lateComponent (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (weights : PMF (LateOption slots)) (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup leaks).Info) :
    weights.bind (lateComponent setup leaks bounds initial horizon scheduler assessment scale
        nonnegative le_one who info) =
      slotTrembledChoice setup leaks bounds initial horizon scheduler scale nonnegative le_one
        who info
        (weights.bind (lateChoice setup leaks bounds initial horizon scheduler assessment who info))
        (PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who info))
        (slotChoice setup leaks bounds initial horizon scheduler assessment who info) :=
  bind_slotTrembledChoice setup leaks bounds initial horizon scheduler weights scale nonnegative
    le_one who info _ _ _

variable {setup leaks bounds initial horizon scheduler}

/-- **Slot-tier choices at a fixed slot.** At a covered pending binding, the
as-if-honest law sent at a fixed slot gives an offered slot-tier choice of a
supported source choice its as-if-honest mass at that slot, and nothing at
another slot. -/
theorem map_slotChoiceOf_apply {assessment : setup.intendedModel.BehavioralAssessment}
    {who : Player} {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} {event : (graph setup).EventId}
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (site : CoveredPendingBinding setup leaks bounds assessment who past view event payload
      outputEq codeEq) (serial : Nat) {slot : Nat}
    {choice : Option (OwnAction Player L)}
    (supported : choice ∈ (asIfHonestProfile setup leaks assessment who
      (some (past, view))).support) (slotCapacity : slot < bounds.candidateCount)
    (offered : slotResponse setup leaks who past view event slot choice ∈
      bounds.onePacketActions (runtime setup) leaks who past view) :
    (asIfHonestProfile setup leaks assessment who (some (past, view))).map
        (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event serial)
        (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event slot
          choice) =
      if slot = serial then
        asIfHonestProfile setup leaks assessment who (some (past, view)) choice
      else 0 := by
  split
  · rename_i same
    subst same
    exact map_apply_of_injOn _ (slotChoiceOf setup leaks bounds initial horizon scheduler who past
      view event slot) choice fun other otherSupported equal =>
        (slotChoiceOf_injective setup leaks bounds initial horizon scheduler who past view event
          site.node site.freshOfPermitted slotCapacity slotCapacity (site.covered choice supported)
          (site.covered other otherSupported) offered equal).2
  · rename_i different
    apply map_apply_eq_zero_of_forall_ne
    intro other otherSupported equal
    by_cases serialCapacity : serial < bounds.candidateCount
    · exact different (slotChoiceOf_injective setup leaks bounds initial horizon scheduler who past
        view event site.node site.freshOfPermitted slotCapacity serialCapacity
        (site.covered choice supported) (site.covered other otherSupported) offered equal).1.symm
    · obtain ⟨action, encoded, _⟩ := site.covered choice supported
      obtain ⟨material, transmits, _⟩ := slotResponse_transmission setup leaks who past view
        event site.node slot choice action encoded
      have values := congrArg Subtype.val equal
      have offeredValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
          event slot choice).1 = some (slotResponse setup leaks who past view event slot choice) :=
        by simp only [slotChoiceOf, responseChoice, offered, ↓reduceDIte]
      rw [offeredValue] at values
      by_cases otherOffered : slotResponse setup leaks who past view event serial other ∈
          bounds.onePacketActions (runtime setup) leaks who past view
      · obtain ⟨otherAction, otherEncoded, _⟩ := site.covered other otherSupported
        obtain ⟨otherMaterial, otherTransmits, otherEnvelope⟩ := slotResponse_transmission setup
          leaks who past view event site.node serial other otherAction otherEncoded
        have effective := ((bounds.mem_onePacketActions (runtime setup) leaks who past view
          _).mp otherOffered).1
        have packetEq : otherMaterial.call.packet = .commitment event (who, .prepared serial) :=
          congrArg (fun message : Message Player (WitnessedPacket (graph setup)) =>
            message.payload.call) otherEnvelope
        exact serialCapacity (offered_commitment_capacity who past view _ effective
          otherMaterial otherTransmits packetEq)
      · have otherValue : (slotChoiceOf setup leaks bounds initial horizon scheduler who past view
            event serial other).1 = some ⟨none⟩ := by
          simp only [slotChoiceOf, responseChoice, otherOffered, ↓reduceDIte]
        rw [otherValue] at values
        have silent := congrArg ReactiveApplication.Action.transmission (Option.some.inj values)
        rw [transmits] at silent
        cases silent

/-- At the player's turn, the late choice of sending at a slot is the
as-if-honest law sent at that slot. -/
theorem lateChoice_some_eq_map (assessment : setup.intendedModel.BehavioralAssessment)
    {slots : Nat} (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event) (slot : Fin slots) :
    lateChoice setup leaks bounds initial horizon scheduler assessment who (some (past, view))
        (some slot) =
      (asIfHonestProfile setup leaks assessment who (some (past, view))).map
        (slotChoiceOf setup leaks bounds initial horizon scheduler who past view event
          slot.val) := by
  change (lateResponse setup leaks assessment who past view (some slot)).map _ = _
  unfold lateResponse
  rw [turn]
  dsimp only
  rw [PMF.map_comp]
  rfl

/-- The late choice of waiting is silence. -/
theorem lateChoice_none (assessment : setup.intendedModel.BehavioralAssessment) {slots : Nat}
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    lateChoice (slots := slots) setup leaks bounds initial horizon scheduler assessment who
        (some (past, view)) none =
      PMF.pure (silenceChoice setup leaks bounds initial horizon scheduler who
        (some (past, view))) := by
  change (PMF.pure (⟨none⟩ : (application setup leaks).Action)).map _ = _
  rw [PMF.pure_map]
  rfl

end Vegas
