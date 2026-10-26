/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketTrembles

/-! # Value-preserving slot trembles

A tremble that draws a whole response uniformly from the menu can send a
commitment at a non-canonical handle slot, which is visible, with a uniformly
drawn value. Its slot then carries information about the value that honest play
does not. The components here keep the value law under a slot tremble.

**The slot tier.** At the owner's turn the slot tier draws a prepared slot
uniformly among the first `max 1 candidateCount` slots, and independently a
source choice from as-if-honest play (`Vegas.slotPairs`); a binding commits the
encoded value at the drawn slot, normalized as a canonical decision is, and any
other event takes the canonical
decision (`Vegas.slotResponse`). The joint law of slot and value is the
product (`Vegas.slotPairs_apply`), so the value law given any slot is the
as-if-honest law.

**Components.** A slot-trembled component puts the cube of the scale on the
uniform law over the one-packet menu, then its square on the slot tier, then
the scale on an alternative, and the rest on a main law
(`Vegas.slotTrembledChoice`). A main choice keeps at least
`(1 - scale³)(1 - scale²)(1 - scale)` of its main mass, which is at least
`1 - 3 scale` (`Vegas.slotTrembledChoice_ge_main`, `Vegas.slotFactor_ge`). A
choice has mass at most `scale³`, plus `scale²` times its slot-tier mass, plus
`scale` times its alternative mass, plus its main mass
(`Vegas.slotTrembledChoice_le`), so one outside all three laws has mass at most
`scale³` (`Vegas.slotTrembledChoice_le_of_unprescribed`). The prescribed
component sends the as-if-honest response with silence as its alternative
(`Vegas.slotPrescribedComponent`); any other main law, such as a late choice,
is slot-trembled by `Vegas.slotTrembledChoice` with silence as its alternative
and the slot tier.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

/-- The point mass of a product law built by drawing the first coordinate and
then the second independently is the product of the masses. -/
theorem bind_map_pair_apply {α β : Type} (first : PMF α) (second : PMF β) (a : α) (b : β) :
    (first.bind fun x => second.map (Prod.mk x)) (a, b) = first a * second b := by
  classical
  rw [PMF.bind_apply, tsum_eq_single a]
  · rw [PMF.map_apply, tsum_eq_single b]
    · simp
    · intro other different
      simp [Ne.symm different]
  · intro other different
    rw [PMF.map_apply]
    simp [Ne.symm different]

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section SlotTier

variable (bounds : MessageBounds (graph setup))

/-- The prepared slots the slot tier draws from: the first
`max 1 candidateCount` slots. -/
def trembleSlots : Finset Nat := Finset.range (max 1 bounds.candidateCount)

theorem trembleSlots_nonempty : (trembleSlots setup bounds).Nonempty :=
  ⟨0, Finset.mem_range.mpr (lt_of_lt_of_le zero_lt_one (le_max_left _ _))⟩

/-- The response of the slot tier for a drawn slot and source choice: at a
binding, commit the encoded value at the drawn slot, normalized as a canonical
decision is; at any other event, the
canonical decision of the encoded action; silence when nothing encodes. -/
def slotResponse (who : Player) (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) (event : (graph setup).EventId) (slot :
      Nat)
    (choice : Option (OwnAction Player L)) : (application setup runtime leaks).Action :=
  match choice.bind (encodeEventAction? setup.program event) with
  | none => ⟨none⟩
  | some action =>
      match nodeView (graph setup) event with
      | .bind _ payload outputEq _ =>
          (runtime.reactiveNormalization leaks).action who past view
            (runtime.reactiveBinding leaks who event payload
              (cast (congrArg EventGraph.EventField.Action outputEq) action) slot)
      | .resolve .. | .sample .. =>
          runtime.canonicalServiceDecision leaks who past view event action

/-- The slot and source choice of the slot tier: a uniform slot and,
independently, the as-if-honest choice. -/
def slotPairs (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) : PMF (Nat × Option (OwnAction Player
      L)) :=
  (PMF.uniformOfFinset (trembleSlots setup bounds)
      (trembleSlots_nonempty setup bounds)).bind fun slot =>
    (asIfHonestProfile setup runtime leaks assessment who (some (past, view))).map (Prod.mk slot)

/-- **The value law given a slot is the as-if-honest law.** The slot tier's
joint law of slot and source choice is the product of the uniform slot law and
the as-if-honest law. -/
theorem slotPairs_apply (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) (slot : Nat)
    (choice : Option (OwnAction Player L)) :
    slotPairs setup runtime leaks bounds assessment who past view (slot, choice) =
      PMF.uniformOfFinset (trembleSlots setup bounds) (trembleSlots_nonempty setup bounds) slot *
        asIfHonestProfile setup runtime leaks assessment who (some (past, view)) choice :=
  bind_map_pair_apply _ _ slot choice

/-- The responses of the slot tier at a player view: silence away from the
player's turn. -/
def slotTierResponse (assessment : setup.intendedModel.BehavioralAssessment) (who : Player)
    (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView) : PMF (application setup runtime
      leaks).Action :=
  match view.application.publicView.ownTurn? who with
  | none => PMF.pure ⟨none⟩
  | some event => (slotPairs setup runtime leaks bounds assessment who past view).map fun pair =>
      slotResponse setup runtime leaks who past view event pair.1 pair.2

variable [Fintype Player] (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

/-- The slot tier as a law over one-packet choices. -/
def slotChoice (assessment : setup.intendedModel.BehavioralAssessment) (who : Player) :
    (info : (application setup runtime leaks).Info) →
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info)
  | none => PMF.pure ⟨none, rfl⟩
  | some (past, view) => (slotTierResponse setup runtime leaks bounds assessment who past view).map
      (responseChoice setup runtime leaks bounds initial horizon scheduler who (some (past, view)))

end SlotTier

section Components

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

/-- **A slot-trembled component.** The cube of the scale on the uniform law
over the one-packet menu; of the rest, the square of the scale on the slot
law; of the rest, the scale on the alternative and the remainder on the main
law. -/
def slotTrembledChoice (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info)) :
    PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info) :=
  mix (scale ^ 3) (pow_nonneg nonnegative 3) (pow_le_one₀ nonnegative le_one)
    ((bounds.onePacketMenu runtime leaks).uniformPolicy initial horizon scheduler who info)
    (mix (scale ^ 2) (sq_nonneg _) (pow_le_one₀ nonnegative le_one) slot
      (mix scale nonnegative le_one alternative main))

/-- The real mass a slot-trembled component gives a choice. -/
theorem slotTrembledChoice_apply_toReal (scale : ℝ) (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who
      info) :
    (slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale nonnegative
      le_one who
        info main alternative slot choice).toReal =
      scale ^ 3 * ((bounds.onePacketMenu runtime leaks).uniformPolicy initial horizon
          scheduler who info choice).toReal +
        (1 - scale ^ 3) * (scale ^ 2 * (slot choice).toReal +
          (1 - scale ^ 2) * (scale * (alternative choice).toReal +
            (1 - scale) * (main choice).toReal)) := by
  unfold slotTrembledChoice
  rw [mix_apply_toReal, mix_apply_toReal, mix_apply_toReal]

/-- A slot-trembled component with a positive scale is fully supported. -/
theorem slotTrembledChoice_fullSupport {scale : ℝ} (positive : 0 < scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info)) :
    FullSupport (slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale
      positive.le le_one who info main alternative slot) := by
  intro choice
  let := Fintype.ofFinite
    ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info)
  exact mem_support_mix_left _ _ _ (pow_pos positive 3) (PMF.mem_support_uniformOfFintype choice)

private theorem unit_mass {α : Type} (law : PMF α) (a : α) :
    0 ≤ (law a).toReal ∧ (law a).toReal ≤ 1 :=
  ⟨ENNReal.toReal_nonneg,
    ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one law a)⟩

/-- **The main factor.** A slot-trembled component gives a choice at least
`(1 - scale³)(1 - scale²)(1 - scale)` times its main mass. -/
theorem slotTrembledChoice_ge_main {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who
      info) :
    (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) * (main choice).toReal ≤
      (slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale nonnegative
        le_one
        who info main alternative slot choice).toReal := by
  rw [slotTrembledChoice_apply_toReal]
  have uniform := unit_mass ((bounds.onePacketMenu runtime leaks).uniformPolicy initial
    horizon scheduler who info) choice
  have other := unit_mass alternative choice
  have tier := unit_mass slot choice
  have cube : 0 ≤ 1 - scale ^ 3 := by linarith [pow_le_one₀ (n := 3) nonnegative le_one]
  have square : 0 ≤ 1 - scale ^ 2 := by linarith [pow_le_one₀ (n := 2) nonnegative le_one]
  have : 0 ≤ scale ^ 3 * ((bounds.onePacketMenu runtime leaks).uniformPolicy initial
      horizon scheduler who info choice).toReal := mul_nonneg (pow_nonneg nonnegative 3) uniform.1
  have : 0 ≤ (1 - scale ^ 3) * (scale ^ 2 * (slot choice).toReal) :=
    mul_nonneg cube (mul_nonneg (sq_nonneg _) tier.1)
  have : 0 ≤ (1 - scale ^ 3) * ((1 - scale ^ 2) * (scale * (alternative choice).toReal)) :=
    mul_nonneg cube (mul_nonneg square (mul_nonneg nonnegative other.1))
  nlinarith

/-- The main factor is at least `1 - 3 scale`, so it tends to one with the
scale. -/
theorem slotFactor_ge {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    1 - 3 * scale ≤ (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) := by
  have cube : scale ^ 3 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have square : scale ^ 2 ≤ scale := pow_le_of_le_one nonnegative le_one (by norm_num)
  have cubeNonneg : 0 ≤ scale ^ 3 := pow_nonneg nonnegative 3
  have squareNonneg : 0 ≤ scale ^ 2 := sq_nonneg scale
  have first : 0 ≤ 1 - scale ^ 3 := by linarith
  have second : 0 ≤ 1 - scale ^ 2 := by linarith
  have pair : 1 - scale ^ 3 - scale ^ 2 ≤ (1 - scale ^ 3) * (1 - scale ^ 2) := by
    nlinarith [mul_nonneg cubeNonneg squareNonneg]
  have : (1 - scale ^ 3 - scale ^ 2) * (1 - scale) ≤
      (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) :=
    mul_le_mul_of_nonneg_right pair (by linarith)
  nlinarith [mul_nonneg (add_nonneg cubeNonneg squareNonneg) nonnegative]

theorem slotFactor_le_one {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) ≤ 1 := by
  have first : 0 ≤ 1 - scale ^ 3 := by linarith [pow_le_one₀ (n := 3) nonnegative le_one]
  have second : 0 ≤ 1 - scale ^ 2 := by linarith [pow_le_one₀ (n := 2) nonnegative le_one]
  have : (1 - scale ^ 3) * (1 - scale ^ 2) ≤ 1 := by
    nlinarith [pow_nonneg nonnegative 3, sq_nonneg scale]
  calc (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale) ≤ 1 * 1 :=
        mul_le_mul this (by linarith) (by linarith) zero_le_one
    _ = 1 := one_mul 1

/-- The general upper bound: the uniform tier at most the cube of the scale,
the slot tier at most its square, the alternative at most the scale. -/
theorem slotTrembledChoice_le {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who
      info) :
    (slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale nonnegative
      le_one
        who info main alternative slot choice).toReal ≤
      scale ^ 3 + scale ^ 2 * (slot choice).toReal + scale * (alternative choice).toReal +
        (main choice).toReal := by
  rw [slotTrembledChoice_apply_toReal]
  have uniform := unit_mass ((bounds.onePacketMenu runtime leaks).uniformPolicy initial
    horizon scheduler who info) choice
  have other := unit_mass alternative choice
  have tier := unit_mass slot choice
  have prescribed := unit_mass main choice
  have cubeLe : scale ^ 3 ≤ 1 := pow_le_one₀ nonnegative le_one
  have squareLe : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have cubeNonneg : 0 ≤ scale ^ 3 := pow_nonneg nonnegative 3
  have squareNonneg : 0 ≤ scale ^ 2 := sq_nonneg scale
  have inner : scale * (alternative choice).toReal + (1 - scale) * (main choice).toReal ≤
      scale * (alternative choice).toReal + (main choice).toReal := by
    nlinarith [mul_nonneg nonnegative prescribed.1]
  have innerNonneg : 0 ≤ scale * (alternative choice).toReal +
      (1 - scale) * (main choice).toReal :=
    add_nonneg (mul_nonneg nonnegative other.1) (mul_nonneg (by linarith) prescribed.1)
  have middle : scale ^ 2 * (slot choice).toReal + (1 - scale ^ 2) *
        (scale * (alternative choice).toReal + (1 - scale) * (main choice).toReal) ≤
      scale ^ 2 * (slot choice).toReal + (scale * (alternative choice).toReal +
        (main choice).toReal) := by
    nlinarith [mul_nonneg squareNonneg innerNonneg]
  have middleNonneg : 0 ≤ scale ^ 2 * (slot choice).toReal + (1 - scale ^ 2) *
      (scale * (alternative choice).toReal + (1 - scale) * (main choice).toReal) :=
    add_nonneg (mul_nonneg squareNonneg tier.1) (mul_nonneg (by linarith) innerNonneg)
  nlinarith [mul_le_mul_of_nonneg_left uniform.2 cubeNonneg,
    mul_nonneg cubeNonneg middleNonneg]

/-- **The full-menu tremble is of the order of the cube of the scale.** A
choice outside all three laws has mass at most `scale³`. -/
theorem slotTrembledChoice_le_of_unprescribed {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1) (who : Player) (info : (application setup runtime leaks).Info)
    (main alternative slot :
      PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info))
    (choice : (onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info)
    (outsideMain : main choice = 0) (outsideAlternative : alternative choice = 0)
    (outsideSlot : slot choice = 0) :
    (slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale nonnegative
      le_one
        who info main alternative slot choice).toReal ≤ scale ^ 3 := by
  have bound := slotTrembledChoice_le setup runtime leaks bounds initial horizon scheduler
    nonnegative
    le_one who info main alternative slot choice
  rw [outsideMain, outsideAlternative, outsideSlot, ENNReal.toReal_zero] at bound
  linarith

/-- **The slot-trembled prescribed component.** Send the as-if-honest
response; the timing deviation is silence; the slot tier keeps the as-if-honest
value law. -/
def slotPrescribedComponent (assessment : setup.intendedModel.BehavioralAssessment)
    (scale : ℝ) (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) (who : Player)
    (info : (application setup runtime leaks).Info) :
    PMF ((onePacketModel setup runtime leaks bounds initial horizon scheduler).Choice who info) :=
  slotTrembledChoice setup runtime leaks bounds initial horizon scheduler scale nonnegative le_one
    who info
    (honestChoice setup runtime leaks bounds initial horizon scheduler assessment who info)
    (PMF.pure (silenceChoice setup runtime leaks bounds initial horizon scheduler who info))
    (slotChoice setup runtime leaks bounds initial horizon scheduler assessment who info)

end Components

end Vegas
