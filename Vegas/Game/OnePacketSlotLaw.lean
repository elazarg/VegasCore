/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketHonestForced
import Vegas.Game.OnePacketSlotTrembles

/-! # The law approximation for slot-trembled components

A slot-trembled component keeps the fraction
`(1 - scale³)(1 - scale²)(1 - scale)` of its main law (`Vegas.slotRetention`,
`Vegas.slotTrembledChoice_ge_main`), which tends to one along vanishing scales
(`Vegas.tendsto_slotRetention`). Profiles playing, at every forced information
state, a slot-trembled component whose main law is as-if-honest play therefore
satisfy the law approximation with exclusion payoffs
(`Vegas.onePacket_slot_lawApproximation`), whatever their alternative and slot
laws.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

/-- The fraction of its main law a slot-trembled component keeps. -/
def slotRetention (scale : ℝ) : ℝ := (1 - scale ^ 3) * (1 - scale ^ 2) * (1 - scale)

theorem slotRetention_nonneg {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    0 ≤ slotRetention scale := by
  unfold slotRetention
  have : scale ^ 3 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : scale ^ 2 ≤ 1 := pow_le_one₀ nonnegative le_one
  have : 0 ≤ 1 - scale := by linarith
  have : 0 ≤ 1 - scale ^ 3 := by linarith
  have : 0 ≤ 1 - scale ^ 2 := by linarith
  positivity

theorem slotRetention_le_one {scale : ℝ} (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1) :
    slotRetention scale ≤ 1 :=
  slotFactor_le_one nonnegative le_one

/-- Along vanishing tremble scales the slot retention tends to one. -/
theorem tendsto_slotRetention {scales : ℕ → ℝ} (vanishing : Tendsto scales atTop (nhds 0)) :
    Tendsto (fun n => slotRetention (scales n)) atTop (nhds 1) := by
  have limit := (((tendsto_const_nhds (x := (1 : ℝ))).sub (vanishing.pow 3)).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub (vanishing.pow 2))).mul
    ((tendsto_const_nhds (x := (1 : ℝ))).sub vanishing)
  simpa [slotRetention] using limit

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **The law approximation for slot-trembled components.** Under the
hypotheses of `onePacket_exclusion_lawApproximation`, along vanishing tremble
scales in `[0, 1]`, profiles playing, at every forced information state, a
slot-trembled component whose main law is as-if-honest play satisfy the law
approximation with exclusion payoffs. -/
theorem onePacket_slot_lawApproximation [Fintype Player] (bounds : MessageBounds (graph setup))
    (wellFormed : setup.WellFormed) {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (retains : RetainsFirstCanonical setup leaks bounds bound)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessments : ℕ → setup.intendedModel.BehavioralAssessment)
    (scales : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ scales n) (le_one : ∀ n, scales n ≤ 1)
    (vanishing : Tendsto scales atTop (nhds 0))
    (profiles : ℕ → ∀ who,
      (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (slotted : ∀ n who info,
      forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
        scheduler who info →
      ∃ alternative slot, profiles n who info =
        slotTrembledChoice setup leaks bounds (initialLaw setup) horizon scheduler (scales n)
          (nonnegative n) (le_one n) who info
          (honestChoice setup leaks bounds (initialLaw setup) horizon scheduler (assessments n)
            who info) alternative slot) :
    ∃ lawError : ℕ → ℝ, Tendsto lawError atTop (nhds 0) ∧
      ∀ n outcome,
        |((((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).runBehavioral
            (profiles n) (2 * horizon + 1)).map
            (readoutExclusion setup leaks bounds (initialLaw setup) horizon scheduler parameter
              utility excludedPayoff)) outcome).toReal -
          (((setup.intendedModel.runBehavioral (assessments n).strategy
            (instructionCount setup.program + 1)).map
            (intendedReadoutExclusion setup parameter utility excludedPayoff))
            outcome).toReal| ≤ lawError n :=
  onePacket_exclusion_lawApproximation bounds wellFormed contract timely retains parameter utility
    excludedPayoff assessments (fun n => slotRetention (scales n))
    (fun n => slotRetention_nonneg (nonnegative n) (le_one n))
    (fun n => slotRetention_le_one (nonnegative n) (le_one n))
    (tendsto_slotRetention vanishing) profiles fun n who info _ forced choice => by
      obtain ⟨alternative, slot, profileEq⟩ := slotted n who info forced
      rw [profileEq]
      exact slotTrembledChoice_ge_main setup leaks bounds (initialLaw setup) horizon scheduler
        (nonnegative n) (le_one n) who _ _ _ _ choice

end Vegas
