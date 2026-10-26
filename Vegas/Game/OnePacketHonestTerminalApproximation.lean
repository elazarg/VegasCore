/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.StoppedHonestResponseCount
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Terminal honest-law approximation by actual response opportunities -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup leaks).State)
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)

local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu (runtime setup) leaks) initial horizon scheduler

theorem onePacket_terminal_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile start) :
    PMF.WithinTV ((1 - retention) * (menu).expectedResponses initial horizon scheduler certificate
        (honestProfile setup leaks bounds initial horizon scheduler assessment) (fun _ => False)
        start)
      ((N).runBehavioralTerminalFrom certificate
        (honestProfile setup leaks bounds initial horizon scheduler assessment) start)
      ((N).runBehavioralTerminalFrom certificate profile start) := by
  rw [(N).runBehavioralTerminalFrom_eq_until_false,
    (N).runBehavioralTerminalFrom_eq_until_false]
  exact onePacket_stopped_withinTV_honest setup leaks bounds initial horizon scheduler assessment
    certificate (fun _ => False) profile start nonnegative le_one dominates

/-- The uniform initialized error has one possible response per scheduler
round, with no ambient-player or environment-step multiplier. -/
theorem onePacket_bounded_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (profile : ∀ who, (N).BehavioralPolicy who)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile (E).initHistory) :
    PMF.WithinTV ((min (Fintype.card Player) 1 * horizon : ℕ) * (1 - retention))
      ((N).runBehavioral
        (honestProfile setup leaks bounds initial horizon scheduler assessment) (2 * horizon + 1))
      ((N).runBehavioral profile (2 * horizon + 1)) := by
  classical
  by_cases inhabited : Nonempty Player
  · let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    have close := onePacket_terminal_withinTV_honest setup leaks bounds initial horizon scheduler
      assessment certificate profile (E).initHistory nonnegative le_one dominates
    rw [(N).runBehavioralTerminalFrom_initHistory certificate _
        ((menu).bounded initial horizon scheduler),
      (N).runBehavioralTerminalFrom_initHistory certificate _
        ((menu).bounded initial horizon scheduler)] at close
    have activePopulation : min (Fintype.card Player) 1 = 1 :=
      Nat.min_eq_right (Fintype.card_pos_iff.mpr inhabited)
    simp only [activePopulation, one_mul]
    apply close.mono
    have budget := ((menu).expectedResponses_bounds initial horizon scheduler certificate
      (honestProfile setup leaks bounds initial horizon scheduler assessment) (fun _ => False)
      (E).initHistory).2
    change _ ≤ (horizon : ℝ) at budget
    nlinarith
  · have same : profile =
        honestProfile setup leaks bounds initial horizon scheduler assessment := by
      funext who
      exact (inhabited ⟨who⟩).elim
    rw [same]
    exact (PMF.WithinTV.refl _).mono (by positivity)

/-- An exact honest readout law transfers the horizon response bound to the
joint typed readout and the original parameter-dependent exclusion payoff. -/
theorem onePacket_bounded_readout_exclusion_withinTV
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (sourceFuel : Nat)
    (honestLaw : ((N).runBehavioral
        (honestProfile setup leaks bounds initial horizon scheduler assessment)
        (2 * horizon + 1)).map (fun final => sourceReadout setup leaks final.state) =
      (setup.intendedModel.runBehavioral intended sourceFuel).map
        (fun final => setup.protocolReadout final.state))
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup leaks bounds initial horizon scheduler assessment
      retention profile (E).initHistory) :
    PMF.WithinTV ((min (Fintype.card Player) 1 * horizon : ℕ) * (1 - retention))
      (((N).runBehavioral profile (2 * horizon + 1)).map
        (readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
          excludedPayoff))
      ((setup.intendedModel.runBehavioral intended sourceFuel).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  let attach := fun readout : Option (State L setup.program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup parameter utility excludedPayoff readout)
  have native : readoutExclusion setup leaks bounds initial horizon scheduler parameter utility
      excludedPayoff = attach ∘ fun final => sourceReadout setup leaks final.state := rfl
  have source : intendedReadoutExclusion setup parameter utility excludedPayoff =
      attach ∘ fun final => setup.protocolReadout final.state := rfl
  rw [native, source, ← PMF.map_comp, ← PMF.map_comp, ← honestLaw, PMF.map_comp,
    PMF.map_comp]
  exact ((onePacket_bounded_withinTV_honest setup leaks bounds initial horizon scheduler
    assessment profile nonnegative le_one dominates).map _).symm

end Vegas
