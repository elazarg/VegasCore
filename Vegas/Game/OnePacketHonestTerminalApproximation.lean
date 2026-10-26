/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.StoppedHonestResponseCount
import Vegas.Game.SourceTerminalComparison
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Terminal honest-law approximation by actual response opportunities -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (initial : PMF (application setup runtime leaks).State)
  (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)

local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) initial horizon scheduler

theorem onePacket_terminal_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup runtime leaks bounds initial horizon scheduler assessment
      retention profile start) :
    PMF.WithinTV ((1 - retention) * (menu).expectedResponses initial horizon scheduler certificate
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) (fun _ =>
          False)
        start)
      ((N).runBehavioralTerminalFrom certificate
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) start)
      ((N).runBehavioralTerminalFrom certificate profile start) := by
  rw [(N).runBehavioralTerminalFrom_eq_until_false,
    (N).runBehavioralTerminalFrom_eq_until_false]
  exact onePacket_stopped_withinTV_honest setup runtime leaks bounds initial horizon
    scheduler assessment
    certificate (fun _ => False) profile start nonnegative le_one dominates

/-- The uniform initialized error has one possible response per scheduler
round, with no ambient-player or environment-step multiplier. -/
theorem onePacket_bounded_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (profile : ∀ who, (N).BehavioralPolicy who)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom setup runtime leaks bounds initial horizon scheduler assessment
      retention profile (E).initHistory) :
    PMF.WithinTV ((min (Fintype.card Player) 1 * horizon : ℕ) * (1 - retention))
      ((N).runBehavioral
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) (2 *
          horizon + 1))
      ((N).runBehavioral profile (2 * horizon + 1)) := by
  classical
  by_cases inhabited : Nonempty Player
  · let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
    have close := onePacket_terminal_withinTV_honest setup runtime leaks bounds initial horizon
      scheduler
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
      (honestProfile setup runtime leaks bounds initial horizon scheduler assessment) (fun _ =>
        False)
      (E).initHistory).2
    change _ ≤ (horizon : ℝ) at budget
    nlinarith
  · have same : profile =
        honestProfile setup runtime leaks bounds initial horizon scheduler assessment := by
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
        (honestProfile setup runtime leaks bounds initial horizon scheduler assessment)
        (2 * horizon + 1)).map (fun final => sourceReadout setup runtime leaks final.state) =
      (setup.intendedModel.runBehavioral intended sourceFuel).map
        (fun final => setup.protocolReadout final.state))
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (dominates : DominatesHonestFrom setup runtime leaks bounds initial horizon scheduler assessment
      retention profile (E).initHistory) :
    PMF.WithinTV ((min (Fintype.card Player) 1 * horizon : ℕ) * (1 - retention))
      (((N).runBehavioral profile (2 * horizon + 1)).map
        (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
          excludedPayoff))
      ((setup.intendedModel.runBehavioral intended sourceFuel).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff)) := by
  classical
  let certificate := ((menu).bounded initial horizon scheduler).wellFoundedHistories
  let honest := honestProfile setup runtime leaks bounds initial horizon scheduler assessment
  let complete := fun history : (E).History =>
    NativeSourceTerminal (runtime := runtime) (setup := setup) (leaks := leaks) history.state
  have close := onePacket_sourceTerminal_readout_exclusion_withinTV_honest setup runtime
    leaks bounds initial horizon scheduler parameter utility excludedPayoff assessment
      certificate profile
    (E).initHistory nonnegative le_one dominates
  have counted : (menu).expectedResponses initial horizon scheduler certificate honest complete
      (E).initHistory ≤ (min (Fintype.card Player) 1 * horizon : Nat) := by
    by_cases inhabited : Nonempty Player
    · have countBound := ((menu).expectedResponses_bounds initial horizon scheduler certificate
        honest complete (E).initHistory).2
      have playerCount : 1 ≤ Fintype.card Player := Fintype.card_pos_iff.mpr inhabited
      simpa only [Nat.min_eq_right playerCount, one_mul,
        show (application setup runtime leaks).remainingResponses horizon (E).initHistory.state =
          horizon
          from rfl] using countBound
    · have counts : ∀ history : (E).History,
          (application setup runtime leaks).responseCount history.state = 0 := by
        intro history
        cases history.state with
        | none => rfl
        | some control =>
            apply Finset.sum_eq_zero
            intro who _
            exact (inhabited ⟨who⟩).elim
      simp only [ReactiveApplication.ResponseMenu.expectedResponses, counts, Nat.cast_zero,
        expect_zero, sub_self]
      exact Nat.cast_nonneg _
  have exposureBound : (1 - retention) * (menu).expectedResponses initial horizon scheduler
      certificate honest complete (E).initHistory ≤
        ((min (Fintype.card Player) 1 * horizon : Nat) : ℝ) * (1 - retention) :=
    (mul_le_mul_of_nonneg_left counted (sub_nonneg.mpr le_one)).trans_eq (mul_comm _ _)
  have coarse := close.mono exposureBound
  rw [(N).runBehavioralTerminalFrom_initHistory certificate _
      ((menu).bounded initial horizon scheduler),
    (N).runBehavioralTerminalFrom_initHistory certificate _
      ((menu).bounded initial horizon scheduler)] at coarse
  let attach := fun readout : Option (State L setup.program.terminalCtx) =>
    (readout, exclusionReadoutUtility setup parameter utility excludedPayoff readout)
  have native : readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter
    utility
      excludedPayoff = attach ∘ fun final => sourceReadout setup runtime leaks final.state := rfl
  have source : intendedReadoutExclusion setup parameter utility excludedPayoff =
      attach ∘ fun final => setup.protocolReadout final.state := rfl
  have jointLaw : ((N).runBehavioral honest (2 * horizon + 1)).map
      (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
        excludedPayoff) =
        (setup.intendedModel.runBehavioral intended sourceFuel).map
          (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
    rw [native, source, ← PMF.map_comp, ← PMF.map_comp, honestLaw]
  rw [← jointLaw]
  exact coarse.symm

end Vegas
