/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceTerminalReadout
import Vegas.Game.StoppedHonestResponseCount

/-! # Honest readout comparisons charge only responses before source completion

The selected observation is the complete source readout, optionally paired with
its native fixed-exit payoff vector. The native configuration freezes once the
source cut completes, so later responses preserve this joint observation.
-/

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
local notation "N" =>
  onePacketModel (runtime := runtime) setup leaks bounds initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol (menu) initial horizon scheduler
local notation "complete" => (fun history : (E).History =>
  NativeSourceTerminal (runtime := runtime) (setup := setup) (leaks := leaks) (History.state
    history))

/-- Stopping at source completion preserves the actual joint native readout
and fixed-exit payoff law for every continuation profile. -/
theorem sourceTerminal_readout_exclusion_law
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History) :
    (((N).runBehavioralTerminalFrom certificate profile start).map
      (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
        excludedPayoff)) =
      (((N).runBehavioralUntil certificate profile complete start).map
        (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter utility
          excludedPayoff)) := by
  apply InformationModel.runBehavioralTerminalFrom_map_eq_until_of_stable_readout
    (N) certificate profile complete _ _ start
  intro history terminal final supported
  apply Prod.ext
  · exact sourceTerminal_readout_stable (runtime := runtime) (menu) initial horizon scheduler
      certificate profile history terminal final supported
  · exact sourceTerminal_exclusionBase_stable setup runtime parameter utility excludedPayoff leaks
      (menu) initial horizon scheduler certificate profile history terminal final supported

/-- Every legal continuation is compared at its actual readout-freeze time.
The conditional budget counts honest callbacks only until source completion. -/
theorem onePacket_sourceTerminal_readout_withinTV_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom (runtime := runtime) setup leaks bounds
      initial horizon scheduler assessment
      retention profile start) :
    PMF.WithinTV ((1 - retention) * (menu).expectedResponses initial horizon scheduler certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) complete start)
      (((N).runBehavioralTerminalFrom certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) start).map
        (fun final => sourceReadout setup runtime leaks final.state))
      (((N).runBehavioralTerminalFrom certificate profile start).map
        (fun final => sourceReadout setup runtime leaks final.state)) := by
  have close := onePacket_stopped_withinTV_honest (runtime := runtime) setup leaks bounds
    initial horizon scheduler
    assessment certificate complete profile start nonnegative le_one dominates
  rw [sourceTerminal_readout_law (menu) initial horizon scheduler certificate,
    sourceTerminal_readout_law (menu) initial horizon scheduler certificate]
  exact close.map _

/-- The same stopping budget covers the actual joint source readout and native
fixed-exit payoff, including defaults before a readout becomes available. -/
theorem onePacket_sourceTerminal_readout_exclusion_withinTV_honest
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom (runtime := runtime) setup leaks bounds
      initial horizon scheduler assessment
      retention profile start) :
    PMF.WithinTV ((1 - retention) * (menu).expectedResponses initial horizon scheduler certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) complete start)
      (((N).runBehavioralTerminalFrom certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) start).map
        (readoutExclusion (runtime := runtime) setup leaks bounds initial horizon
          scheduler parameter utility
          excludedPayoff))
      (((N).runBehavioralTerminalFrom certificate profile start).map
        (readoutExclusion (runtime := runtime) setup leaks bounds initial horizon
          scheduler parameter utility
          excludedPayoff)) := by
  have close := onePacket_stopped_withinTV_honest (runtime := runtime) setup leaks bounds
    initial horizon scheduler assessment certificate complete profile start nonnegative le_one
    dominates
  rw [sourceTerminal_readout_exclusion_law setup runtime leaks bounds initial horizon scheduler
      parameter utility excludedPayoff certificate,
    sourceTerminal_readout_exclusion_law setup runtime leaks bounds initial horizon scheduler
      parameter utility excludedPayoff certificate]
  exact close.map (readoutExclusion setup runtime leaks bounds initial horizon scheduler parameter
    utility excludedPayoff)

/-- Every utility of that typed readout, in particular each player's original
exclusion utility, has the conditional readout-freeze error budget. -/
theorem onePacket_sourceTerminal_payoff_sub_le_honest
    (assessment : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who) (start : (E).History)
    {retention : ℝ} (nonnegative : 0 ≤ retention) (le_one : retention ≤ 1)
    (dominates : DominatesHonestFrom (runtime := runtime) setup leaks bounds
      initial horizon scheduler assessment
      retention profile start)
    (payoff : Option (Config Player L setup.program.terminalCtx) → ℝ) {low width : ℝ}
    (payoffBounded : ∀ readout, low ≤ payoff readout ∧ payoff readout ≤ low + width) :
    |expect ((N).runBehavioralTerminalFrom certificate profile start)
        (fun final => payoff (sourceReadout setup runtime leaks final.state)) -
      expect ((N).runBehavioralTerminalFrom certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) start)
        (fun final => payoff (sourceReadout setup runtime leaks final.state))| ≤
      width * ((1 - retention) * (menu).expectedResponses initial horizon scheduler certificate
        (honestProfile (runtime := runtime) setup leaks bounds initial horizon
          scheduler assessment) complete
        start) := by
  have close := onePacket_sourceTerminal_readout_withinTV_honest (runtime := runtime) setup
    leaks bounds initial horizon
    scheduler assessment certificate profile start nonnegative le_one dominates
  have first := close.expect_sub_le payoff low width (fun readout _ => payoffBounded readout)
  have second := close.symm.expect_sub_le payoff low width (fun readout _ => payoffBounded readout)
  rw [expect_map, expect_map] at first second
  dsimp only [Function.comp_def] at first second
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

end Vegas
