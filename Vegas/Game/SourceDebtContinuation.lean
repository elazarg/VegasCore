/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceFailureReadout
import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport

/-! # Fixed exit utility for continuations carrying source debt

Debt follows the ordinary source decoder through every native transition.
At completed initialized histories, source publication provenance turns that
debt into the same public default recorded by the ledger.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {profile : BehavioralProfile setup.program}

/-- Once a native history completes, latent source debt has the declared exit
utility. Publication provenance is obtained from the initialized history. -/
theorem decoded_owesFailure_exclusionBase_of_complete {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    {menu : (application setup runtime leaks).ResponseMenu} {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) history.state)
    (control : (application setup runtime leaks).Control) (current : history.state = some control)
    (complete : control.execution.application.config.cut.Terminal) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks history.state who =
      excludedPayoff who := by
  obtain ⟨terminal, readout⟩ := serviceSourceReadout_exists_of_terminal setup .sequential
    runtime.deadline leaks control complete
  exact decoded_owesFailure_exclusionBase_of_readout parameter utility excludedPayoff who history
    owed terminal (current ▸ readout)

variable [Fintype Player]

/-- Under complete play, every supported terminal continuation of an initialized
history carrying source debt pays its owner the fixed exit utility. -/
theorem exclusionBase_continuation_of_owesFailure {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) history.state) :
    ∀ final ∈ ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate players history).support,
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who =
        excludedPayoff who := by
  have preserved := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_closed certificate players
    (DecodedState setup runtime leaks profile (ProtocolState.OwesFailure who setup.program))
    (fun before joint _legal after holds reached =>
      decodedHolds_transition (owesFailure_stepClosed who) (initialLaw setup) horizon scheduler
        before after joint holds reached) history owed
  intro final supported
  have remains := preserved final supported
  have stopped := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_terminal certificate players history final
      supported
  cases current : final.state with
  | none => rw [current] at remains; exact remains.elim
  | some control =>
      rw [current] at stopped
      have trace := current ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
      simpa only [current] using decoded_owesFailure_exclusionBase_of_complete parameter utility
        excludedPayoff who final remains control current (completes control trace stopped)

/-- The whole completed continuation carrying source debt is integrable and
has the declared exit expectation, without an ordinary utility range bound. -/
theorem exclusionBase_expect_of_owesFailure {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) history.state) :
    let law := (menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
      certificate players history
    PayoffIntegrable law (fun final =>
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) ∧
    expect law (fun final =>
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) =
        excludedPayoff who := by
  have fixed := exclusionBase_continuation_of_owesFailure parameter utility excludedPayoff menu
    horizon scheduler completes certificate players who history owed
  refine ⟨payoffIntegrable_congr_on_support (fun final supported => (fixed final supported).symm)
    (payoffIntegrable_constant _ _), ?_⟩
  exact (expect_congr_on_support fixed).trans (expect_constant _ _)

/-- At a history carrying source debt, every whole-policy deviation has zero
base-utility gain under complete play. -/
theorem exclusionBase_historyGain_eq_zero_of_owesFailure {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (assessment : (menu.information (initialLaw setup) horizon scheduler).BehavioralAssessment)
    {who : Player}
    (deviation : (menu.information (initialLaw setup) horizon scheduler).AssessmentDeviation who)
    (history : (menu.information (initialLaw setup) horizon scheduler).InformationHistory who
      deviation.1.1)
    (owed : DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
      who setup.program) history.1.state) :
    (menu.information (initialLaw setup) horizon scheduler).historyGain
      ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate)
      (fun final => final.state)
      (exclusionBase setup runtime parameter utility excludedPayoff leaks) assessment deviation
      history = 0 := by
  let model := menu.information (initialLaw setup) horizon scheduler
  have fixed (players : ∀ player, model.BehavioralPolicy player) :
      expect ((model.runBehavioralTerminalFrom certificate players history.1).map
        (fun final => final.state))
        (fun state => exclusionBase setup runtime parameter utility excludedPayoff leaks
          state who) = excludedPayoff who := by
    rw [expect_map]
    exact (exclusionBase_expect_of_owesFailure parameter utility excludedPayoff menu horizon
      scheduler completes certificate players who history.1 owed).2
  unfold InformationModel.historyGain
  exact sub_eq_zero.mpr ((fixed _).trans (fixed _).symm)

/-- Any belief supported on histories carrying own source debt makes every
whole-policy deviation indifferent under complete play. -/
theorem exclusionBase_gain_eq_zero_of_owesFailure {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup runtime leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    [Finite (menu.protocol (initialLaw setup) horizon scheduler).History]
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (assessment : (menu.information (initialLaw setup) horizon scheduler).BehavioralAssessment)
    {who : Player}
    (deviation : (menu.information (initialLaw setup) horizon scheduler).AssessmentDeviation who)
    (owed : ∀ history ∈ (assessment.belief who deviation.1).support,
      DecodedState setup runtime leaks profile (ProtocolState.OwesFailure
        who setup.program) history.1.state) :
    expect ((menu.information (initialLaw setup) horizon scheduler).assessmentComparisonWith
      ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate)
      (fun final => final.state) assessment who deviation).alternative
        (fun state => exclusionBase setup runtime parameter utility excludedPayoff leaks
          state who) -
    expect ((menu.information (initialLaw setup) horizon scheduler).assessmentComparisonWith
      ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate)
      (fun final => final.state) assessment who deviation).prescribed
        (fun state => exclusionBase setup runtime parameter utility excludedPayoff leaks
          state who) = 0 := by
  rw [(menu.information (initialLaw setup) horizon scheduler).gain_eq_expect_historyGain]
  rw [expect_congr_on_support (g := fun _ => 0) (fun history supported =>
    exclusionBase_historyGain_eq_zero_of_owesFailure parameter utility excludedPayoff menu horizon
      scheduler completes certificate assessment deviation history (owed history supported))]
  exact expect_constant _ _

end Vegas
