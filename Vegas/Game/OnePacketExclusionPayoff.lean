/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.RevealServicePayoffs
import Interaction.ReactiveNormalHistory

/-! # The exclusion payoff on the supplied runtime

Under exclusion a publicly defaulted player receives a fixed exit
payoff, and every other player its utility of the parameter and public outcome
(`Vegas.SourceProgram.exclusionUtility`). The same payoff is read on terminal
source configurations (`Vegas.exclusionTerminalUtility`), on typed readouts, zero
without one (`Vegas.exclusionReadoutUtility`), and on native protocol states of
the supplied runtime (`Vegas.exclusionBase`). Public default fixes the native
payoff even when the service horizon ends without a terminal readout. The
readout version is the utility on the outcome type shared by the intended game
(`Vegas.SourceProgram.Setup.protocolReadout`) and the runtime
(`Vegas.sourceReadout`).

Bounds on an actual readout bound the native payoff
(`Vegas.exclusionBase_mem_Icc`). No intended history has
a public default, so the exclusion payoff of the intended readout is the
intended payoff, and every sequential equilibrium of the intended game is
sequentially rational against it
(`Vegas.SourceProgram.Setup.intended_exclusionSource`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Payoff

variable (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup)) {Parameter : Type}
  (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- The payoff of a terminal source configuration: public default fixes the
declared exit payoff; active players retain their ordinary valuation. -/
def exclusionTerminalUtility (terminal : Config Player L setup.program.terminalCtx)
    (who : Player) : ℝ :=
  exclusionUtility setup.program excludedPayoff utility (setup.parameterOutcome parameter terminal)
    who

/-- The payoff under exclusion of a typed readout, zero without one. -/
def exclusionReadoutUtility (readout : Option (Config Player L setup.program.terminalCtx))
    (who : Player) : ℝ :=
  readout.elim 0 fun terminal =>
    exclusionTerminalUtility setup parameter utility excludedPayoff terminal who

/-- An intended history's full source configuration and fixed-exit payoff. -/
def intendedReadoutExclusion (final : setup.intendedProtocol.History) :
    Option (Config Player L setup.program.terminalCtx) × (Player → ℝ) :=
  (setup.protocolReadout final.state,
    exclusionReadoutUtility setup parameter utility excludedPayoff
      (setup.protocolReadout final.state))

/-- A publicly defaulted player receives exactly its declared exit payoff. -/
theorem exclusionTerminalUtility_of_defaulted
    {terminal : Config Player L setup.program.terminalCtx}
    {who : Player}
    (defaulted : who ∈ terminal.defaulted) :
    exclusionTerminalUtility setup parameter utility excludedPayoff terminal who =
      excludedPayoff who :=
  exclusionUtility_of_defaulted setup.program excludedPayoff utility defaulted

/-- An active player retains the ordinary utility of the complete public result. -/
theorem exclusionTerminalUtility_of_not_defaulted
    {terminal : Config Player L setup.program.terminalCtx}
    {who : Player}
    (active : who ∉ terminal.defaulted) :
    exclusionTerminalUtility setup parameter utility excludedPayoff terminal who =
      utility (setup.parameterOutcome parameter terminal) who :=
  exclusionUtility_of_not_defaulted setup.program excludedPayoff utility active

/-- Bounds on the actual readout and exit payoff bound its utility; an absent
readout pays zero and requires no ordinary-utility bound. -/
theorem exclusionReadoutUtility_mem_Icc (lower upper : Player → ℝ)
    (readout : Option (Config Player L setup.program.terminalCtx))
    (lower_le : ∀ terminal, readout = some terminal →
      ∀ who, lower who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (le_upper : ∀ terminal, readout = some terminal →
      ∀ who, utility (setup.parameterOutcome parameter terminal) who ≤ upper who)
    (who : Player) :
    exclusionReadoutUtility setup parameter utility excludedPayoff readout who ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) := by
  cases readout with
  | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
  | some terminal =>
      change exclusionUtility setup.program excludedPayoff utility
        (setup.parameterOutcome parameter terminal) who ∈ _
      unfold exclusionUtility
      split
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
          (le_max_left _ _).trans (le_max_right _ _)⟩
      · exact ⟨(min_le_right _ _).trans ((min_le_right _ _).trans (lower_le _ rfl who)),
          (le_upper _ rfl who).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Public default fixes the native exit payoff immediately. Active players
receive their terminal readout utility, or zero while no readout is available. -/
def exclusionBase : (application setup runtime leaks).ProtocolState → Player → ℝ
  | none, _ => 0
  | some control, who =>
      if who ∈ control.execution.application.config.defaulted then excludedPayoff who
      else exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup runtime leaks (some control)) who

/-- Public default fixes exit utility without a source-completion premise. -/
theorem exclusionBase_of_defaulted
    (control : (application setup runtime leaks).Control)
    (who : Player) (defaulted : who ∈ control.execution.application.config.defaulted) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks (some control) who =
      excludedPayoff who := by
  simp only [exclusionBase, defaulted, ite_true]

/-- Active players use the utility of the actual terminal source readout. -/
theorem exclusionBase_of_not_defaulted
    (control : (application setup runtime leaks).Control)
    (who : Player) (active : who ∉ control.execution.application.config.defaulted) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks (some control) who =
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup runtime leaks (some control)) who := by
  simp only [exclusionBase, active, ite_false]

/-- A successful full readout makes native and source exit utility agree. -/
theorem exclusionBase_eq_readout_of_readout
    (state : (application setup runtime leaks).ProtocolState)
    (terminal : Config Player L setup.program.terminalCtx)
    (read : sourceReadout setup runtime leaks state = some terminal) (who : Player) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks state who =
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup runtime leaks state) who := by
  cases state with
  | none => cases read
  | some control =>
      by_cases defaulted : who ∈ control.execution.application.config.defaulted
      · rw [exclusionBase_of_defaulted setup runtime parameter utility excludedPayoff leaks
          control who defaulted, read]
        symm
        apply exclusionTerminalUtility_of_defaulted
        change who ∈ terminal.defaults.defaulted
        rw [serviceSourceReadout_defaults setup .sequential runtime.deadline leaks control
          terminal read]
        exact defaulted
      · exact exclusionBase_of_not_defaulted setup runtime parameter utility excludedPayoff
          leaks control who defaulted

/-- Submission normalization retains the configuration and its native exit utility. -/
theorem exclusionBase_normalization (state : (application setup runtime leaks).ProtocolState) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks
        ((runtime.reactiveNormalization leaks).state state) =
      exclusionBase setup runtime parameter utility excludedPayoff leaks state := by
  cases state <;> rfl

/-- Bounds on an actual native readout suffice to bound its fixed-exit base utility. -/
theorem exclusionBase_mem_Icc (lower upper : Player → ℝ)
    (state : (application setup runtime leaks).ProtocolState)
    (lower_le : ∀ terminal, sourceReadout setup runtime leaks state = some terminal →
      ∀ who, lower who ≤ utility (setup.parameterOutcome parameter terminal) who)
    (le_upper : ∀ terminal, sourceReadout setup runtime leaks state = some terminal →
      ∀ who, utility (setup.parameterOutcome parameter terminal) who ≤ upper who)
    (who : Player) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks state who ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) := by
  cases state with
  | none => exact ⟨min_le_left _ _, le_max_left _ _⟩
  | some control =>
      by_cases defaulted : who ∈ control.execution.application.config.defaulted
      · rw [exclusionBase_of_defaulted setup runtime parameter utility excludedPayoff leaks
          control who defaulted]
        exact ⟨(min_le_right _ _).trans (min_le_left _ _),
          (le_max_left _ _).trans (le_max_right _ _)⟩
      · rw [exclusionBase_of_not_defaulted setup runtime parameter utility excludedPayoff leaks
          control who defaulted]
        exact exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff lower upper
          _ lower_le le_upper who

end Payoff

end Vegas

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))

/-- On every intended history the exit utility agrees with the ordinary payoff,
because no player publicly defaults. -/
theorem intended_exclusionReadoutUtility (wellFormed : setup.WellFormed) {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (history : setup.intendedProtocol.History) (who : Player) :
    exclusionReadoutUtility setup parameter utility excludedPayoff
        (setup.protocolReadout history.state) who =
      (setup.protocolReadout history.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who) := by
  cases read : setup.protocolReadout history.state with
  | none => rfl
  | some terminal =>
      exact exclusionTerminalUtility_of_not_defaulted setup parameter utility excludedPayoff
        (setup.not_defaulted_of_intendedState
          (setup.intendedState_trace wellFormed history.trace) who read)

/-- **The intended equilibrium as the source of the exclusion comparison.**
Every sequential equilibrium of the intended game of a well-formed setup is the
pointwise limit of fully mixed Bayes-consistent assessments, and is sequentially
rational against the exclusion payoff of the intended readout for play cut off
at the intended game's horizon, whatever the exclusion payoffs. -/
theorem intended_exclusionSource [Fintype Player] (wellFormed : setup.WellFormed)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    ∃ sequence : ℕ → setup.intendedModel.BehavioralAssessment,
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent setup.intendedModel
        (sequence n) setup.intended_decision_antichain) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sequence intended ∧
      intended.IsSequentiallyRationalFor (fun who site =>
        intended.truncatedContinuationContext site
          (fun history => exclusionReadoutUtility setup parameter utility excludedPayoff
            (setup.protocolReadout history.state) who)
          (instructionCount setup.program + 1)) := by
  have truncated := (intended.isSequentialEquilibrium_iff_truncated_of_bounded setup.intendedModel
    setup.intended_decision_antichain setup.intended_bounded.wellFoundedHistories
    setup.intended_bounded _).mp equilibrium
  obtain ⟨sequence, regular, converges⟩ := truncated.2
  refine ⟨sequence, fun n => (regular n).1, fun n => (regular n).2, converges, ?_⟩
  intro who site
  have same : (fun history : setup.intendedProtocol.History =>
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (setup.protocolReadout history.state) who) =
      (fun final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who)) :=
    funext fun history =>
      setup.intended_exclusionReadoutUtility wellFormed parameter utility excludedPayoff history who
  beta_reduce
  rw [same]
  exact truncated.1 who site

end Vegas.SourceProgram.Setup
