/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.RevealServicePayoffs

/-! # The exclusion payoff on the supplied runtime

Under exclusion a publicly defaulted player receives a fixed exit
payoff, and every other player its utility of the parameter and public outcome
(`Vegas.SourceProgram.exclusionUtility`). The same payoff is read on terminal
source configurations (`Vegas.exclusionTerminalUtility`), on typed readouts, zero
without one (`Vegas.exclusionReadoutUtility`), and on native protocol states of
the supplied runtime through their typed readout (`Vegas.exclusionBase`). The
readout version is the utility on the outcome type shared by the intended game
(`Vegas.SourceProgram.Setup.protocolReadout`) and the runtime
(`Vegas.sourceReadout`).

Bounds on the utility bound the native payoff over all protocol states, hence
under every scheduler (`Vegas.exclusionBase_mem_Icc`). No intended history has
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

/-- Bounds on the utility and the exclusion payoff bound the payoff of every
readout, the missing readout paying zero. -/
theorem exclusionReadoutUtility_mem_Icc (lower upper : Player → ℝ)
    (lower_le : ∀ outcome who, lower who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readout : Option (Config Player L setup.program.terminalCtx)) (who : Player) :
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
      · exact ⟨(min_le_right _ _).trans ((min_le_right _ _).trans (lower_le _ who)),
          (le_upper _ who).trans ((le_max_right _ _).trans (le_max_right _ _))⟩

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The exclusion payoff of a native protocol state of the supplied runtime: the
exclusion payoff of its typed terminal readout, zero without one. -/
abbrev exclusionBase : (application setup runtime leaks).ProtocolState → Player → ℝ :=
  baseUtility setup runtime leaks (exclusionTerminalUtility setup parameter utility excludedPayoff)

/-- The native exclusion payoff is the readout payoff of the typed readout. -/
theorem exclusionBase_eq_readout (state : (application setup runtime leaks).ProtocolState)
    (who : Player) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks state who =
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup runtime leaks state) who := rfl

/-- A complete native readout retains the fixed exit utility of every publicly
defaulted player, including a binding omission without any failed reveal. -/
theorem exclusionBase_of_defaulted
    (control : (application setup runtime leaks).Control)
    (terminal : Config Player L setup.program.terminalCtx)
    (read : sourceReadout setup runtime leaks (some control) = some terminal)
    (who : Player) (defaulted : who ∈ control.execution.application.config.defaulted) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks (some control) who =
      excludedPayoff who := by
  change (sourceReadout setup runtime leaks (some control)).elim 0 _ = _
  rw [read]
  apply exclusionTerminalUtility_of_defaulted
  change who ∈ terminal.defaults.defaulted
  rw [serviceSourceReadout_defaults setup .sequential runtime.deadline leaks control terminal read]
  exact defaulted

/-- **Scheduler-independent bounds.** Bounds on the utility and the exclusion
payoff bound the native exclusion payoff at every protocol state. -/
theorem exclusionBase_mem_Icc (lower upper : Player → ℝ)
    (lower_le : ∀ outcome who, lower who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (state : (application setup runtime leaks).ProtocolState) (who : Player) :
    exclusionBase setup runtime parameter utility excludedPayoff leaks state who ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) :=
  exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff lower upper lower_le
    le_upper _ who

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
