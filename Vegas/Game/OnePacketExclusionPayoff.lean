/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedPreservation
import Vegas.Game.RevealServicePayoffs
import Vegas.Game.SourceTerminalReadout
import Vegas.Game.SourceStateKernel
import Interaction.ReactiveNormalHistory
import GameTheory.Math.Probability.ExpectationComposition
import GameTheoryExtensions.Math.FiniteIntervalBounds

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

/-- The source continuation value of a profile at a point: the expected
exclusion payoff of `who` under the typed readout of its continuation. -/
def sourcePointValue (profile : BehavioralProfile setup.program) (who : Player)
    (point : ProtocolState setup.program) : ℝ :=
  expect ((ProtocolState.continuationLaw setup.program profile point).map some)
    (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout who)

variable [Fintype Player] in
/-- **The source step keeps the continuation value.** The expected source
continuation value of a profile after one step of its own behavioral step law
is the continuation value before it. -/
theorem expect_sourcePointValue_behavioralStateStep (profile : BehavioralProfile setup.program)
    (who : Player) {bound : ℝ}
    (readoutBounded : ∀ readout, |exclusionReadoutUtility setup parameter utility excludedPayoff
      readout who| ≤ bound)
    (point : ProtocolState setup.program) :
    expect (ProtocolState.behavioralStateStep setup.program profile point)
        (sourcePointValue setup parameter utility excludedPayoff profile who) =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
  unfold sourcePointValue
  simp only [expect_map]
  rw [← expect_bind_tower_bounded _ _ ((fun readout => exclusionReadoutUtility setup
    parameter utility excludedPayoff readout who) ∘ some) (fun terminal => readoutBounded
      (some terminal)), ProtocolState.behavioralStateStep_continuation]

/-- The utility of an observation of readout and payoffs: its payoff component. -/
abbrev payoffComponent
    (outcome : Option (Config Player L setup.program.terminalCtx) × (Player → ℝ))
    (who : Player) : ℝ :=
  outcome.2 who


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

/-- A completed native graph freezes its base exit utility under arbitrary continuations. -/
theorem sourceTerminal_exclusionBase_stable [Fintype Player]
    (menu : (application setup runtime leaks).ResponseMenu)
    (initial : PMF (application setup runtime leaks).State) (horizon : Nat)
    (scheduler : (application setup runtime leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (start : (menu.protocol initial horizon scheduler).History)
    (terminal : NativeSourceTerminal (runtime := runtime) (setup := setup) (leaks := leaks)
      start.state) :
    ∀ final ∈ ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
        players start).support,
      exclusionBase setup runtime parameter utility excludedPayoff leaks final.state =
        exclusionBase setup runtime parameter utility excludedPayoff leaks start.state := by
  cases current : start.state with
  | none => simp only [NativeSourceTerminal, current] at terminal
  | some control =>
      simp only [NativeSourceTerminal, current] at terminal
      have fixed := sourceTerminal_config_stable menu initial horizon scheduler certificate
        players start control current terminal
      intro final supported
      obtain ⟨found, state, same⟩ := fixed final supported
      have readout : sourceReadout setup runtime leaks (some found) =
          sourceReadout setup runtime leaks (some control) := by
        rw [sourceReadout, serviceSourceReadout_eq_decode, serviceSourceReadout_eq_decode, same]
      rw [state]
      funext who
      simp only [exclusionBase, same, readout]

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

variable [Fintype Player] in
/-- **The exclusion payoffs are bounded** by the sum over players of the spread
between the exclusion payoff, zero and the utility bounds. -/
theorem exclusionPayoffs_bounded (lowerUtility upperUtility : Player → ℝ)
    (lower_le : ∀ outcome who, lowerUtility who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upperUtility who) :
    let budget := ∑ player, (max 0 (max (excludedPayoff player) (upperUtility player)) -
      min 0 (min (excludedPayoff player) (lowerUtility player)))
    0 ≤ budget ∧
      (∀ who readout, |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤
        budget) ∧ ∀ who, |excludedPayoff who| ≤ budget := by
  intro budget
  let lower := fun who => min 0 (min (excludedPayoff who) (lowerUtility who))
  let upper := fun who => max 0 (max (excludedPayoff who) (upperUtility who))
  have lowerNonpos : ∀ who, lower who ≤ 0 := fun _ => min_le_left _ _
  have upperNonneg : ∀ who, 0 ≤ upper who := fun _ => le_max_left _ _
  refine ⟨Finset.sum_nonneg (fun who _ => sub_nonneg.mpr
    ((lowerNonpos who).trans (upperNonneg who))), ?_, ?_⟩
  · intro who readout
    exact GameTheory.Math.abs_le_sum_interval_width lower upper lowerNonpos upperNonneg who
      (exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff lowerUtility
        upperUtility readout (fun _ _ who => lower_le _ who)
        (fun _ _ who => le_upper _ who) who)
  · intro who
    apply GameTheory.Math.abs_le_sum_interval_width lower upper lowerNonpos upperNonneg who
    exact ⟨(min_le_right _ _).trans (min_le_left _ _),
      (le_max_left _ _).trans (le_max_right _ _)⟩

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
