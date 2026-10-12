/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDecodedDebt
import Vegas.Game.IntendedAuditedOutcome

/-! # The exclusion payoff on the default runtime

Under exclusion a player with a failed reveal receives a fixed exclusion
payoff, and every other player its utility of the parameter and public outcome
(`Vegas.SourceProgram.exclusionUtility`). The same payoff is read on terminal
source stores (`Vegas.exclusionTerminalUtility`), on typed readouts, zero
without one (`Vegas.exclusionReadoutUtility`), and on native protocol states of
the default runtime through their typed readout (`Vegas.exclusionBase`). The
readout version is the utility on the outcome type shared by the intended game
(`Vegas.SourceProgram.Setup.protocolReadout`) and the runtime
(`Vegas.sourceReadout`).

A source debt or failed binding read through the native decoding is paid: every
terminal continuation, under any players and a scheduler that completes play,
records a failed reveal of its owner
(`Vegas.decoded_owesFailure_failedReveals`), so the owner receives exactly its
exclusion payoff there (`Vegas.decoded_owesFailure_exclusionBase`), and in
expectation from that history (`Vegas.decoded_owesFailure_expect_exclusionBase`).

Bounds on the utility bound the native payoff over all protocol states, hence
under every scheduler (`Vegas.exclusionBase_mem_Icc`), and the payoff ignores
private response normalization (`Vegas.exclusionBase_normalization`). No
intended history has a failed reveal, so the exclusion payoff of the intended
readout is the intended payoff, and every sequential equilibrium of the intended
game is sequentially rational against it
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

variable (setup : Setup (Player := Player) (L := L)) {Parameter : Type}
  (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

/-- The payoff under exclusion of a terminal source store: a player with a
failed reveal receives its exclusion payoff, every other player its utility of
the store's parameter and public outcome. -/
def exclusionTerminalUtility (terminal : State L setup.program.terminalCtx) (who : Player) : ℝ :=
  exclusionUtility setup.program excludedPayoff utility (setup.parameterOutcome parameter terminal)
    who

/-- The payoff under exclusion of a typed readout, zero without one. -/
def exclusionReadoutUtility (readout : Option (State L setup.program.terminalCtx))
    (who : Player) : ℝ :=
  readout.elim 0 fun terminal =>
    exclusionTerminalUtility setup parameter utility excludedPayoff terminal who

/-- A player with a failed reveal receives exactly its exclusion payoff. -/
theorem exclusionTerminalUtility_of_failed {terminal : State L setup.program.terminalCtx}
    {who : Player}
    (failed : 1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal)) :
    exclusionTerminalUtility setup parameter utility excludedPayoff terminal who =
      excludedPayoff who :=
  exclusionUtility_of_failedReveals_pos setup.program excludedPayoff utility failed

/-- A player without a failed reveal receives its utility. -/
theorem exclusionTerminalUtility_of_not_failed {terminal : State L setup.program.terminalCtx}
    {who : Player}
    (noFailure : failedReveals setup.program who (publicOutcome setup.program terminal) = 0) :
    exclusionTerminalUtility setup parameter utility excludedPayoff terminal who =
      utility (setup.parameterOutcome parameter terminal) who :=
  exclusionUtility_of_failedReveals_eq_zero setup.program excludedPayoff utility noFailure

/-- Bounds on the utility and the exclusion payoff bound the payoff of every
readout, the missing readout paying zero. -/
theorem exclusionReadoutUtility_mem_Icc (lower upper : Player → ℝ)
    (lower_le : ∀ outcome who, lower who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (readout : Option (State L setup.program.terminalCtx)) (who : Player) :
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
      · exact ⟨(min_le_right _ _).trans ((min_le_right _ _).trans (lower_le _ who)),
          (le_upper _ who).trans ((le_max_right _ _).trans (le_max_right _ _))⟩
      · exact ⟨(min_le_right _ _).trans (min_le_left _ _),
          (le_max_left _ _).trans (le_max_right _ _)⟩

variable (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The exclusion payoff of a native protocol state of the default runtime: the
exclusion payoff of its typed terminal readout, zero without one. -/
abbrev exclusionBase : (application setup leaks).ProtocolState → Player → ℝ :=
  baseUtility setup leaks (exclusionTerminalUtility setup parameter utility excludedPayoff)

/-- The native exclusion payoff is the readout payoff of the typed readout. -/
theorem exclusionBase_eq_readout (state : (application setup leaks).ProtocolState)
    (who : Player) :
    exclusionBase setup parameter utility excludedPayoff leaks state who =
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup leaks state) who := rfl

/-- The native exclusion payoff ignores private response normalization. -/
theorem exclusionBase_normalization (state : (application setup leaks).ProtocolState) :
    exclusionBase setup parameter utility excludedPayoff leaks
        (((runtime setup).reactiveNormalization leaks).state state) =
      exclusionBase setup parameter utility excludedPayoff leaks state :=
  baseUtility_normalization setup leaks _ state

/-- **Scheduler-independent bounds.** Bounds on the utility and the exclusion
payoff bound the native exclusion payoff at every protocol state. -/
theorem exclusionBase_mem_Icc (lower upper : Player → ℝ)
    (lower_le : ∀ outcome who, lower who ≤ utility outcome who)
    (le_upper : ∀ outcome who, utility outcome who ≤ upper who)
    (state : (application setup leaks).ProtocolState) (who : Player) :
    exclusionBase setup parameter utility excludedPayoff leaks state who ∈
      Set.Icc (min 0 (min (excludedPayoff who) (lower who)))
        (max 0 (max (excludedPayoff who) (upper who))) :=
  exclusionReadoutUtility_mem_Icc setup parameter utility excludedPayoff lower upper lower_le
    le_upper _ who

end Payoff

/-- A player owing a failure is closed under every source step. -/
theorem owesFailure_stepClosed {setup : Setup (Player := Player) (L := L)} (who : Player) :
    StepClosed setup (ProtocolState.OwesFailure who setup.program) :=
  fun state joint target owed reached =>
    ProtocolState.owesFailure_step who setup.program state joint target owed reached

variable {setup : Setup (Player := Player) (L := L)} {profile : BehavioralProfile setup.program}

/-- **Decoded failures are paid.** Suppose a native history of a response menu,
under a scheduler that completes play, has a configuration that decodes at its
prefix to a source point at which `who` owes a failed reveal: one of its reveals
failed, it is indebted to a guard, or it holds a failed binding. Then every
terminal history of terminal play from it, under any players, has a source
readout recording at least one failed reveal of `who`. -/
theorem decoded_owesFailure_failedReveals [Fintype Player]
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.state) :
    ∀ final ∈ ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate players history).support,
      ∃ terminal, sourceReadout setup leaks final.state = some terminal ∧
        1 ≤ failedReveals setup.program who (publicOutcome setup.program terminal) := by
  intro final supported
  have reachedOwed := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_closed certificate players
    (DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program))
    (fun state joint _ target holds reached =>
      decodedHolds_transition (owesFailure_stepClosed who) (initialLaw setup) horizon scheduler
        state target joint holds reached)
    history owed final supported
  have stopped := (menu.information (initialLaw setup) horizon
    scheduler).runBehavioralTerminalFrom_support_terminal certificate players history final
    supported
  cases state : final.state with
  | none =>
      rw [state] at reachedOwed
      exact reachedOwed.elim
  | some control =>
      rw [state] at reachedOwed stopped
      obtain ⟨rank, ⟨residual⟩, decoded⟩ := reachedOwed
      have trace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some control) :=
        state ▸ menu.toRawTrace (initialLaw setup) horizon scheduler final.trace
      have terminalCut := completes control trace stopped
      have full := isPrefix_eventCount_of_terminal residual.checkpoint.ordered terminalCut
      subst full
      have read := sourceServicePrefix?_terminal_readout setup control.execution.application.config
      obtain ⟨point, decodedEq⟩ :
          ∃ point, sourceServicePrefix? setup (eventCount setup.program)
            control.execution.application.config = some point :=
        ⟨_, residual.decode⟩
      have pointOwed := decoded point decodedEq
      rw [decodedEq] at read
      obtain ⟨terminal, terminalRead⟩ :=
        ProtocolState.exists_readout_of_terminal setup.program point
          (decodeSourcePrefix?_terminal setup.program _ _ _ _ _ _ point decodedEq)
      refine ⟨terminal, ?_, ProtocolState.failedReveals_pos_of_owesFailure who setup.program point
        pointOwed terminalRead⟩
      rw [sourceReadout_eq_decode, ← read]
      exact terminalRead

/-- **A decoded failure fixes the payoff.** Under the hypotheses of
`decoded_owesFailure_failedReveals`, the native exclusion payoff of `who` is its
exclusion payoff on every terminal continuation, whatever anyone plays. -/
theorem decoded_owesFailure_exclusionBase [Fintype Player]
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.state) :
    ∀ final ∈ ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate players history).support,
      exclusionBase setup parameter utility excludedPayoff leaks final.state who =
        excludedPayoff who := by
  intro final supported
  obtain ⟨terminal, read, failed⟩ := decoded_owesFailure_failedReveals menu horizon scheduler
    completes certificate players who history owed final supported
  rw [exclusionBase_eq_readout, read]
  exact exclusionTerminalUtility_of_failed setup parameter utility excludedPayoff failed

/-- Under the hypotheses of `decoded_owesFailure_exclusionBase`, the expected
native exclusion payoff of `who` from the history is its exclusion payoff. -/
theorem decoded_owesFailure_expect_exclusionBase [Fintype Player]
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : (menu.protocol (initialLaw setup) horizon scheduler).WellFoundedHistories)
    (players : ∀ who, (menu.information (initialLaw setup) horizon scheduler).BehavioralPolicy who)
    (who : Player) (history : (menu.protocol (initialLaw setup) horizon scheduler).History)
    (owed : DecodedState setup leaks profile (ProtocolState.OwesFailure who setup.program)
      history.state) :
    expect ((menu.information (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom
        certificate players history)
      (fun final => exclusionBase setup parameter utility excludedPayoff leaks final.state who) =
      excludedPayoff who := by
  rw [expect_congr_on_support (g := fun _ => excludedPayoff who)
    (decoded_owesFailure_exclusionBase parameter utility excludedPayoff menu horizon scheduler
      completes certificate players who history owed)]
  exact expect_constant _ _

end Vegas

namespace Vegas.SourceProgram.Setup

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- On every history of the intended game the exclusion payoff of its readout
is the intended payoff: no reveal of the intended game fails. -/
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
      exact exclusionTerminalUtility_of_not_failed setup parameter utility excludedPayoff
        (setup.failedReveals_eq_zero_of_intendedState
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
    (equilibrium : intended.IsSequentialEquilibrium setup.intended_decision_antichain
      setup.intended_bounded.wellFoundedHistories
      (fun who final => (setup.protocolReadout final.state).elim 0
        (fun state => utility (setup.parameterOutcome parameter state) who))) :
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
