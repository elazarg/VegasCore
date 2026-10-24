/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseProposalObservableDebt
import Vegas.Game.PhaseProposalReservedDebt
import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport

/-! # Zero native conditional gain at observable saved binding failures

Every history in the same full input fiber satisfies the observable selector.
Actual source readback supplies checkpoint debt separately at each history;
no hidden-world-dependent source deviation lottery is selected.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => PMF.map encodeInputs setup.initialLaw
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)

/-- Public request evidence and the full decision input recover actual debt
at EVERY hidden history of that input. No Bayes or reach premise is needed. -/
theorem phaseProposalSavedBindingFailure_information_history
    (horizon : Nat) (scheduler : (app).Scheduler) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event view)
    (history : ((menu).information initial horizon scheduler).InformationHistory who
      (some (past, view))) :
    ∃ control : (app).Control, history.val.state = some control ∧
      control.actor = some who ∧
        PhaseCheckpointDebt setup mode plan who control.execution.application := by
  have observed := ((menu).info initial horizon scheduler who history.val.trace).symm.trans
    history.property
  cases current : history.val.state with
  | none =>
      rw [current] at observed
      cases observed
  | some control =>
      rw [current] at observed
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe app who) else none) =
          some (past, view) at observed
      split at observed
      · rename_i active
        have viewed : control.execution.observe app who = view :=
          (Prod.mk.inj (Option.some.inj observed)).2
        have counted : ((menu).protocol initial horizon scheduler).Trace (some control) :=
          current ▸ history.val.trace
        have raw := (menu).toRawTrace initial horizon scheduler counted
        obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
          scheduler raw
        have actualRequest : PhaseRuntimeState.requests control.execution.application.publicView
            who ⟨control.execution.application.attempt, event⟩ := by
          change PhaseRuntimeState.requests
            (control.execution.observe app who).application.2 who
            ⟨(control.execution.observe app who).application.2.attempt, event⟩
          rw [viewed]
          exact requested
        have request := (control.execution.application.requests_publicView valid who
          ⟨control.execution.application.attempt, event⟩).mp actualRequest
        have original : ((menu).protocol
            (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
            horizon scheduler).Trace (some control) := by
          have sameInitial : initial = setup.initialLaw.map
              (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) :=
            PMF.map_comp _ _ _
          exact sameInitial ▸ counted
        refine ⟨control, rfl, active, ?_⟩
        exact phaseProposalSavedBindingFailure_checkpointDebt setup mode runtime leaks plan bounds
          maximal horizon scheduler original who event payload binding request
            (viewed.symm ▸ failed)
      · cases observed

variable {length : Nat} (prior : PMF (ReservedEpoch.Tape Player length))

local notation "horizon" => ReservedEpoch.executionHorizon runtime
local notation "scheduler" => ReactiveApplication.SchedulerImplementation.scheduler
  (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior)
local notation "model" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds)
    (PMF.map (PhaseRuntimeState.initial plan) (PMF.map encodeInputs setup.initialLaw))
      (ReservedEpoch.executionHorizon runtime)
      (ReactiveApplication.SchedulerImplementation.scheduler
        (ReservedEpoch.implementation runtime leaks (ReservedEpoch.packetCapacity runtime) prior))

/-- Arbitrary behavioral continuation from a saved-failure input has the
actual exclusion payoff at every terminal history in its support. -/
theorem phaseProposalSavedBindingFailure_information_terminal_payoff
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (players : ∀ owner, (model).BehavioralPolicy owner) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event view)
    (history : (model).InformationHistory who (some (past, view)))
    (final : ((menu).protocol initial horizon scheduler).History)
    (supported : final ∈ ((model).runBehavioralTerminalFrom certificate players
      history.val).support)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who =
      excludedPayoff who := by
  obtain ⟨control, current, _active, owed⟩ :=
    phaseProposalSavedBindingFailure_information_history setup mode runtime leaks bounds plan
      maximal horizon scheduler who past view event payload binding requested failed history
  exact reserved_checkpointDebt_behavioral_terminal_payoff setup mode runtime leaks prior plan
    maximal inputs menu certificate players history.val final control current who owed supported
      utility excludedPayoff

/-- Saved failure makes the actual history gain zero for every whole-policy
alternative, hence also for the current-law alternatives of local comparison. -/
theorem phaseProposalSavedBindingFailure_historyGain_eq_zero
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (assessment : (model).BehavioralAssessment) {who : Player}
    (deviation : (model).AssessmentDeviation who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (information : deviation.1.val = some (past, view))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event view)
    (history : (model).InformationHistory who deviation.1.val)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    (model).historyGain ((model).runBehavioralTerminalFrom certificate)
      (fun final => final.state)
      (phaseExclusionBase setup mode runtime leaks utility excludedPayoff)
      assessment deviation history = 0 := by
  apply (model).historyGain_eq_zero_of_constant_payoff _ _ _ assessment deviation history
    (excludedPayoff who)
  intro players final supported
  exact phaseProposalSavedBindingFailure_information_terminal_payoff setup mode runtime leaks bounds
    plan maximal prior certificate players who past view event payload binding requested failed
    ⟨history.val, history.property.trans information⟩ final supported utility excludedPayoff

/-- The observable case is uniform on the full information fiber, so any
assessment belief gives zero conditional gain. Its hidden-history distribution
and correlations remain unrestricted. -/
theorem phaseProposalSavedBindingFailure_gain_eq_zero
    [Finite ((menu).protocol initial horizon scheduler).History]
    (certificate : ((menu).protocol initial horizon scheduler).WellFoundedHistories)
    (assessment : (model).BehavioralAssessment) {who : Player}
    (deviation : (model).AssessmentDeviation who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (information : deviation.1.val = some (past, view))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (requested : PhaseRuntimeState.requests view.application.2 who
      ⟨view.application.2.attempt, event⟩)
    (failed : phaseProposalSavedBindingFailure setup mode runtime leaks who event view)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    expect ((model).assessmentComparisonWith
      ((model).runBehavioralTerminalFrom certificate)
      (fun final => final.state) assessment who deviation).alternative
        (fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff
          state who) -
      expect ((model).assessmentComparisonWith
      ((model).runBehavioralTerminalFrom certificate)
        (fun final => final.state) assessment who deviation).prescribed
        (fun state => phaseExclusionBase setup mode runtime leaks utility excludedPayoff state who)
      = 0 := by
  apply (model).gain_eq_zero_of_constant_continuations _ _ _ assessment deviation
    (fun _ => excludedPayoff who)
  intro history players final supported
  exact phaseProposalSavedBindingFailure_information_terminal_payoff setup mode runtime leaks bounds
    plan maximal prior certificate players who past view event payload binding requested failed
    ⟨history.val, history.property.trans information⟩ final supported utility excludedPayoff

end Vegas
