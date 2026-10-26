/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceTerminalReadout
import Vegas.Game.OnePacketExclusionPayoff
import GameTheoryExtensions.Analysis.Protocol.SourceGainTransport
import GameTheoryExtensions.Analysis.Protocol.StoppedResidual

/-! # Actual whole-policy indifference after the source readout freezes

A completed public source view identifies a completed cut throughout the real
information fiber. Every continuation profile then has the same original
readout payoff at each hidden history. This cancels its signed residual and
its whole-policy conditional gain; audit charges are not part of this payoff.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  (menu : (application setup leaks).ResponseMenu)
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

local notation "E" => menu.protocol initial horizon scheduler
local notation "M" => menu.information initial horizon scheduler

omit [Fintype Player] in
/-- Source completion is genuinely public throughout the actual native
information fiber, including callbacks after the last event has completed. -/
theorem sourceTerminal_of_info {who : Player}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (history : (E).History)
    (seen : (M).infoOf who history.trace = some (past, view))
    (complete : ∀ event : (graph setup).EventId,
      event ∈ view.application.publicView.observation.completionOrder) :
    NativeSourceTerminal (setup := setup) (leaks := leaks) history.state := by
  have observed := (menu.info initial horizon scheduler who history.trace).symm.trans seen
  cases current : history.state with
  | none => rw [current] at observed; cases observed
  | some control =>
      rw [current] at observed
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        have viewEq := (Prod.mk.inj (Option.some.inj observed)).2
        change control.execution.application.config.cut.completed = Finset.univ
        apply Finset.eq_univ_of_forall
        intro event
        apply (control.execution.application.config.history_exact event).mp
        have recorded := complete event
        rw [← viewEq] at recorded
        exact recorded
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

/-- The exact terminal expectation is fixed for every actual native profile.
The payoff is explicitly a function of the typed source readout. -/
theorem sourceTerminal_expect_payoff
    (certificate : (E).WellFoundedHistories)
    (players : ∀ who, (M).BehavioralPolicy who) (start : (E).History)
    (terminal : NativeSourceTerminal (setup := setup) (leaks := leaks) start.state)
    (payoff : Option (State L setup.program.terminalCtx) → ℝ) :
    expect ((M).runBehavioralTerminalFrom certificate players start)
        (fun final => payoff (sourceReadout setup leaks final.state)) =
      payoff (sourceReadout setup leaks start.state) := by
  calc
    _ = expect ((M).runBehavioralTerminalFrom certificate players start)
        (fun _ => payoff (sourceReadout setup leaks start.state)) := by
      apply expect_congr_on_support
      intro final reached
      rw [sourceTerminal_readout_stable menu initial horizon scheduler certificate players start
        terminal final reached]
    _ = _ := expect_constant _ _

/-- Native source completion kills the actual signed continuation residual
for every pair of profiles, rather than postulating a simulation or charge law. -/
theorem sourceTerminal_residual_eq_zero
    (certificate : (E).WellFoundedHistories)
    (source target : ∀ who, (M).BehavioralPolicy who) (history : (E).History)
    (terminal : NativeSourceTerminal (setup := setup) (leaks := leaks) history.state)
    (payoff : Option (State L setup.program.terminalCtx) → ℝ) :
    (M).stoppedContinuationResidual certificate source target (fun _ => False)
      (fun final => payoff (sourceReadout setup leaks final.state)) history = 0 := by
  classical
  by_cases ended : (E).terminal history.state
  · simp only [InformationModel.stoppedContinuationResidual, ended, or_true, ↓reduceIte]
  let value := fun current : (E).History => expect
    ((M).runBehavioralUntil certificate target (fun _ => False) current)
      (fun final => payoff (sourceReadout setup leaks final.state))
  have currentValue (current : (E).History)
      (complete : NativeSourceTerminal (setup := setup) (leaks := leaks) current.state) :
      value current = payoff (sourceReadout setup leaks current.state) := by
    dsimp only [value]
    rw [← (M).runBehavioralTerminalFrom_eq_until_false]
    exact sourceTerminal_expect_payoff menu initial horizon scheduler certificate target current
      complete payoff
  have afterValue : ∀ next ∈ ((M).runBehavioralFrom source 1 history).support,
      value next = payoff (sourceReadout setup leaks history.state) := by
    intro next reached
    obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
      (M).mem_support_runBehavioralFrom_one source ended reached
    cases before : history.state with
    | none => simp only [NativeSourceTerminal, before] at terminal
    | some control =>
        have complete : control.execution.application.config.cut.Terminal := by
          simpa only [NativeSourceTerminal, before] using terminal
        have stepped : next.state ∈ ((application setup leaks).transition initial horizon scheduler
            (some control) joint).support := before ▸ realized
        obtain ⟨after, afterState, same⟩ := sourceTerminal_transition control complete joint stepped
        have nextComplete : NativeSourceTerminal (setup := setup) (leaks := leaks) next.state := by
          rw [afterState]
          change after.execution.application.config.cut.Terminal
          rw [same]
          exact complete
        rw [currentValue next nextComplete, afterState, sourceReadout_eq_decode,
          sourceReadout_eq_decode, same]
  unfold InformationModel.stoppedContinuationResidual
  rw [ite_eq_right (by simpa only [false_or] using ended)]
  change expect _ value - value history = 0
  rw [currentValue history terminal]
  exact sub_eq_zero.mpr ((expect_congr_on_support afterValue).trans (expect_constant _ _))

/-- Every actual whole-policy deviation is indifferent after a completed source
view. All hidden histories and all assessment beliefs are retained. -/
theorem sourceTerminal_gain_eq_zero [Finite (E).History]
    (certificate : (E).WellFoundedHistories)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ)
    (assessment : (M).BehavioralAssessment) {who : Player}
    (deviation : (M).AssessmentDeviation who)
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView}
    (atSite : deviation.1.1 = some (past, view))
    (complete : ∀ event : (graph setup).EventId,
      event ∈ view.application.publicView.observation.completionOrder) :
    expect ((M).assessmentComparisonWith ((M).runBehavioralTerminalFrom certificate)
        (fun final => sourceReadout setup leaks final.state) assessment who deviation).alternative
        (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
          who) -
      expect ((M).assessmentComparisonWith ((M).runBehavioralTerminalFrom certificate)
        (fun final => sourceReadout setup leaks final.state) assessment who deviation).prescribed
        (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout
          who) = 0 := by
  apply (M).gain_eq_zero_of_constant_continuations _ _ _ assessment deviation
    (fun history => exclusionReadoutUtility setup parameter utility excludedPayoff
      (sourceReadout setup leaks history.1.state) who)
  intro history players final reached
  have terminal := sourceTerminal_of_info menu initial horizon scheduler history.1
    (history.2.trans atSite) complete
  rw [sourceTerminal_readout_stable menu initial horizon scheduler certificate players history.1
    terminal final reached]

end Vegas
