/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Game.SourceServiceCompletion
import Vegas.Pending.ReactiveGraphSteps
import Interaction.ReactiveRawRoundTrace
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Boundary continuations of the service

The source continuation of a configuration's typed prefix
(`Vegas.sourceContinuation`), the approximate continuation law from completion
boundaries (`Vegas.BoundaryContinuationWithin`), and the facts about
completion runs and terminal rounds they use: an activation leaves the
application unchanged (`Vegas.activation_application`), rounds from a terminal
configuration keep it (`Vegas.runRounds_config_terminal`), and a stopped point
of a completion run from a completion boundary at which the event has completed
is a boundary at its actual completed rank (`Vegas.CompletionBoundary.stopped`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

variable {setup} {leaks}

theorem deferral_nonneg {turns : Nat} (timing : TurnTiming setup turns mode)
    (event : (serviceGraph setup mode).EventId) : 0 ≤ timing.deferral event := by
  unfold TurnTiming.deferral
  split
  · exact le_rfl
  · rename_i who owned
    have atMost : (timing event who owned 0).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ 0)
    linarith

/-- Rounds from a terminal configuration keep the configuration. -/
theorem runRounds_config_terminal
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (players : Player → (serviceApplication setup mode deadline leaks).Policy) (count : Nat)
    (execution next : (serviceApplication setup mode deadline leaks).Execution)
    (terminal : execution.application.config.cut.IsPrefix
      (serviceGraph setup mode).order.eventCount)
    (reached : next ∈ ((serviceApplication setup mode deadline leaks).runRounds scheduler players
      count execution).support) :
    next.application.config = execution.application.config := by
  let app := serviceApplication setup mode deadline leaks
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | succ count ih =>
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
      obtain ⟨stepped, stepMember, resumed⟩ :=
        Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
      have stepConfig : stepped.application.config = execution.application.config :=
        EventGraph.Config.Step.path_eq_of_terminal
          (((serviceRuntime setup mode deadline).reactiveApplication_graphSteps
            leaks).environmentStep execution stepped command stepMember) terminal.terminal
      have middleConfig : middle.application.config = execution.application.config := by
        change middle ∈ (app.resume players (command.actor? app) stepped).support at resumed
        cases actor : command.actor? app with
        | none =>
            rw [actor] at resumed
            simp only [ReactiveApplication.resume, PMF.mem_support_pure_iff] at resumed
            subst resumed
            exact stepConfig
        | some who =>
            rw [actor] at resumed
            change middle ∈ (app.invoke players who stepped).support at resumed
            rw [ReactiveApplication.invoke, PMF.support_map] at resumed
            obtain ⟨response, _, rfl⟩ := resumed
            rw [((serviceRuntime setup mode deadline).reactive_respond_application leaks stepped who
              response).1, stepConfig]
      have terminalMiddle : middle.application.config.cut.IsPrefix
          (serviceGraph setup mode).order.eventCount := by
        rw [middleConfig]
        exact terminal
      rw [ih middle terminalMiddle rest, middleConfig]

end Generic
/-- The approximate version of `BoundaryContinuationLaw`: from every completion
boundary within the horizon, the players' run is within `error rank` of the
source continuation. -/
def BoundaryContinuationWithin (scheduler : (application setup runtime leaks).Scheduler)
  (horizon : Nat)
    (players : Player → (application setup runtime leaks).Policy)
    (profile : BehavioralProfile setup.program) (error : Nat → ℝ) : Prop :=
  ∀ rank (execution : (application setup runtime leaks).Execution),
    CompletionBoundary setup leaks scheduler players rank execution →
    execution.environmentRecall.length ≤ horizon →
    PMF.WithinTV (error rank)
      (((application setup runtime leaks).runToHorizon scheduler players horizon execution).map
        (fun final => sourceReadout setup runtime leaks ((application setup runtime
          leaks).finished final)))
      (sourceContinuation setup profile rank execution.application.config)

/-- With no error, the approximate law is the exact one. -/
theorem BoundaryContinuationWithin.law {scheduler : (application setup runtime leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup runtime leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (within : BoundaryContinuationWithin setup runtime leaks scheduler horizon players profile
      error)
    (zero : ∀ rank, error rank = 0) :
    BoundaryContinuationLaw setup leaks scheduler horizon players profile := by
  intro rank execution boundary bounded
  have close := within rank execution boundary bounded
  rw [zero rank] at close
  exact close.eq_of_zero
variable {setup leaks}
/-- A stopped point of a completion run from a completion boundary at which
the event has completed is a later actual boundary, within the horizon. -/
theorem CompletionBoundary.stopped {scheduler : (application setup runtime leaks).Scheduler}
    {players : Player → (application setup runtime leaks).Policy} {horizon : Nat}
    (event : (graph setup).EventId) (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup runtime leaks).Execution)
    (reached : stopped ∈ ((application setup runtime leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support)
    (finished : event ∈ stopped.application.config.cut.completed) :
    stopped.environmentRecall.length ≤ horizon ∧
      ∃ actualRank, event.val < actualRank ∧
        CompletionBoundary setup leaks scheduler players actualRank stopped := by
  let app := application setup runtime leaks
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup runtime leaks scheduler players _ execution
    boundary.supported
  have rankEq := EventOrder.Cut.IsPrefix.unique ranked boundary.ordered
  subst rankEq
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players _ _ execution
    stopped reached
  obtain ⟨stoppedSeen, stoppedConfig⟩ := runUntil_completion_prefix setup runtime leaks scheduler
    players event _ execution stopped boundary.ordered seen reached
  rcases stoppedConfig with current | ⟨actualRank, later, ordered⟩
  · exact (Nat.lt_irrefl _ ((current.2 event).mp finished)).elim
  · refine ⟨by omega, actualRank, later,
      app.roundsFrom_runUntil scheduler players (initialLaw setup) _ _ execution
        stopped boundary.supported reached, ordered, ?_⟩
    intro next rankNext observer entry member readyView
    have := stoppedSeen observer entry member next readyView
    omega

variable (setup leaks)

/-- Local completion laws determine every terminal native readout.
Automatic completion may cross several source instructions before the next boundary. -/
theorem CompletionBoundary.runToHorizon_law {Outcome : Type*}
    (profile : (graph setup).BehavioralProfile) (read : (graph setup).Config → Outcome)
    {scheduler : (application setup runtime leaks).Scheduler}
    {players : Player → (application setup runtime leaks).Policy} {horizon : Nat}
    (completes : runtime.CompletesPlay leaks (initialLaw setup) horizon scheduler)
    (completionLaw : ∀ (event : (graph setup).EventId)
      (execution : (application setup runtime leaks).Execution),
      CompletionBoundary setup leaks scheduler players event.val execution →
      execution.environmentRecall.length ≤ horizon →
      ((application setup runtime leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
          (fun final => ((graph setup).runPlan
            ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
            final.application.config.remaining final.application.config).map read) =
        ((graph setup).runPlan
          ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          execution.application.config.remaining execution.application.config).map read)
    {rank : Nat} (execution : (application setup runtime leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ((application setup runtime leaks).runToHorizon scheduler players horizon execution).map
        (fun final => read final.application.config) =
      ((graph setup).runPlan
        ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
        execution.application.config.remaining execution.application.config).map read := by
  classical
  let app := application setup runtime leaks
  let plan := (graph setup).policyPlan profile (graph setup).canonicalScheduler
  generalize remainingEq : execution.application.config.remaining = remaining
  induction remaining using Nat.strong_induction_on generalizing rank execution with
  | h remaining ih =>
      rw [← remainingEq]
      by_cases finished : rank = (graph setup).order.eventCount
      · have terminal : execution.application.config.cut.IsPrefix
            (graph setup).order.eventCount := finished ▸ boundary.ordered
        have zero : execution.application.config.remaining = 0 :=
          execution.application.config.terminal_iff_remaining_zero.mp terminal.terminal
        rw [zero, EventGraph.runPlan, PMF.pure_map]
        change (app.runRounds scheduler players _ execution).map _ = _
        rw [map_congr_on_support _
          (g := fun _ => read execution.application.config)
          (fun next reached => congrArg read (runRounds_config_terminal
            (setup := setup) (leaks := leaks) scheduler players _ execution next terminal reached)),
          pmf_map_fun_const]
      · have active : rank < (graph setup).order.eventCount := by
          have rankBound : rank ≤ (graph setup).order.eventCount := boundary.ordered.1
          omega
        let event : (graph setup).EventId := ⟨rank, active⟩
        rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players
          (fun final => event ∈ final.application.config.cut.completed), PMF.map_bind]
        calc
          _ = (app.runUntilHorizon scheduler players
              (fun final => event ∈ final.application.config.cut.completed) horizon
              execution).bind (fun final =>
                ((graph setup).runPlan plan final.application.config.remaining
                  final.application.config).map read) := by
            apply bind_congr_on_support _
            intro stopped reached
            have stoppedDone : event ∈ stopped.application.config.cut.completed := by
              rcases app.runUntilHorizon_stopped scheduler players
                  (fun final => event ∈ final.application.config.cut.completed) horizon
                  (horizon - execution.environmentRecall.length) execution stopped
                  (by omega) reached with completed | spent
              · exact completed
              · have supported := app.roundsFrom_runUntil scheduler players (initialLaw setup)
                  (fun final => event ∈ final.application.config.cut.completed) _ execution
                  stopped boundary.supported reached
                have supportedAtHorizon : stopped ∈
                    (app.roundsFrom (initialLaw setup) scheduler players horizon).support := by
                  simpa only [spent] using supported
                obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
                  players horizon le_rfl stopped supportedAtHorizon
                have terminal := completes ⟨horizon - horizon, none, stopped⟩ trace
                  ⟨Nat.sub_self _, rfl⟩
                rw [EventOrder.Cut.Terminal] at terminal
                rw [terminal]
                exact Finset.mem_univ _
            obtain ⟨stoppedBounded, actualRank, later, nextBoundary⟩ :=
              boundary.stopped runtime event execution bounded stopped reached stoppedDone
            have decrease : stopped.application.config.remaining < remaining := by
              have oldCard : execution.application.config.cut.completed.card = rank :=
                boundary.ordered.card
              have nextCard : stopped.application.config.cut.completed.card = actualRank :=
                nextBoundary.ordered.card
              have nextBound : actualRank ≤ (graph setup).order.eventCount :=
                nextBoundary.ordered.1
              have laterRank : rank < actualRank := later
              unfold EventGraph.Config.remaining at remainingEq ⊢
              omega
            exact ih stopped.application.config.remaining decrease stopped nextBoundary
              stoppedBounded rfl
          _ = _ := completionLaw event execution boundary bounded


end Vegas
