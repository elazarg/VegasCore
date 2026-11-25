module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceTurnPolicy
public import Vegas.Game.SourceServiceCompletion
public import Vegas.Pending.GraphCompletionLaw
public import GameTheoryExtensions.Math.Probability.TotalVariation

@[expose] public section

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
  (timeouts : EventTimeouts setup.informationGraph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))

section Generic

variable (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

variable {setup} {leaks}

theorem deferral_nonneg {turns : Nat} (timing : TurnTiming setup turns deps)
    (event : (serviceGraph setup deps).EventId) : 0 ≤ timing.deferral event := by
  unfold TurnTiming.deferral
  split
  · exact le_rfl
  · rename_i who owned
    have atMost : (timing event who owned 0).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ 0)
    linarith

/-- Rounds from a terminal configuration keep the configuration. -/
theorem runRounds_config_terminal
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (players : Player → (serviceApplication setup deps duration leaks).Policy) (count : Nat)
    (execution next : (serviceApplication setup deps duration leaks).Execution)
    (terminal : execution.application.config.cut.IsPrefix
      (serviceGraph setup deps).order.eventCount)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).runRounds scheduler players
      count execution).support) :
    next.application.config = execution.application.config :=
  EventGraph.Config.Step.path_eq_of_terminal (reactive_runRounds_graph_steps
    (serviceTimeouts setup deps duration) leaks scheduler players count execution next reached)
    terminal.terminal

end Generic
/-- The approximate version of `BoundaryContinuationLaw`: from every completion
boundary within the horizon, the players' run is within `error rank` of the
source continuation. -/
def BoundaryContinuationWithin (scheduler : (application setup timeouts leaks).Scheduler)
  (horizon : Nat)
    (players : Player → (application setup timeouts leaks).Policy)
    (profile : BehavioralProfile setup.program) (error : Nat → ℝ) : Prop :=
  ∀ rank (execution : (application setup timeouts leaks).Execution),
    CompletionBoundary setup leaks scheduler players rank execution →
    execution.environmentRecall.length ≤ horizon →
    PMF.WithinTV (error rank)
      (((application setup timeouts leaks).runToHorizon scheduler players horizon execution).map
        (fun final => sourceReadout setup timeouts leaks ((application setup timeouts
          leaks).finished final)))
      (sourceContinuation setup profile rank execution.application.config)

/-- With no error, the approximate law is the exact one. -/
theorem BoundaryContinuationWithin.law {scheduler : (application setup timeouts leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup timeouts leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (within : BoundaryContinuationWithin setup timeouts leaks scheduler horizon players profile
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
theorem CompletionBoundary.stopped {scheduler : (application setup timeouts leaks).Scheduler}
    {players : Player → (application setup timeouts leaks).Policy} {horizon : Nat}
    (event : setup.informationGraph.EventId) (execution : (application setup timeouts
      leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup timeouts leaks).Execution)
    (reached : stopped ∈ ((application setup timeouts leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support)
    (finished : event ∈ stopped.application.config.cut.completed) :
    stopped.environmentRecall.length ≤ horizon ∧
      ∃ actualRank, event.val < actualRank ∧
        CompletionBoundary setup leaks scheduler players actualRank stopped := by
  let app := application setup timeouts leaks
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup timeouts leaks scheduler players _
    execution
    boundary.supported
  have rankEq := EventOrder.Cut.IsPrefix.unique ranked boundary.ordered
  subst rankEq
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players _ _ execution
    stopped reached
  obtain ⟨stoppedSeen, stoppedConfig⟩ := runUntil_completion_prefix setup timeouts leaks scheduler
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
    (profile : setup.informationGraph.BehavioralProfile) (read : setup.informationGraph.Config →
      Outcome)
    {scheduler : (application setup timeouts leaks).Scheduler}
    {players : Player → (application setup timeouts leaks).Policy} {horizon : Nat}
    (completes : (CompletesPlay timeouts) leaks (initialLaw setup) horizon scheduler)
    (completionLaw : ∀ (event : setup.informationGraph.EventId)
      (execution : (application setup timeouts leaks).Execution),
      CompletionBoundary setup leaks scheduler players event.val execution →
      execution.environmentRecall.length ≤ horizon →
      ((application setup timeouts leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
          (fun final => (setup.informationGraph.runPlan
            (setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler)
            final.application.config.remaining final.application.config).map read) =
        (setup.informationGraph.runPlan
          (setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler)
          execution.application.config.remaining execution.application.config).map read)
    {rank : Nat} (execution : (application setup timeouts leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    ((application setup timeouts leaks).runToHorizon scheduler players horizon execution).map
        (fun final => read final.application.config) =
      (setup.informationGraph.runPlan
        (setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler)
        execution.application.config.remaining execution.application.config).map read := by
  let plan := setup.informationGraph.policyPlan profile setup.informationGraph.canonicalScheduler
  let atBoundary := fun before : (application setup timeouts leaks).Execution =>
    ∃ rank, CompletionBoundary setup leaks scheduler players rank before
  have localLaw : EventCompletionLaw plan read scheduler players horizon atBoundary := by
    intro before ⟨actualRank, current⟩ within nonterminal
    have active : actualRank < setup.informationGraph.order.eventCount := by
      apply lt_of_le_of_ne current.ordered.1
      intro equal
      exact nonterminal (equal ▸ current.ordered).terminal
    let event : setup.informationGraph.EventId := ⟨actualRank, active⟩
    refine ⟨event, fun done => (Nat.lt_irrefl actualRank) ((current.ordered.2 event).mp done),
      ?_, completionLaw event before current within⟩
    intro after reached done
    obtain ⟨_, next, _, later⟩ := current.stopped timeouts event before within after reached done
    exact ⟨next, later⟩
  exact localLaw.runToHorizon completes execution ⟨rank, boundary⟩ boundary.supported bounded


end Vegas
