/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceTurnPolicy
import GameTheoryExtensions.Math.Probability.TotalVariation

/-! # Boundary continuations of the service

The source continuation of a configuration's typed prefix
(`Vegas.sourceContinuation`), the approximate continuation law from completion
boundaries (`Vegas.BoundaryContinuationWithin`), and the facts about
completion runs and terminal rounds they use: an activation leaves the
application unchanged (`Vegas.activation_application`), rounds from a terminal
configuration keep it (`Vegas.runRounds_config_terminal`), and a stopped point
of a completion run from a completion boundary at which the event has completed
is the next boundary (`Vegas.CompletionBoundary.stopped`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The source continuation of the configuration's typed prefix of rank `rank`. -/
def sourceContinuation (profile : BehavioralProfile setup.program) (rank : Nat)
    (config : (serviceGraph setup mode).Config) : PMF
    (Option (State L setup.program.terminalCtx)) :=
  (setup.continuationLaw profile (serviceSourcePrefix? setup mode rank config)).map some

/-- An activation leaves the application unchanged. -/
theorem activation_application
    (execution middle : (serviceApplication setup mode deadline leaks).Execution) (who : Player)
    (moved : middle ∈
        (execution.environmentStep (serviceApplication setup mode deadline leaks)
        (.activate who)).support) :
    middle.application = execution.application := by
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  rw [PMF.support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

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
      have stepConfig : stepped.application.config = execution.application.config := by
        rcases environmentStep_configStep setup leaks execution stepped command stepMember with
          same | ⟨event, ready, _, _⟩
        · exact same
        · exact (ready.1 ((terminal.2 event).mpr event.isLt)).elim
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
def BoundaryContinuationWithin (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (players : Player → (application setup leaks).Policy)
    (profile : BehavioralProfile setup.program) (error : Nat → ℝ) : Prop :=
  ∀ rank (execution : (application setup leaks).Execution),
    CompletionBoundary setup leaks scheduler players rank execution →
    execution.environmentRecall.length ≤ horizon →
    PMF.WithinTV (error rank)
      (((application setup leaks).runToHorizon scheduler players horizon execution).map
        (fun final => sourceReadout setup leaks ((application setup leaks).finished final)))
      (sourceContinuation setup profile rank execution.application.config)

/-- With no error, the approximate law is the exact one. -/
theorem BoundaryContinuationWithin.law {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    {profile : BehavioralProfile setup.program} {error : Nat → ℝ}
    (within : BoundaryContinuationWithin setup leaks scheduler horizon players profile error)
    (zero : ∀ rank, error rank = 0) :
    BoundaryContinuationLaw setup leaks scheduler horizon players profile := by
  intro rank execution boundary bounded
  have close := within rank execution boundary bounded
  rw [zero rank] at close
  exact close.eq_of_zero
variable {setup leaks}
/-- A stopped point of a completion run from a completion boundary at which
the event has completed is the next boundary, within the horizon. -/
theorem CompletionBoundary.stopped {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} {horizon : Nat}
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support)
    (finished : event ∈ stopped.application.config.cut.completed) :
    stopped.environmentRecall.length ≤ horizon ∧
      CompletionBoundary setup leaks scheduler players (event.val + 1) stopped := by
  let app := application setup leaks
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler players _ execution
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  obtain ⟨used, within, _, length⟩ := app.runUntil_runRounds scheduler players _ _ execution
    stopped reached
  obtain ⟨stoppedSeen, stoppedConfig⟩ := runUntil_completion_prefix setup leaks scheduler
    players event _ execution stopped boundary.ordered seen reached
  refine ⟨by omega, app.roundsFrom_runUntil scheduler players (initialLaw setup) _ _ execution
    stopped boundary.supported reached, ?_, ?_⟩
  · rcases stoppedConfig with current | advanced
    · exact (Nat.lt_irrefl _ ((current.2 event).mp finished)).elim
    · exact advanced
  · intro next rankNext observer entry member readyView
    have := stoppedSeen observer entry member next readyView
    omega

end Vegas
