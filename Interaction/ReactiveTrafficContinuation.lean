/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveTrafficState
import Interaction.ReactiveRounds

/-! # Traffic evidence through actual runtime continuations

The physical round evaluator and the canonical history evaluator preserve the
same traffic records. These results allow arbitrary responses and schedulers;
neither conformance nor eventual acceptance of an envelope is required.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem executionTraffic_environment (execution next : app.Execution) (command : app.Command)
    (reached : next ∈ (execution.environmentStep app command).support) :
    app.executionTraffic next = app.executionTraffic execution := by
  have recorded : next.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, command⟩] := by
    obtain ⟨raw, _, rfl⟩ := FinDist.support_map .. ▸ reached
    rfl
  have sameInputs := app.environmentStep_inputs execution next command reached
  simp only [executionTraffic, recorded, List.map_append, List.map_cons, List.map_nil,
    trafficViews_append]
  have empty : app.trafficBetween (execution.observeEnvironment app)
      (next.observeEnvironment app) = [] := by
    simp [trafficBetween, Execution.observeEnvironment, MessageNetwork.publicView, sameInputs]
  rw [empty, List.append_nil]

/-- An activation records the current public view before the response. The
response therefore appends exactly the traffic observed across the dispatch. -/
theorem executionTraffic_activated_response (execution activated : app.Execution)
    (who : Principal) (action : app.Action) (remaining : Nat)
    (reached : activated ∈ (execution.environmentStep app (.activate who)).support) :
    app.executionTraffic (activated.respond app who action) =
      app.executionTraffic execution ++ app.trafficStep
        (some ⟨remaining + 1, none, execution⟩)
        (some ⟨remaining, none, activated.respond app who action⟩) := by
  have recorded : activated.environmentRecall = execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .activate who⟩] := by
    obtain ⟨raw, _, rfl⟩ := FinDist.support_map .. ▸ reached
    rfl
  simp only [executionTraffic, app.respond_environmentRecall, recorded, List.map_append,
    List.map_cons, List.map_nil, trafficViews_append]
  rfl

theorem executionTraffic_dispatch (players : Principal → app.Policy) (command : app.Command)
    (execution next : app.Execution)
    (reached : next ∈ (app.dispatch players command execution).support) :
    app.executionTraffic execution <+: app.executionTraffic next := by
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  cases command with
  | activate who =>
      obtain ⟨action, _, rfl⟩ := FinDist.support_map .. ▸ resumed
      rw [app.executionTraffic_activated_response execution middle who action 0 moved]
      exact List.prefix_append ..
  | wait | application operation | «include» id =>
      cases FinDist.mem_support_pure.mp resumed
      rw [app.executionTraffic_environment execution next _ moved]

theorem executionTraffic_runRounds (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (count : Nat) (execution next : app.Execution)
    (reached : next ∈ (app.runRounds scheduler players count execution).support) :
    app.executionTraffic execution <+: app.executionTraffic next := by
  induction count generalizing execution with
  | zero => cases FinDist.mem_support_pure.mp reached; rfl
  | succ count ih =>
      obtain ⟨middle, stepped, rest⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      obtain ⟨command, _, dispatched⟩ := Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ stepped)
      exact (app.executionTraffic_dispatch players command execution middle dispatched).trans
        (ih middle rest)

theorem stateTraffic_reaches (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last) :
    app.stateTraffic first.state <+: app.stateTraffic last.state := by
  rw [← app.trafficAudit_eq_stateTraffic initial horizon scheduler first.trace,
    ← app.trafficAudit_eq_stateTraffic initial horizon scheduler last.trace]
  exact app.trafficAudit_reaches initial horizon scheduler path

/-- Completing the actual runtime from a legal prefix retains all evidence,
including an unfinished activation's response and every subsequent round. -/
theorem stateTraffic_finish (initial : FinDist app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (players : Principal → app.Policy)
    (history : (app.protocol initial horizon scheduler).History) (next : app.ProtocolState)
    (reached : next ∈ (app.finish initial horizon scheduler players history.state).support) :
    app.stateTraffic history.state <+: app.stateTraffic next := by
  have law := (app.run_map_state initial horizon scheduler players
    (app.rank horizon history.state) history).trans
      (app.iterate_eq_finish initial horizon scheduler players
        (app.rank horizon history.state) history.state (by rfl))
  have supported := (congrArg
    (fun distribution : FinDist app.ProtocolState => next ∈ distribution.support) law.symm).mp
      reached
  obtain ⟨final, member, rfl⟩ := FinDist.support_map .. ▸ supported
  exact app.stateTraffic_reaches initial horizon scheduler
    ((app.protocol initial horizon scheduler).runRandomizedFor_reachesWithin
      ((app.information initial horizon scheduler).singleMoverChooser
        (app.singleMover initial horizon scheduler) (fun who => app.encodePolicy (players who)))
      _ history final member)

end Interaction.ReactiveApplication
