/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnPrefix

/-! # Initialized source prefixes under the global first-turn policy

Ordered completion stops compose the real scheduler rounds. At every stopped
rank the initialized execution is an untouched completion boundary. The whole
decoded prefix law is the iterated effective source behavioral kernel, with
the same initial draw retained jointly.
-/

noncomputable section

namespace Vegas

open SourceProgram
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- All instructions strictly below `rank` have actually completed. -/
def sourceServiceRankCompleted (rank : Nat)
    (execution : (application setup leaks).Execution) : Prop :=
  ∀ event : (graph setup).EventId, event.val < rank →
    event ∈ execution.application.config.cut.completed

instance (rank : Nat) : DecidablePred (sourceServiceRankCompleted (setup := setup)
    (leaks := leaks) rank) := fun execution => inferInstanceAs
      (Decidable (∀ event : (graph setup).EventId, event.val < rank →
        event ∈ execution.application.config.cut.completed))

private theorem rankCompleted_zero (execution : (application setup leaks).Execution) :
    sourceServiceRankCompleted 0 execution := by
  intro event below
  omega

private theorem rankCompleted_of_prefix {rank : Nat}
    {execution : (application setup leaks).Execution}
    (ordered : execution.application.config.cut.IsPrefix rank) :
    sourceServiceRankCompleted rank execution := fun event below => (ordered.2 event).mpr below

private theorem runUntil_rank_eq_event (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (event : (graph setup).EventId) :
    ∀ count (execution : (application setup leaks).Execution),
      execution.application.config.cut.IsPrefix event.val →
      ReadySeen setup leaks event.val execution →
      (application setup leaks).runUntil scheduler players
          (sourceServiceRankCompleted (event.val + 1)) count execution =
        (application setup leaks).runUntil scheduler players
          (fun final => event ∈ final.application.config.cut.completed) count execution := by
  classical
  let app := application setup leaks
  intro count
  induction count with
  | zero => intros; rfl
  | succ count ih =>
      intro execution ordered seen
      have running : event ∉ execution.application.config.cut.completed :=
        fun member => Nat.lt_irrefl _ ((ordered.2 event).mp member)
      have notRank : ¬ sourceServiceRankCompleted (event.val + 1) execution :=
        fun stopped => running (stopped event (Nat.lt_succ_self _))
      simp only [ReactiveApplication.runUntil, notRank, running, ↓reduceIte]
      apply bind_congr_on_support _
      intro next reached
      obtain ⟨nextSeen, progressed⟩ := round_prefix setup leaks scheduler players event.val
        execution next ordered seen reached
      rcases progressed with same | advanced
      · exact ih next (by rw [same]; exact ordered) nextSeen
      · have done : event ∈ next.application.config.cut.completed :=
          (advanced.2 event).mpr (Nat.lt_succ_self _)
        rw [app.runUntil_of_stop scheduler players _ _ next
          (rankCompleted_of_prefix advanced),
          app.runUntil_of_stop scheduler players _ _ next done]

/-- At an actual untouched rank boundary, stopping at the next completed prefix is
exactly stopping at its current event. -/
theorem sourceServiceRank_runUntil_eq_event {scheduler : (application setup leaks).Scheduler}
    {players : Player → (application setup leaks).Policy} {horizon : Nat}
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution) :
    (application setup leaks).runUntilHorizon scheduler players
        (sourceServiceRankCompleted (event.val + 1)) horizon execution =
      (application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  classical
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler players _ execution
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  exact runUntil_rank_eq_event scheduler players event _ execution boundary.ordered seen

private theorem initial_boundary (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (initial : State L setup.context) (supported : initial ∈ setup.initialLaw.support) :
    CompletionBoundary setup leaks scheduler players 0
      (.initial (application setup leaks)
        (EventGraphRuntime.State.initial (setup.eventInputs initial))) := by
  let app := application setup leaks
  refine ⟨?_, EventOrder.Cut.empty_isPrefix _, ?_⟩
  · change ReactiveApplication.Execution.initial app _ ∈
      (app.roundsFrom (initialLaw setup) scheduler players 0).support
    rw [ReactiveApplication.roundsFrom, PMF.mem_support_bind_iff]
    refine ⟨EventGraphRuntime.State.initial (setup.eventInputs initial), ?_, ?_⟩
    · rw [initialLaw, PMF.support_map]
      exact ⟨initial, supported, rfl⟩
    · exact (PMF.mem_support_pure_iff _ _).mpr rfl
  · intro event rank who entry member
    simp [ReactiveApplication.Execution.initial] at member

private def optionalSourceStep [Fintype Player] (profile : BehavioralProfile setup.program) :
    setup.ProtocolState → PMF setup.ProtocolState
  | none => PMF.pure none
  | some before => (ProtocolState.behavioralStateStep setup.program profile before).map some

/-- A supported initial draw reaches exactly the requested completion
boundary, and its decoded prefix has the finite source-kernel law. -/
theorem sourceServiceFirstTurn_rank_law [Fintype Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support) :
    ∀ rank, rank ≤ (graph setup).order.eventCount →
      (∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          (sourceServiceRankCompleted rank) horizon
          (.initial (application setup leaks)
            (EventGraphRuntime.State.initial (setup.eventInputs initial)))).support,
        stopped.environmentRecall.length ≤ horizon ∧
          CompletionBoundary setup leaks scheduler
            (sourceServiceTurnPolicy setup leaks bound turns
              (firstTurnTiming setup turns) profile) rank stopped) ∧
      ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        (sourceServiceRankCompleted rank) horizon
        (.initial (application setup leaks)
          (EventGraphRuntime.State.initial (setup.eventInputs initial)))).map
          (fun stopped => sourceServicePrefix? setup rank stopped.application.config) =
        ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
          (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
            some := by
  classical
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let start := ReactiveApplication.Execution.initial app
    (EventGraphRuntime.State.initial (setup.eventInputs initial))
  let native := fun rank => app.runUntilHorizon scheduler players
    (sourceServiceRankCompleted rank) horizon start
  let source := fun rank =>
    (fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
      (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))
  change ∀ rank, rank ≤ _ →
    (∀ stopped ∈ (native rank).support,
      stopped.environmentRecall.length ≤ horizon ∧
        CompletionBoundary setup leaks scheduler players rank stopped) ∧
    (native rank).map (fun stopped => sourceServicePrefix? setup rank stopped.application.config)
      = (source rank).map some
  intro rank
  induction rank with
  | zero =>
      intro within
      have nativeZero : native 0 = PMF.pure start := by
        exact app.runUntil_of_stop scheduler players _ _ start (rankCompleted_zero start)
      rw [nativeZero]
      refine ⟨?_, ?_⟩
      · intro stopped reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact ⟨Nat.zero_le _, initial_boundary scheduler players initial initialSupport⟩
      · rw [PMF.pure_map]
        change PMF.pure (sourceServicePrefix? setup 0
            (EventGraphRuntime.State.initial (graph := graph setup)
              (setup.eventInputs initial)).config) = _
        rw [sourceServicePrefix?_initial]
        simp only [source, Function.iterate_zero_apply, PMF.pure_map]
  | succ rank ih =>
      intro within
      obtain ⟨supported, previous⟩ := ih (by omega)
      let event : (graph setup).EventId := ⟨rank, by omega⟩
      have composed : native (rank + 1) = (native rank).bind
          (app.runUntilHorizon scheduler players (sourceServiceRankCompleted (rank + 1))
            horizon) :=
        app.runUntilHorizon_eq_runUntilHorizon_bind scheduler players _ _
          (fun execution completed other before => completed other (by omega)) horizon start
      have phaseEq (execution : app.Execution) (reached : execution ∈ (native rank).support) :
          app.runUntilHorizon scheduler players (sourceServiceRankCompleted (rank + 1))
              horizon execution =
            app.runUntilHorizon scheduler players
              (fun final => event ∈ final.application.config.cut.completed) horizon execution :=
        sourceServiceRank_runUntil_eq_event event execution (supported execution reached).2
      refine ⟨?_, ?_⟩
      · intro stopped reached
        rw [composed, PMF.mem_support_bind_iff] at reached
        obtain ⟨execution, reached, later⟩ := reached
        obtain ⟨bounded, boundary⟩ := supported execution reached
        rw [phaseEq execution reached] at later
        exact CompletionBoundary.stopped event execution boundary bounded stopped later
          (completionRun_completes contract.completes event execution boundary bounded stopped
            later)
      · rw [composed, PMF.map_bind]
        calc
          _ = (native rank).bind fun execution => optionalSourceStep profile
              (sourceServicePrefix? setup rank execution.application.config) := by
            apply bind_congr_on_support _
            intro execution reached
            rw [phaseEq execution reached]
            obtain ⟨before, decoded, law⟩ := sourceServiceTurnPolicy_firstTurn_prefix_law
              contract timely profile effective event execution (supported execution reached).2
              (roundsFrom_turnFacts setup leaks
                (fun who => sourceServiceTurnPolicy_submitsAtTurn setup leaks _ _ _ _ who)
                _ _ (supported execution reached).2.supported).1
              (supported execution reached).1
            rw [decoded]
            exact law
          _ = ((native rank).map
              (fun execution => sourceServicePrefix? setup rank execution.application.config)).bind
                (optionalSourceStep profile) := by rw [PMF.bind_map]; rfl
          _ = ((source rank).map some).bind (optionalSourceStep profile) := by rw [previous]
          _ = (source (rank + 1)).map some := by
            rw [PMF.bind_map]
            change (source rank).bind (fun before =>
                (ProtocolState.behavioralStateStep setup.program profile before).map some) = _
            rw [← PMF.map_bind]
            dsimp only [source]
            rw [Function.iterate_succ_apply']

/-- The initialized rank-prefix law retains any reading of the same initial
draw jointly. Initial parameters may be correlated with the complete source
prefix and need not be independent of any player's information. -/
theorem sourceServiceFirstTurn_rank_joint_law [Fintype Player] {Parameter : Type}
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (parameter : State L setup.context → Parameter)
    (rank : Nat) (within : rank ≤ (graph setup).order.eventCount) :
    (setup.initialLaw.bind fun initial =>
      ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        (sourceServiceRankCompleted rank) horizon
        (.initial (application setup leaks)
          (EventGraphRuntime.State.initial (setup.eventInputs initial)))).map
            (fun stopped => (parameter initial,
              sourceServicePrefix? setup rank stopped.application.config))) =
      setup.initialLaw.bind fun initial =>
        ((fun law => law.bind (ProtocolState.behavioralStateStep setup.program profile))^[rank]
          (PMF.pure (ProtocolState.entry setup.program (setup.initialConfig initial)))).map
            (fun before => (parameter initial, some before)) := by
  classical
  apply bind_congr_on_support _
  intro initial supported
  have law := (sourceServiceFirstTurn_rank_law (turns := turns) contract timely profile effective
    initial supported rank within).2
  have retained := congrArg (PMF.map (fun state => (parameter initial, state))) law
  simpa only [PMF.map_comp, Function.comp_def] using retained

end Vegas
