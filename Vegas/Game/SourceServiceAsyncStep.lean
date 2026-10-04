/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTurnPolicy
import Vegas.Game.SourceServiceCompletion
import Interaction.ReactiveRawRoundTrace

/-! # The approximate step law of the turn-counted policy

From an untouched completion boundary, the turn-counted prescribed policy
completes the current event and continues in the source within the event's
deferral weight of the source continuation, for every scheduler. Before the
event completes it is the only ready event, so every other player replays and
the owner follows its timing mixture; the mixture splits by the chosen turn,
whose prior is untouched by the boundary's recall; and the first-turn branch
carries all but the deferral weight.

That the first-turn branch is exact, that the event completes before the
horizon, and that a terminal boundary reads out its source state are collected
in `Vegas.FirstTurnCompletes`. Chaining the step law over the remaining
events gives the approximate continuation law
(`Vegas.sourceServiceTurnPolicy_boundaryContinuationWithin`), with error the
sum of the remaining deferral weights.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The source continuation of the configuration's typed prefix of rank `rank`. -/
def sourceContinuation (profile : BehavioralProfile setup.program) (rank : Nat)
    (config : (graph setup).Config) : PMF (Option (State L setup.program.terminalCtx)) :=
  (setup.continuationLaw profile (sourceServicePrefix? setup rank config)).map some

/-- The profile in which an event's owner, if any, decides at its first turn
and every other response replays. -/
def firstTurnProfile (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) : Player → (application setup leaks).Policy :=
  match (graph setup).actor? event with
  | none => fun _ => (application setup leaks).replayPolicy
  | some owner => Function.update (fun _ => (application setup leaks).replayPolicy) owner
      (sourceServiceTurnFamily setup leaks bound profile owner event turns 0)

/-- **The first-turn premises of the step law.** For the turn-counted policy
with inclusion bound `bound` under `scheduler` up to `horizon`, from every
completion boundary within the horizon:

* `completes`: the current event completes before the run stops;
* `exact`: if its owner decides at the first turn, completing the event and
  continuing in the source is exactly the source continuation;
* `terminal`: at the terminal boundary the source continuation is the point
  mass at the readout.

The asynchronous preservation argument must derive these premises from the
service contract, timeliness and the source correspondence. This structure
records the required continuation facts; it does not prove them. -/
structure FirstTurnCompletes (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) :
    Prop where
  completes : ∀ (event : (graph setup).EventId) (execution : (application setup leaks).Execution),
    CompletionBoundary setup leaks scheduler (sourceServiceTurnPolicy setup leaks bound turns timing
      profile) event.val execution →
    execution.environmentRecall.length ≤ horizon →
    ∀ stopped ∈ ((application setup leaks).runUntilHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support,
      event ∈ stopped.application.config.cut.completed
  exact : ∀ (event : (graph setup).EventId) (execution : (application setup leaks).Execution),
    CompletionBoundary setup leaks scheduler (sourceServiceTurnPolicy setup leaks bound turns timing
      profile) event.val execution →
    execution.environmentRecall.length ≤ horizon →
    ((application setup leaks).runUntilHorizon scheduler
      (firstTurnProfile setup leaks bound turns profile event)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (fun stopped => sourceContinuation setup profile (event.val + 1)
          stopped.application.config) =
      sourceContinuation setup profile event.val execution.application.config
  terminal : ∀ execution : (application setup leaks).Execution,
    CompletionBoundary setup leaks scheduler (sourceServiceTurnPolicy setup leaks bound turns timing
      profile) (graph setup).order.eventCount execution →
    sourceContinuation setup profile (graph setup).order.eventCount
        execution.application.config =
      PMF.pure (sourceReadout setup leaks ((application setup leaks).finished execution))

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

/-- An activation leaves the application unchanged. -/
theorem activation_application (execution middle : (application setup leaks).Execution)
    (who : Player)
    (moved : middle ∈ (execution.environmentStep (application setup leaks)
      (.activate who)).support) :
    middle.application = execution.application := by
  unfold ReactiveApplication.Execution.environmentStep at moved
  rw [PMF.support_map] at moved
  obtain ⟨updated, supported, rfl⟩ := moved
  rw [PMF.support_map] at supported
  obtain ⟨_, _, rfl⟩ := supported
  rfl

/-- Before the current event completes, the turn-counted policy is the owner's
timing mixture for that event, with every other response replaying. -/
def phaseProfile (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) :
    Player → (application setup leaks).Policy :=
  match owned : (graph setup).actor? event with
  | none => fun _ => (application setup leaks).replayPolicy
  | some owner => Function.update (fun _ => (application setup leaks).replayPolicy) owner
      ((application setup leaks).policyMixture (timing event owner owned)
        (sourceServiceTurnFamily setup leaks bound profile owner event turns)).policy

theorem phaseProfile_actorless (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId)
    (actorless : (graph setup).actor? event = none) :
    phaseProfile setup leaks bound turns timing profile event =
      fun _ => (application setup leaks).replayPolicy := by
  unfold phaseProfile
  split
  · rfl
  · rename_i owner owned
    rw [actorless] at owned
    cases owned

theorem phaseProfile_owned (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) :
    phaseProfile setup leaks bound turns timing profile event =
      Function.update (fun _ => (application setup leaks).replayPolicy) owner
        ((application setup leaks).policyMixture (timing event owner owned)
          (sourceServiceTurnFamily setup leaks bound profile owner event turns)).policy := by
  unfold phaseProfile
  split
  · rename_i actorless
    rw [owned] at actorless
    cases actorless
  · rename_i who ownedWho
    have same : who = owner := Option.some.inj (ownedWho.symm.trans owned)
    subst same
    rfl

/-- At a state where `event` is the ready event, the turn-counted policy and
the phase profile agree for every player. -/
theorem sourceServiceTurnPolicy_eq_phaseProfile (bound : (graph setup).EventId → Nat)
    (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId)
    (state : EventGraphRuntime.State (graph setup)) (ready : state.config.cut.Ready event)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (current : view.application.publicView = state.publicView) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who past view =
      phaseProfile setup leaks bound turns timing profile event who past view := by
  have sole := soleReady_of_ready setup state ready
  rw [← current] at sole
  cases owned : (graph setup).actor? event with
  | none =>
      rw [phaseProfile_actorless setup leaks bound turns timing profile event owned]
      have foreign : (graph setup).actor? event ≠ some who := by rw [owned]; simp
      simp only [sourceServiceTurnPolicy, sole.ownTurn?_foreign foreign]
  | some owner =>
      rw [phaseProfile_owned setup leaks bound turns timing profile event owner owned]
      by_cases same : who = owner
      · subst who
        rw [Function.update_self]
        exact sourceServiceTurnPolicy_turn setup leaks bound turns timing profile owner past view
          event
          owned (PublicView.ownTurn?_of_ownTurn _ owner event (sole.ownTurn owned))
      · rw [Function.update_of_ne same]
        have foreign : (graph setup).actor? event ≠ some who := by
          rw [owned]
          exact fun equal => same (Option.some.inj equal).symm
        simp only [sourceServiceTurnPolicy, sole.ownTurn?_foreign foreign]

variable {setup leaks}

/-- Before stopping at the completion of `event`, the turn-counted policy runs
as the phase profile. -/
theorem runUntil_turnPolicy_eq_phase (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (count : Nat) (execution : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution) :
    (application setup leaks).runUntil scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (phaseProfile setup leaks bound turns timing profile event)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := application setup leaks
  let invariant := fun current : app.Execution =>
    ReadySeen setup leaks event.val current ∧
      (current.application.config.cut.IsPrefix event.val ∨
        current.application.config.cut.IsPrefix (event.val + 1))
  have orderedOf (current : app.Execution) (holds : invariant current)
      (running : ¬ event ∈ current.application.config.cut.completed) :
      current.application.config.cut.IsPrefix event.val := by
    rcases holds.2 with ordered | advanced
    · exact ordered
    · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim
  apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
  · intro current holds running command _ middle moved who active
    have ordered := orderedOf current holds running
    have ready := (ready_iff_rank setup _ event.val ordered event).mpr rfl
    cases command with
    | activate actor =>
        have sameApp := activation_application setup leaks current middle actor moved
        exact sourceServiceTurnPolicy_eq_phaseProfile setup leaks bound turns timing profile event
          middle.application (by rw [sameApp]; exact ready) who _ _ rfl
    | «include» _ => cases active
    | application _ => cases active
    | wait => cases active
  · intro current holds running next reached
    obtain ⟨nextSeen, nextConfig⟩ := round_prefix setup leaks scheduler _ event.val current next
      (orderedOf current holds running) holds.1 reached
    refine ⟨nextSeen, ?_⟩
    rcases nextConfig with same | advanced
    · rw [same]
      exact Or.inl (orderedOf current holds running)
    · exact Or.inr advanced
  · exact ⟨seen, Or.inl ordered⟩

/-- The deferral weight bounds the mass off the first turn. -/
theorem deferral_eq {turns : Nat} (timing : TurnTiming setup turns)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) :
    timing.deferral event = 1 - (timing event owner owned 0).toReal := by
  unfold TurnTiming.deferral
  split
  · rename_i actorless
    rw [owned] at actorless
    cases actorless
  · rename_i who ownedWho
    have same : who = owner := Option.some.inj (ownedWho.symm.trans owned)
    subst same
    rfl

theorem deferral_nonneg {turns : Nat} (timing : TurnTiming setup turns)
    (event : (graph setup).EventId) : 0 ≤ timing.deferral event := by
  unfold TurnTiming.deferral
  split
  · exact le_rfl
  · rename_i who owned
    have atMost : (timing event who owned 0).toReal ≤ 1 :=
      ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using PMF.coe_le_one _ 0)
    linarith

/-- **Approximate step law.** From an untouched completion boundary of rank
`event.val`, completing the event and continuing in the source is within the
event's deferral weight of the source continuation. -/
theorem sourceServiceTurnPolicy_step_within {scheduler : (application setup leaks).Scheduler}
    {horizon turns : Nat} {bound : (graph setup).EventId → Nat} {timing : TurnTiming setup turns}
    {profile : BehavioralProfile setup.program}
    (first : FirstTurnCompletes setup leaks scheduler horizon bound turns timing profile)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile) event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    PMF.WithinTV (timing.deferral event)
      (((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns timing profile)
          (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
        (fun stopped => sourceContinuation setup profile (event.val + 1)
          stopped.application.config))
      (sourceContinuation setup profile event.val execution.application.config) := by
  let app := application setup leaks
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler _ _ execution
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  have exact := first.exact event execution boundary bounded
  unfold ReactiveApplication.runUntilHorizon at exact ⊢
  rw [runUntil_turnPolicy_eq_phase scheduler bound turns timing profile event _ execution
    boundary.ordered seen]
  unfold firstTurnProfile at exact
  cases owned : (graph setup).actor? event with
  | none =>
    rw [phaseProfile_actorless setup leaks bound turns timing profile event owned]
    simp only [owned] at exact
    rw [exact]
    exact (PMF.WithinTV.refl _).mono (deferral_nonneg timing event)
  | some owner =>
    rw [phaseProfile_owned setup leaks bound turns timing profile event owner owned]
    simp only [owned] at exact
    let mixture := app.policyMixture (timing event owner owned)
      (sourceServiceTurnFamily setup leaks bound profile owner event turns)
    have prior : mixture.posterior (execution.recall owner) = timing event owner owned := by
      apply app.policyMixture_posterior_of_agree _ _ app.replayPolicy
      intro earlier entry member slot
      apply app.turnScheduledPolicy_of_none
      apply sourceServiceTurn_of_not_turn
      intro turn
      have entryMember : entry ∈ execution.recall owner :=
        member.subset (List.mem_append_right _ (List.mem_singleton_self _))
      exact boundary.untouched event rfl owner entry entryMember
        (PublicView.ownTurn?_spec _ owner event turn).1
    rw [← app.runUntil_policyMixture scheduler (timing event owner owned)
      (sourceServiceTurnFamily setup leaks bound profile owner event turns) owner _ _ _ execution,
      prior, PMF.bind_bind]
    have close := PMF.WithinTV.of_bind_point (timing event owner owned) 0
      (fun slot => (app.runUntil scheduler (Function.update (fun _ => app.replayPolicy) owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
        (fun final => event ∈ final.application.config.cut.completed)
        (horizon - execution.environmentRecall.length) execution).bind
          (fun stopped => sourceContinuation setup profile (event.val + 1)
            stopped.application.config))
      (error := timing.deferral event) (le_of_eq (deferral_eq timing event owner owned).symm)
    rwa [exact] at close

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

/-- Rounds from a terminal configuration keep the configuration. -/
theorem runRounds_config_terminal (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (execution next : (application setup leaks).Execution)
    (terminal : execution.application.config.cut.IsPrefix (graph setup).order.eventCount)
    (reached : next ∈ ((application setup leaks).runRounds scheduler players count
      execution).support) :
    next.application.config = execution.application.config := by
  let app := application setup leaks
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
        rcases (environmentStep_configStep setup leaks execution stepped command stepMember).prefix
            _ terminal with same | beyond
        · exact same
        · exact absurd beyond.1 (Nat.not_succ_le_self _)
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
            rw [((runtime setup).reactive_respond_application leaks stepped who response).1,
              stepConfig]
      have terminalMiddle : middle.application.config.cut.IsPrefix
          (graph setup).order.eventCount := by
        rw [middleConfig]
        exact terminal
      rw [ih middle terminalMiddle rest, middleConfig]

/-- **Approximate continuation law of the turn-counted policy.** Given the
first-turn premises, from every completion boundary of rank `rank` within the
horizon, the run is within the sum of the remaining events' deferral weights
of the source continuation. -/
theorem sourceServiceTurnPolicy_boundaryContinuationWithin
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {bound : (graph setup).EventId → Nat}
    {timing : TurnTiming setup turns} {profile : BehavioralProfile setup.program}
    (first : FirstTurnCompletes setup leaks scheduler horizon bound turns timing profile) :
    BoundaryContinuationWithin setup leaks scheduler horizon
      (sourceServiceTurnPolicy setup leaks bound turns timing profile) profile
      (fun rank => ∑ event ∈ Finset.univ.filter
        (fun event : (graph setup).EventId => rank ≤ event.val), timing.deferral event) := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns timing profile
  let readout := fun final : app.Execution => sourceReadout setup leaks (app.finished final)
  suffices remaining : ∀ gap rank (execution : app.Execution),
      (graph setup).order.eventCount - rank = gap →
      CompletionBoundary setup leaks scheduler players rank execution →
      execution.environmentRecall.length ≤ horizon →
      PMF.WithinTV (∑ event ∈ Finset.univ.filter
          (fun event : (graph setup).EventId => rank ≤ event.val), timing.deferral event)
        ((app.runToHorizon scheduler players horizon execution).map readout)
        (sourceContinuation setup profile rank execution.application.config) by
    intro rank execution boundary bounded
    exact remaining _ rank execution rfl boundary bounded
  intro gap
  induction gap with
  | zero =>
      intro rank execution gapEq boundary bounded
      have within := boundary.ordered.1
      have rankEq : rank = (graph setup).order.eventCount := by omega
      subst rankEq
      have empty : Finset.univ.filter (fun event : (graph setup).EventId =>
          (graph setup).order.eventCount ≤ event.val) = ∅ := by
        apply Finset.filter_false_of_mem
        intro event _
        exact Nat.not_le.mpr event.isLt
      rw [empty, Finset.sum_empty, first.terminal execution boundary]
      have frozen : (app.runToHorizon scheduler players horizon execution).map readout =
          PMF.pure (readout execution) := by
        unfold ReactiveApplication.runToHorizon
        rw [map_congr_on_support _ (g := fun _ => readout execution) (fun next reached => by
          have same := runRounds_config_terminal scheduler players _ execution next
            boundary.ordered reached
          change sourceReadout setup leaks (some ⟨0, none, next⟩) =
            sourceReadout setup leaks (some ⟨0, none, execution⟩)
          simp only [sourceReadout, Option.bind_some, same])]
        exact PMF.map_const _ _
      rw [frozen]
      exact PMF.WithinTV.refl _
  | succ gap ih =>
      intro rank execution gapEq boundary bounded
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
        PMF.map_bind]
      have later := PMF.WithinTV.bind_right (app.runUntilHorizon scheduler players stop horizon
          execution)
        (first := fun stopped => (app.runToHorizon scheduler players horizon stopped).map readout)
        (second := fun stopped => sourceContinuation setup profile (rank + 1)
          stopped.application.config)
        (error := ∑ other ∈ Finset.univ.filter
          (fun other : (graph setup).EventId => rank + 1 ≤ other.val), timing.deferral other)
        (fun stopped reached => by
          obtain ⟨stoppedBounded, stoppedBoundary⟩ := CompletionBoundary.stopped event execution
            boundary bounded stopped reached
            (first.completes event execution boundary bounded stopped reached)
          exact ih (rank + 1) stopped (by omega) stoppedBoundary stoppedBounded)
      have step := sourceServiceTurnPolicy_step_within first event execution boundary bounded
      have total : (∑ other ∈ Finset.univ.filter
            (fun other : (graph setup).EventId => rank + 1 ≤ other.val),
            timing.deferral other) + timing.deferral event =
          ∑ other ∈ Finset.univ.filter
            (fun other : (graph setup).EventId => rank ≤ other.val), timing.deferral other := by
        have single : timing.deferral event =
            ∑ other, if other = event then timing.deferral other else 0 := by simp
        rw [Finset.sum_filter, Finset.sum_filter, single, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro other _
        by_cases same : other = event
        · subst same
          simp [event]
        · have different : other.val ≠ rank := fun equal => same (Fin.ext equal)
          by_cases above : rank + 1 ≤ other.val
          · simp [above, show rank ≤ other.val by omega, same]
          · simp [above, show ¬ rank ≤ other.val by omega, same]
      exact (later.trans step).mono total.le

/-- Under complete play, every stopped point of a completion run from a
completion boundary within the horizon has completed the event, for any
players. -/
theorem completionRun_completes {scheduler : (application setup leaks).Scheduler}
    {horizon : Nat} {players : Player → (application setup leaks).Policy}
    (complete : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution).support) :
    event ∈ stopped.application.config.cut.completed := by
  let app := application setup leaks
  rcases app.runUntilHorizon_stopped scheduler players _ horizon
      (horizon - execution.environmentRecall.length) execution stopped (by omega) reached with
    done | spent
  · exact done
  · have supported := app.roundsFrom_runUntil scheduler players (initialLaw setup) _ _ execution
      stopped boundary.supported reached
    obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players _
      (by omega) stopped supported
    have terminal := complete _ trace (by
      change horizon - stopped.environmentRecall.length = 0 ∧ _
      exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

end Vegas
