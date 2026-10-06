/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTurnSettlement

/-! # The first-turn coupling against one deviating player

The turn-counted clients and their first-turn limit differ only in the owners'
timing lotteries. This stays true when one player follows an arbitrary native
policy: in the phase of an event owned by another player, the owner's lottery
over its turn index is untouched by the deviator, and its first branch is the
first-turn phase; in the phases of the deviator's own events and of chance
events, every other player is silent under both timings. Hence, for every
scheduler, every timing, every source profile and every policy of the deviating
player, the turn-counted and first-turn runs to the horizon, followed by any
common kernel, are within the total deferral weight of each other in total
variation (`Vegas.sourceServiceTurnPolicy_deviation_roundsFrom_bind_within`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The turn-counted clients of a profile, with one player replaced. -/
abbrev deviatedTurnProfile (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (application setup leaks).Policy) :
    Player → (application setup leaks).Policy :=
  Function.update (sourceServiceTurnPolicy setup leaks bound turns timing profile) who alternative

private theorem runRounds_eq_runUntil_never {Principal : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) :
    app.runRounds scheduler players count execution =
      app.runUntil scheduler players (fun _ => False) count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      simp only [ReactiveApplication.runRounds, ReactiveApplication.runUntil, ↓reduceIte]
      congr 1
      funext next
      exact ih next

/-- From a terminal configuration, the deviated turn-counted profile runs the
same for every timing. -/
theorem runRounds_deviation_terminal (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (first second : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (alternative : (application setup leaks).Policy) (count : Nat)
    (execution : (application setup leaks).Execution)
    (terminal : execution.application.config.cut.IsPrefix (graph setup).order.eventCount) :
    (application setup leaks).runRounds scheduler
        (deviatedTurnProfile bound turns first profile who alternative) count execution =
      (application setup leaks).runRounds scheduler
        (deviatedTurnProfile bound turns second profile who alternative) count execution := by
  let app := application setup leaks
  rw [runRounds_eq_runUntil_never, runRounds_eq_runUntil_never]
  apply app.runUntil_congr_of_agree scheduler _ _ _
    (fun current => current.application.config.cut.IsPrefix (graph setup).order.eventCount)
  · intro current holds _ command _ middle moved player active
    cases command with
    | activate actor =>
        have sameApp := activation_application setup leaks current middle actor moved
        by_cases same : player = who
        · subst same
          simp only [deviatedTurnProfile, Function.update_self]
        · simp only [deviatedTurnProfile, Function.update_of_ne same]
          rw [sourceServiceTurnPolicy_terminal bound turns first profile middle.application
              (by rw [sameApp]; exact holds) player _ _ rfl,
            sourceServiceTurnPolicy_terminal bound turns second profile middle.application
              (by rw [sameApp]; exact holds) player _ _ rfl]
    | «include» _ => cases active
    | application _ => cases active
    | wait => cases active
  · intro current holds _ next reached
    have one : next ∈ (app.runRounds scheduler
        (deviatedTurnProfile bound turns first profile who alternative) 1 current).support := by
      simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using reached
    rw [runRounds_config_terminal scheduler _ 1 current next holds one]
    exact holds
  · exact terminal

/-- Before stopping at the completion of `event`, the deviated turn-counted
profile runs as the deviated phase profile. -/
theorem runUntil_deviation_eq_phase (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (alternative : (application setup leaks).Policy)
    (event : (graph setup).EventId) (count : Nat) (execution : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution) :
    (application setup leaks).runUntil scheduler
        (deviatedTurnProfile bound turns timing profile who alternative)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (Function.update (phaseProfile setup leaks bound turns timing profile event) who
          alternative)
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
  · intro current holds running command _ middle moved player active
    have ordered := orderedOf current holds running
    have ready := (ready_iff_rank setup _ event.val ordered event).mpr rfl
    cases command with
    | activate actor =>
        have sameApp := activation_application setup leaks current middle actor moved
        by_cases same : player = who
        · subst same
          simp only [deviatedTurnProfile, Function.update_self]
        · simp only [deviatedTurnProfile, Function.update_of_ne same]
          exact sourceServiceTurnPolicy_eq_phaseProfile setup leaks bound turns timing profile
            event middle.application (by rw [sameApp]; exact ready) player _ _ rfl
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

/-- In the phase of an event without another owner, the deviated phase profile
does not depend on the timing. -/
theorem deviatedPhase_eq_of_not_foreign (bound : (graph setup).EventId → Nat) (turns : Nat)
    (first second : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (who : Player) (alternative : (application setup leaks).Policy)
    (event : (graph setup).EventId)
    (notForeign : ∀ owner, (graph setup).actor? event = some owner → owner = who) :
    Function.update (phaseProfile setup leaks bound turns first profile event) who alternative =
      Function.update (phaseProfile setup leaks bound turns second profile event) who
        alternative := by
  funext player
  by_cases same : player = who
  · subst same
    simp only [Function.update_self]
  · simp only [Function.update_of_ne same]
    cases owned : (graph setup).actor? event with
    | none =>
        rw [phaseProfile_actorless setup leaks bound turns first profile event owned,
          phaseProfile_actorless setup leaks bound turns second profile event owned]
    | some owner =>
        have owner_eq := notForeign owner owned
        have different : player ≠ owner := fun equal => same (equal.trans owner_eq)
        rw [phaseProfile_owned setup leaks bound turns first profile event owner owned,
          phaseProfile_owned setup leaks bound turns second profile event owner owned,
          Function.update_of_ne different, Function.update_of_ne different]

/-- **Phase decomposition by another owner's turn index.** Before an event
owned by a player other than the deviator completes, from an execution whose
recorded responses never saw it ready, the deviated turn-counted profile runs
as the owner's timing lottery over the members deciding at the selected turn,
every other honest player silent. -/
theorem runUntil_deviation_foreign (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (alternative : (application setup leaks).Policy)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (foreign : owner ≠ who) (count : Nat)
    (execution : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution)
    (untouched : Untouched setup leaks event execution) :
    (application setup leaks).runUntil scheduler
        (deviatedTurnProfile bound turns timing profile who alternative)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (timing event owner owned).bind (fun slot =>
        (application setup leaks).runUntil scheduler
          (Function.update (Function.update (fun _ => (application setup leaks).silentPolicy)
            who alternative) owner
            (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
          (fun final => event ∈ final.application.config.cut.completed) count execution) := by
  let app := application setup leaks
  rw [runUntil_deviation_eq_phase scheduler bound turns timing profile who alternative event count
    execution ordered seen, phaseProfile_owned setup leaks bound turns timing profile event owner
    owned]
  let mixture := app.policyMixture (timing event owner owned)
    (sourceServiceTurnFamily setup leaks bound profile owner event turns)
  have swapped : Function.update (Function.update (fun _ => app.silentPolicy) owner
      mixture.policy) who alternative =
      Function.update (Function.update (fun _ => app.silentPolicy) who alternative) owner
        mixture.policy :=
    Function.update_comm foreign _ _ _
  rw [swapped]
  have prior : mixture.posterior (execution.recall owner) = timing event owner owned := by
    apply app.policyMixture_posterior_of_agree _ _ app.silentPolicy
    intro earlier entry member slot
    apply app.turnScheduledPolicy_of_none
    apply sourceServiceTurn_of_not_turn
    intro turn
    have entryMember : entry ∈ execution.recall owner :=
      member.subset (List.mem_append_right _ (List.mem_singleton_self _))
    exact untouched owner entry entryMember (PublicView.ownTurn?_spec _ owner event turn).1
  rw [← app.runUntil_policyMixture scheduler (timing event owner owned)
    (sourceServiceTurnFamily setup leaks bound profile owner event turns) owner _ _ _ execution,
    prior]

/-- **The deviated turn-counted profile is close to its first-turn limit.** For
every scheduler, timing, source profile and policy of the deviating player, from
every completion boundary of rank `rank` within the horizon, the turn-counted
and first-turn runs to the horizon, followed by any common kernel, are within
the sum of the remaining events' deferral weights in total variation. -/
theorem sourceServiceTurnPolicy_deviation_runToHorizon_bind_within {β : Type}
    (scheduler : (application setup leaks).Scheduler) {horizon turns : Nat}
    {bound : (graph setup).EventId → Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (alternative : (application setup leaks).Policy)
    (readout : (application setup leaks).Execution → PMF β) (rank : Nat)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (deviatedTurnProfile bound turns timing profile who alternative) rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    PMF.WithinTV (∑ event ∈ Finset.univ.filter
        (fun event : (graph setup).EventId => rank ≤ event.val), timing.deferral event)
      (((application setup leaks).runToHorizon scheduler
        (deviatedTurnProfile bound turns timing profile who alternative) horizon execution).bind
          readout)
      (((application setup leaks).runToHorizon scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns) profile who alternative)
          horizon execution).bind readout) := by
  let app := application setup leaks
  let players := deviatedTurnProfile bound turns timing profile who alternative
  let limit := deviatedTurnProfile bound turns (firstTurnTiming setup turns) profile who
    alternative
  suffices remaining : ∀ gap rank (execution : app.Execution),
      (graph setup).order.eventCount - rank = gap →
      CompletionBoundary setup leaks scheduler players rank execution →
      execution.environmentRecall.length ≤ horizon →
      PMF.WithinTV (∑ event ∈ Finset.univ.filter
          (fun event : (graph setup).EventId => rank ≤ event.val), timing.deferral event)
        ((app.runToHorizon scheduler players horizon execution).bind readout)
        ((app.runToHorizon scheduler limit horizon execution).bind readout) from
    remaining _ rank execution rfl boundary bounded
  intro gap
  induction gap with
  | zero =>
      intro rank execution gapEq boundary bounded
      have rankEq : rank = (graph setup).order.eventCount := by
        have := boundary.ordered.1
        omega
      subst rankEq
      have same : app.runToHorizon scheduler players horizon execution =
          app.runToHorizon scheduler limit horizon execution := by
        unfold ReactiveApplication.runToHorizon
        exact runRounds_deviation_terminal scheduler bound turns timing
          (firstTurnTiming setup turns) profile who alternative _ execution boundary.ordered
      rw [same]
      exact (PMF.WithinTV.refl _).mono
        (Finset.sum_nonneg fun event _ => deferral_nonneg timing event)
  | succ gap ih =>
      intro rank execution gapEq boundary bounded
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
        app.runToHorizon_eq_runUntilHorizon_bind scheduler limit stop horizon execution,
        PMF.bind_bind, PMF.bind_bind]
      have later := PMF.WithinTV.bind_right (app.runUntilHorizon scheduler players stop horizon
          execution)
        (first := fun stopped => (app.runToHorizon scheduler players horizon stopped).bind readout)
        (second := fun stopped => (app.runToHorizon scheduler limit horizon stopped).bind readout)
        (error := ∑ other ∈ Finset.univ.filter
          (fun other : (graph setup).EventId => rank + 1 ≤ other.val), timing.deferral other)
        (fun stopped reached => by
          rcases app.runUntilHorizon_stopped scheduler players stop horizon
              (horizon - execution.environmentRecall.length) execution stopped (by omega)
              reached with done | spent
          · obtain ⟨stoppedBounded, stoppedBoundary⟩ := CompletionBoundary.stopped event execution
              boundary bounded stopped reached done
            exact ih (rank + 1) stopped (by omega) stoppedBoundary stoppedBounded
          · have frozen (any : Player → app.Policy) :
                app.runToHorizon scheduler any horizon stopped = PMF.pure stopped := by
              unfold ReactiveApplication.runToHorizon
              rw [spent, Nat.sub_self]
              rfl
            rw [frozen players, frozen limit]
            exact (PMF.WithinTV.refl _).mono
              (Finset.sum_nonneg fun other _ => deferral_nonneg timing other))
      have step : PMF.WithinTV (timing.deferral event)
          ((app.runUntilHorizon scheduler players stop horizon execution).bind
            (fun stopped => (app.runToHorizon scheduler limit horizon stopped).bind readout))
          ((app.runUntilHorizon scheduler limit stop horizon execution).bind
            (fun stopped => (app.runToHorizon scheduler limit horizon stopped).bind readout)) := by
        obtain ⟨ranked, rankedOrdered, rankedSeen⟩ := roundsFrom_ranked setup leaks scheduler
          players _ execution boundary.supported
        have rankEq := isPrefix_unique rankedOrdered boundary.ordered
        subst rankEq
        have seen : ReadySeen setup leaks event.val execution := rankedSeen
        unfold ReactiveApplication.runUntilHorizon
        by_cases foreignOwner : ∃ owner, (graph setup).actor? event = some owner ∧ owner ≠ who
        · obtain ⟨owner, owned, foreign⟩ := foreignOwner
          have untouched := boundary.untouched event rfl
          rw [runUntil_deviation_foreign scheduler bound turns timing profile who alternative
              event owner owned foreign _ execution boundary.ordered seen untouched,
            runUntil_deviation_foreign scheduler bound turns (firstTurnTiming setup turns)
              profile who alternative event owner owned foreign _ execution boundary.ordered seen
              untouched,
            PMF.bind_bind,
            show (firstTurnTiming setup turns) event owner owned = PMF.pure 0 from rfl,
            PMF.pure_bind]
          exact PMF.WithinTV.of_bind_point _ 0 _
            (le_of_eq (deferral_eq timing event owner owned).symm)
        · have notForeign : ∀ owner, (graph setup).actor? event = some owner → owner = who := by
            intro owner owned
            by_contra different
            exact foreignOwner ⟨owner, owned, different⟩
          rw [runUntil_deviation_eq_phase scheduler bound turns timing profile who alternative
              event _ execution boundary.ordered seen,
            runUntil_deviation_eq_phase scheduler bound turns (firstTurnTiming setup turns)
              profile who alternative event _ execution boundary.ordered seen,
            deviatedPhase_eq_of_not_foreign bound turns timing (firstTurnTiming setup turns)
              profile who alternative event notForeign]
          exact (PMF.WithinTV.refl _).mono (deferral_nonneg timing event)
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

/-- **Initialized deviated coupling.** For every scheduler, timing, source
profile and policy of the deviating player, the deviated turn-counted profile's
executions after `horizon` rounds from initialization, followed by any common
kernel, are within the total deferral weight of the deviated first-turn
profile's. -/
theorem sourceServiceTurnPolicy_deviation_roundsFrom_bind_within {β : Type}
    (scheduler : (application setup leaks).Scheduler) {horizon turns : Nat}
    {bound : (graph setup).EventId → Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (who : Player)
    (alternative : (application setup leaks).Policy)
    (readout : (application setup leaks).Execution → PMF β) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (deviatedTurnProfile bound turns timing profile who alternative) horizon).bind readout)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns) profile who alternative)
          horizon).bind readout) := by
  let app := application setup leaks
  unfold ReactiveApplication.roundsFrom
  rw [PMF.bind_bind, PMF.bind_bind]
  apply PMF.WithinTV.bind_right
  intro state supported
  have close := sourceServiceTurnPolicy_deviation_runToHorizon_bind_within (horizon := horizon)
    (bound := bound) scheduler timing profile who alternative readout 0
    (ReactiveApplication.Execution.initial app state)
    (initial_completionBoundary setup leaks scheduler _ state supported) (Nat.zero_le _)
  have all : Finset.univ.filter (fun event : (graph setup).EventId => 0 ≤ event.val) =
      Finset.univ :=
    Finset.filter_true_of_mem fun event _ => Nat.zero_le event.val
  rw [all] at close
  exact close

end Vegas
