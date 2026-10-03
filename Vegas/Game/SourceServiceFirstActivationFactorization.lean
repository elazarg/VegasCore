/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstActivation
import Vegas.Game.SourceServiceStoppedBindingTraffic

/-! # The actual first-owner-input channel during a binding

The actual initialized first-turn policy is used throughout the stopping law.
Before the first ready owner response, foreign players have no ready turn.
At the stopping activation the response lottery integrates out, leaving the
same actual passive input. The whole public scheduling prefix is retained.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private theorem foreign_ready_policy_silent
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner actor : Player)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) (foreign : actor ≠ owner) :
    sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile actor
        (execution.recall actor) (execution.observe (application setup leaks) actor) =
      (application setup leaks).silentPolicy (execution.recall actor)
        (execution.observe (application setup leaks) actor) := by
  apply sourceServiceTurnPolicy_idle setup leaks bound turns _ profile actor _ _
  apply (soleReady_of_ready setup execution.application ready).idle
  rw [owned]
  intro equal
  exact foreign (Option.some.inj equal).symm

private theorem invoke_stopped_input
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (owner : Player)
    (event : (graph setup).EventId) (count : Nat)
    (execution : (application setup leaks).Execution)
    (turn : execution.application.publicView.ownTurn? owner = some event) :
    ((application setup leaks).invoke players owner execution).bind
        (fun next => ((application setup leaks).runUntil scheduler players
          (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠
            none) count next).map
              (fun final => sourceServiceTurnInput? setup leaks owner event
                (final.recall owner))) =
      PMF.pure (some (execution.recall owner,
        execution.observe (application setup leaks) owner)) := by
  let app := application setup leaks
  simp only [ReactiveApplication.invoke, PMF.bind_map, Function.comp_def]
  have each (response : app.Action) :
      (app.runUntil scheduler players
        (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠
          none) count (execution.respond app owner response)).map
            (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner)) =
        PMF.pure (some (execution.recall owner, execution.observe app owner)) := by
    have input := sourceServiceTurnInput?_respond owner event execution turn response
    rw [app.runUntil_of_stop scheduler players _ count _
        (by rw [input]; exact Option.some_ne_none _),
      PMF.pure_map, input]
  dsimp only [app] at each
  simp only [each, PMF.bind_const]

private theorem prehit_round_continuation_silent
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (event : (graph setup).EventId) (count : Nat)
    (execution : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner) :
    ((application setup leaks).round scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        execution).bind (fun next =>
          ((application setup leaks).runUntil scheduler
            (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
              profile)
            (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠
              none) count next).map
                (fun final => sourceServiceTurnInput? setup leaks owner event
                  (final.recall owner))) =
      ((application setup leaks).round scheduler
        (fun _ => (application setup leaks).silentPolicy) execution).bind (fun next =>
          ((application setup leaks).runUntil scheduler
            (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
              profile)
            (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠
              none) count next).map
                (fun final => sourceServiceTurnInput? setup leaks owner event
                  (final.recall owner))) := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  simp only [ReactiveApplication.round, ReactiveApplication.dispatch, PMF.bind_bind]
  apply bind_congr_on_support _
  intro command _
  apply bind_congr_on_support _
  intro middle observed
  cases command with
  | activate actor =>
      have configEq := activation_application setup leaks execution middle actor observed
      have middleReady : middle.application.config.cut.Ready event := by
        rw [configEq]
        exact ready
      by_cases own : actor = owner
      · subst actor
        have turn := ownTurn?_of_ready setup middle.application middleReady owned
        simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume]
        rw [invoke_stopped_input setup leaks scheduler players owner event count middle turn]
        simp only [ReactiveApplication.invoke, ReactiveApplication.silentPolicy_apply,
          PMF.pure_map, PMF.pure_bind]
        have input := sourceServiceTurnInput?_respond owner event middle turn ⟨none⟩
        rw [app.runUntil_of_stop scheduler players _ count _
          (by rw [input]; exact Option.some_ne_none _), PMF.pure_map, input]
      · have policy := foreign_ready_policy_silent setup leaks bound turns profile middle
          event owner actor middleReady owned own
        simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          ReactiveApplication.invoke, policy]
  | «include» _ | wait | application _ => rfl

private theorem silent_round_nonhit_actual
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (event : (graph setup).EventId)
    (execution next : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (moved : next ∈ ((application setup leaks).round scheduler
      (fun _ => (application setup leaks).silentPolicy) execution).support)
    (absent : sourceServiceTurnInput? setup leaks owner event (next.recall owner) = none) :
    next ∈ ((application setup leaks).round scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      execution).support := by
  let app := application setup leaks
  obtain ⟨command, selected, middle, observed, cases⟩ := round_cases setup leaks moved
  rw [ReactiveApplication.round, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨command, selected, ?_⟩
  rw [ReactiveApplication.dispatch, PMF.support_bind]
  apply Set.mem_iUnion₂.mpr
  refine ⟨middle, observed, ?_⟩
  rcases cases with ⟨inactive, rfl⟩ | ⟨actor, active, response, chosen, rfl⟩
  · simp only [inactive, ReactiveApplication.resume, PMF.mem_support_pure_iff]
  · have commandEq : command = .activate actor := by
      cases command with
      | activate who =>
          exact congrArg ReactiveApplication.Command.activate
            (Option.some.inj active)
      | «include» _ | wait | application _ => cases active
    subst commandEq
    have configEq := activation_application setup leaks execution middle actor observed
    have middleReady : middle.application.config.cut.Ready event := by
      rw [configEq]
      exact ready
    by_cases own : actor = owner
    · subst actor
      have input := sourceServiceTurnInput?_respond owner event middle
        (ownTurn?_of_ready setup middle.application middleReady owned) response
      exact (Option.some_ne_none _ (input.symm.trans absent)).elim
    · have policy := foreign_ready_policy_silent setup leaks bound turns profile middle
        event owner actor middleReady owned own
      simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, PMF.support_map]
      exact ⟨response, policy.symm ▸ chosen, rfl⟩

private theorem firstTurn_ready_after_nonhit_round
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (execution next : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (within : next.environmentRecall.length ≤ horizon)
    (initialized : next ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      next.environmentRecall.length).support)
    (moved : next ∈ ((application setup leaks).round scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      execution).support)
    (absent : sourceServiceTurnInput? setup leaks owner event (next.recall owner) = none) :
    next.application.config.cut.Ready event := by
  rcases round_configStep setup leaks scheduler _ execution next moved with same |
      ⟨target, targetReady, action, stepped⟩
  · rw [same]
    exact ready
  · have targetEq := setup.eventGraph.sequentialize_ready_unique
      execution.application.config.cut targetReady ready
    subst target
    have completed : event ∈ next.application.config.cut.completed := by
      rw [execution.application.config.step_cut event ready action next.application.config
        stepped, EventOrder.Cut.mem_complete]
      exact Or.inl rfl
    exact (sourceServiceFirstTurn_completed_input contract timely _ owner turns profile rfl
      next.environmentRecall.length within next initialized event owned completed absent).elim

/-- Equal complete owner traffic determines the whole actual first-ready-owner
input law through public scheduling. Both executions are actual initialized
prefixes of the same exact first-turn profile. -/
theorem sourceServiceFirstActivation_binding_input_runUntil_congr
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (count : Nat) (left right : (application setup leaks).Execution)
    (within : left.environmentRecall.length + count ≤ horizon)
    (leftInitialized : left ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      left.environmentRecall.length).support)
    (rightInitialized : right ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      right.environmentRecall.length).support)
    (ready : left.application.config.cut.Ready event)
    (same : (runtime setup).bindingTraffic leaks owner left =
      (runtime setup).bindingTraffic leaks owner right) :
    ((application setup leaks).runUntil scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠ none)
      count left).map
        (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner)) =
    ((application setup leaks).runUntil scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠ none)
      count right).map
        (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner)) := by
  classical
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let stop := fun final : app.Execution =>
    sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠ none
  let read := fun final : app.Execution =>
    sourceServiceTurnInput? setup leaks owner event (final.recall owner)
  have owned := binding_actor setup event owner payload outputEq
  induction count generalizing left right with
  | zero =>
      have recalls := congrArg (fun traffic => traffic.2.2.2.1) same
      dsimp only [bindingTraffic] at recalls
      simp only [ReactiveApplication.runUntil, PMF.pure_map, recalls]
  | succ count ih =>
      have recalls := congrArg (fun traffic => traffic.2.2.2.1) same
      have environments := congrArg (fun traffic => traffic.2.2.1) same
      have publics := congrArg (fun traffic => traffic.2.2.2.2.2) same
      dsimp only [bindingTraffic] at recalls environments publics
      have rightReady : right.application.config.cut.Ready event := by
        apply (right.application.publicView_eventReady event).mp
        rw [← publics]
        exact (left.application.publicView_eventReady event).mpr ready
      by_cases hit : stop left
      · have rightHit : stop right := by simpa only [stop, recalls] using hit
        rw [app.runUntil_of_stop scheduler players stop _ left hit,
          app.runUntil_of_stop scheduler players stop _ right rightHit]
        simp only [PMF.pure_map, recalls]
      · have rightRunning : ¬ stop right := by simpa only [stop, ← recalls] using hit
        dsimp only [stop] at hit rightRunning
        simp only [ReactiveApplication.runUntil, hit, rightRunning, ↓reduceIte, PMF.map_bind]
        rw [prehit_round_continuation_silent setup leaks scheduler bound turns profile owner
          event count left ready owned,
          prehit_round_continuation_silent setup leaks scheduler bound turns profile owner
            event count right rightReady owned]
        have rounds := (runtime setup).bindingTraffic_silent_round leaks scheduler owner left
          right same event owner payload outputEq codeEq node (soleReady_of_ready setup _ ready)
        apply bind_eq_of_map_eq _ _ _ _ rounds
        intro nextLeft leftMove nextRight rightMove nextSame
        have nextRecalls := congrArg (fun traffic => traffic.2.2.2.1) nextSame
        dsimp only [bindingTraffic] at nextRecalls
        by_cases nextHit : stop nextLeft
        · have nextRightHit : stop nextRight := by simpa only [stop, nextRecalls] using nextHit
          rw [app.runUntil_of_stop scheduler players stop count nextLeft nextHit,
            app.runUntil_of_stop scheduler players stop count nextRight nextRightHit]
          simp only [PMF.pure_map, nextRecalls]
        · have nextAbsent : read nextLeft = none := by
            simpa only [stop, read, ne_eq, not_not] using nextHit
          have rightAbsent : read nextRight = none := by
            simpa only [read, ← nextRecalls] using nextAbsent
          have leftActual := silent_round_nonhit_actual setup leaks scheduler bound turns
            profile owner event left nextLeft ready owned leftMove nextAbsent
          have rightActual := silent_round_nonhit_actual setup leaks scheduler bound turns
            profile owner event right nextRight rightReady owned rightMove rightAbsent
          have leftLength := app.round_environmentRecall_length scheduler players left nextLeft
            leftActual
          have rightLength := app.round_environmentRecall_length scheduler players right
            nextRight rightActual
          have leftNextInitialized : nextLeft ∈ (app.roundsFrom (initialLaw setup) scheduler
              players nextLeft.environmentRecall.length).support := by
            rw [leftLength, app.roundsFrom_succ, PMF.support_bind]
            exact Set.mem_iUnion₂.mpr ⟨left, leftInitialized, leftActual⟩
          have rightNextInitialized : nextRight ∈ (app.roundsFrom (initialLaw setup) scheduler
              players nextRight.environmentRecall.length).support := by
            rw [rightLength, app.roundsFrom_succ, PMF.support_bind]
            exact Set.mem_iUnion₂.mpr ⟨right, rightInitialized, rightActual⟩
          have nextReady := firstTurn_ready_after_nonhit_round setup leaks contract timely turns
            profile owner event owned left nextLeft ready (by omega) leftNextInitialized
              leftActual nextAbsent
          exact ih nextLeft nextRight (by omega) leftNextInitialized rightNextInitialized
            nextReady nextSame

/-- A genuine prior source-view/full-traffic factorization survives the whole
first-ready-owner input stop. The carrier can retain original and effective
source configurations together. No source marginal or posterior is supplied;
the existing carrier marginal is preserved by actual public scheduling. -/
theorem sourceServiceFirstActivation_binding_input_factorization
    {Seed Source View : Type}
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution)
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        event.val (execution seed))
    (within : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks owner (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra)) :
    ∃ channel : View → PMF (application setup leaks).Info,
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠
            none) horizon (execution seed)).map fun final =>
              (source seed, sourceServiceTurnInput? setup leaks owner event
                (final.recall owner))) =
      (prior.map source).bind fun config =>
        (channel (observe config)).map fun input => (config, input) := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let stop := fun final : app.Execution =>
    sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠ none
  let read := fun final : app.Execution =>
    sourceServiceTurnInput? setup leaks owner event (final.recall owner)
  obtain ⟨channel, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks owner (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit) (fun config _ => config) observe
    (fun seed _ => (app.runUntilHorizon scheduler players stop horizon (execution seed)).map read)
    (fun _ _ _ _ _ _ _ _ same => same)
    (by
      intro left leftSupport _ _ right rightSupport _ _ _ same
      have environments := congrArg (fun traffic => traffic.2.2.1) same
      dsimp only [bindingTraffic] at environments
      unfold ReactiveApplication.runUntilHorizon
      rw [← environments]
      have ready : (execution left).application.config.cut.Ready event :=
        (ready_iff_rank setup _ event.val (boundary left leftSupport).ordered event).mpr rfl
      exact sourceServiceFirstActivation_binding_input_runUntil_congr setup leaks contract
        timely turns profile owner event payload outputEq codeEq node _ (execution left)
        (execution right) (by have bounded := within left leftSupport; omega)
        (boundary left leftSupport).supported (boundary right rightSupport).supported ready same)
  refine ⟨channel, ?_⟩
  simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_id,
    PMF.map_comp, Function.comp_def] using law

/-- The actual whole stopping channel has total mass on real owner inputs.
This is contract completeness applied to initialized prefixes, rather than a
normalization of the input readout or a coverage assumption. -/
theorem sourceServiceFirstActivation_binding_input_total
    {Seed : Type}
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (prior : PMF Seed) (execution : Seed → (application setup leaks).Execution)
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        event.val (execution seed))
    (within : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon) :
    (prior.bind fun seed =>
      ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        (fun final => sourceServiceTurnInput? setup leaks owner event (final.recall owner) ≠ none)
        horizon (execution seed)).map fun final =>
          (sourceServiceTurnInput? setup leaks owner event (final.recall owner)).isSome) =
      PMF.pure true := by
  calc
    _ = prior.bind (fun _ => PMF.pure true) := by
      apply bind_congr_on_support _
      intro seed supported
      exact sourceServiceFirstActivation_input_isSome_law contract timely _ owner turns profile
        rfl (execution seed) (within seed supported) (boundary seed supported).supported event
          owned
    _ = _ := PMF.bind_const _ _

end Vegas
