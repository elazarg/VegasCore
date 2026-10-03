/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceStoppedResolutionTraffic

/-! # Prescribed resolution traffic after an actual decision

Once the owner has recorded a response for the current ready event, every
member of its timing family is silent. The actual posterior mixture is therefore
silent too, and other players have no ready turn. Only activation queries a
response, and activation preserves the application and prior recall.

The whole prescribed completion-stopped execution law consequently equals the
all-silent law, for every timing and source profile. Composing the actual traffic
coupling retains earlier deferrals and the complete source-conditioned channel.
Source alignment and protected completion remain separate obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem recorded_turn_input_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (who : Player) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who (execution.recall who)
        (execution.observe (application setup leaks) who) =
      (application setup leaks).silentPolicy (execution.recall who)
        (execution.observe (application setup leaks) who) := by
  let app := application setup leaks
  have sole := soleReady_of_ready setup execution.application ready
  by_cases own : who = owner
  · subst who
    have turn := PublicView.ownTurn?_of_ownTurn execution.application.publicView owner event
      (sole.ownTurn owned)
    rw [sourceServiceTurnPolicy_turn setup leaks bound turns timing profile owner _ _ event
      owned turn, app.policyMixture_policy]
    have family (slot : Fin (turns + 1)) :
        sourceServiceTurnFamily setup leaks bound profile owner event turns slot
          (execution.recall owner) (execution.observe app owner) =
        app.silentPolicy (execution.recall owner) (execution.observe app owner) := by
      simp only [sourceServiceTurnFamily, ReactiveApplication.turnScheduledPolicy]
      split
      · simp only [sourceServiceCanonicalOpportunity, recorded, ↓reduceIte]
        rfl
      · rfl
    dsimp only [app] at family
    simp only [family, PMF.bind_const]
  · apply sourceServiceTurnPolicy_idle setup leaks bound turns timing profile who _ _
    apply sole.idle
    rw [owned]
    intro equal
    exact own (Option.some.inj equal).symm

private theorem recorded_activation_input_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    {execution middle : (application setup leaks).Execution} {owner : Player}
    {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (command : (application setup leaks).Command)
    (moved : middle ∈ (execution.environmentStep (application setup leaks) command).support)
    (who : Player) (active : command.actor? (application setup leaks) = some who) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who (middle.recall who)
        (middle.observe (application setup leaks) who) =
      (application setup leaks).silentPolicy (middle.recall who)
        (middle.observe (application setup leaks) who) := by
  cases command with
  | activate actor =>
      have applicationEq := activation_application setup leaks execution middle actor moved
      have recallEq := (application setup leaks).environmentStep_recall execution middle
        (.activate actor) moved
      exact recorded_turn_input_silent setup leaks bound turns timing profile middle owner event
        (by rw [applicationEq]; exact ready) owned (by rw [recallEq]; exact recorded) who
  | «include» _ => cases active
  | application _ => cases active
  | wait => cases active

/-- Every actual response queried by the next prescribed round is silent
after the current ready event's owner has recorded its decision. The equality
retains the entire physical execution, not just the traffic readout. -/
theorem sourceServiceTurnPolicy_round_of_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true) :
    (application setup leaks).round scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) execution =
      (application setup leaks).round scheduler
        (fun _ => (application setup leaks).silentPolicy) execution := by
  let app := application setup leaks
  simp only [ReactiveApplication.round, ReactiveApplication.dispatch]
  apply bind_congr_on_support _
  intro command _
  apply bind_congr_on_support _
  intro middle moved
  cases actor : command.actor? app with
  | none => rfl
  | some who =>
      have policy := recorded_activation_input_silent setup leaks bound turns timing profile
        ready owned recorded command moved who actor
      simp only [ReactiveApplication.resume, ReactiveApplication.invoke, policy]

/-- A policy silent at every input while this ready decision is recorded has
the exact all-silent completion-stopped execution law. Actual configuration
progress and persistence of the owner's recorded call supply the invariant. -/
theorem sourceServicePolicy_runUntil_of_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (count : Nat)
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (silent : ∀ current : (application setup leaks).Execution,
      current.application.config.cut.Ready event →
      (runtime setup).eventRecorded leaks (current.recall owner) event = true →
      ∀ who, players who (current.recall who) (current.observe (application setup leaks) who) =
        (application setup leaks).silentPolicy (current.recall who)
          (current.observe (application setup leaks) who)) :
    (application setup leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := application setup leaks
  let invariant := fun current : app.Execution =>
    (current.application.config.cut.Ready event ∨
      event ∈ current.application.config.cut.completed) ∧
      (runtime setup).eventRecorded leaks (current.recall owner) event = true
  have readyOf (current : app.Execution) (holds : invariant current)
      (running : event ∉ current.application.config.cut.completed) :
      current.application.config.cut.Ready event := holds.1.resolve_right running
  apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
  · intro current holds running command _ middle moved who active
    cases command with
    | activate actor =>
        have applicationEq := activation_application setup leaks current middle actor moved
        have recallEq := app.environmentStep_recall current middle (.activate actor) moved
        exact silent middle (by rw [applicationEq]; exact readyOf current holds running)
          (by rw [recallEq]; exact holds.2) who
    | «include» _ | application _ | wait => cases active
  · intro current holds running next reached
    have currentReady := readyOf current holds running
    refine ⟨?_, ?_⟩
    · rcases round_configStep setup leaks scheduler _ current next reached with
        same | ⟨target, targetReady, action, supported⟩
      · rw [same]
        exact Or.inl currentReady
      · rw [current.application.config.step_cut target targetReady action next.application.config
          supported]
        by_cases equal : event = target
        · exact Or.inr ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl equal))
        · exact Or.inl (currentReady.after_complete targetReady equal)
    · obtain ⟨command, _, middle, moved, cases⟩ := round_cases setup leaks reached
      have middleRecorded : (runtime setup).eventRecorded leaks (middle.recall owner) event =
          true := by
        rw [app.environmentStep_recall current middle command moved]
        exact holds.2
      rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
      · exact middleRecorded
      · exact (runtime setup).eventRecorded_respond_of_recorded leaks middle responder owner
          response event middleRecorded
  · exact ⟨Or.inl ready, recorded⟩

/-- The prescribed policy and all-silent policy have the same whole execution
law stopped at this recorded event's completion, including horizon exhaustion. -/
theorem sourceServiceTurnPolicy_runUntilHorizon_of_recorded
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (horizon : Nat)
    (execution : (application setup leaks).Execution) (owner : Player)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true) :
    (application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution =
      (application setup leaks).runUntilHorizon scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  unfold ReactiveApplication.runUntilHorizon
  exact sourceServicePolicy_runUntil_of_recorded setup leaks scheduler _ _ execution owner
    event ready recorded (fun current currentReady currentRecorded who =>
      recorded_turn_input_silent setup leaks bound turns timing profile current owner event
        currentReady owned currentRecorded who)

/-- The actual prescribed turn policy preserves an existing source-conditioned
full traffic channel after its current resolution has been recorded, for any
timing. The carrier remains unchanged until this stopping point. -/
theorem sourceServiceTurnPolicy_recorded_resolution_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (focal : Player) (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution) (remaining : Seed → Nat)
    (event : (graph setup).EventId) (owner : Player)
    (trace : ∀ seed ∈ prior.support,
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining seed, none, execution seed⟩))
    (conform : ∀ seed ∈ prior.support, FreshCallsConform setup leaks (execution seed) owner)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (recorded : ∀ seed ∈ prior.support,
      (runtime setup).eventRecorded leaks ((execution seed).recall owner) event = true)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra)) :
    ∃ nextNoise : View → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns timing profile)
          (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final =>
              (source seed, (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (observe config)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, law⟩ := source_async_stopped_resolution_factorization setup leaks scheduler
    horizon focal prior source observe execution remaining event owner trace conform ready payload
    binding checks outputEq codeEq node noise factor
  refine ⟨nextNoise, ?_⟩
  calc
    _ = (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler
          (fun _ => (application setup leaks).silentPolicy)
          (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final =>
              (source seed, (runtime setup).bindingTraffic leaks focal final)) := by
      apply bind_congr_on_support _
      intro seed supported
      rw [sourceServiceTurnPolicy_runUntilHorizon_of_recorded setup leaks scheduler bound turns
        timing profile horizon (execution seed) owner event (ready seed supported)
        (nodeView_resolve_actor outputEq codeEq) (recorded seed supported)]
    _ = _ := law

end Vegas
