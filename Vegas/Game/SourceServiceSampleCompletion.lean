/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnCompletes
import Vegas.Game.SourceServiceSampleEnvironmentFactorization

/-! # Actual public sampling through completion stopping

At a ready chance event every player is idle, so the prescribed turn policy
has the same whole stopped execution law as silence, for every timing. The
actual completion boundary and complete-play contract ensure that the stopped
configuration has the exact public sample law. Neither a sample time nor a
source posterior is supplied.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem sample_activation_input_silent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    {execution middle : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none)
    (command : (application setup leaks).Command)
    (moved : middle ∈ (execution.environmentStep (application setup leaks) command).support)
    (who : Player) (active : command.actor? (application setup leaks) = some who) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who (middle.recall who)
        (middle.observe (application setup leaks) who) =
      (application setup leaks).silentPolicy (middle.recall who)
        (middle.observe (application setup leaks) who) := by
  cases command with
  | activate actor =>
      have same := activation_application setup leaks execution middle actor moved
      have current : middle.application.config.cut.Ready event := by rw [same]; exact ready
      apply sourceServiceTurnPolicy_idle setup leaks bound turns timing profile who _ _
      exact (soleReady_of_ready setup middle.application current).idle (by
        rw [actorless]
        intro impossible
        cases impossible)
  | «include» _ => cases active
  | application _ => cases active
  | wait => cases active

/-- At a ready chance event every actual activation asks for silence. The
whole next-round law retains the network, all recalls, and application state. -/
theorem sourceServiceTurnPolicy_sample_round
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none) :
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
  cases active : command.actor? app with
  | none => rfl
  | some who =>
      have law := sample_activation_input_silent setup leaks bound turns timing profile
        ready actorless command moved who active
      simp only [ReactiveApplication.resume, ReactiveApplication.invoke, law]

/-- The actual prescribed policy and silence have the same whole execution
law until this ready chance event completes, including horizon exhaustion. -/
theorem sourceServiceTurnPolicy_sample_runUntilHorizon
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (horizon : Nat)
    (execution : (application setup leaks).Execution) (event : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready event)
    (actorless : (graph setup).actor? event = none) :
    (application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution =
      (application setup leaks).runUntilHorizon scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  let app := application setup leaks
  let invariant := fun current : app.Execution =>
    current.application.config.cut.Ready event ∨ event ∈ current.application.config.cut.completed
  have readyOf (current : app.Execution) (holds : invariant current)
      (running : event ∉ current.application.config.cut.completed) :
      current.application.config.cut.Ready event := holds.resolve_right running
  unfold ReactiveApplication.runUntilHorizon
  apply app.runUntil_congr_of_agree scheduler _ _ _ invariant
  · intro current holds running command _ middle moved who active
    exact sample_activation_input_silent setup leaks bound turns timing profile
      (readyOf current holds running) actorless command moved who active
  · intro current holds running next reached
    have currentReady := readyOf current holds running
    change next.application.config.cut.Ready event ∨
      event ∈ next.application.config.cut.completed
    rcases round_configStep setup leaks scheduler _ current next reached with
      same | ⟨target, targetReady, action, supported⟩
    · rw [same]
      exact Or.inl currentReady
    · rw [current.application.config.step_cut target targetReady action next.application.config
        supported]
      by_cases equal : event = target
      · exact Or.inr ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl equal))
      · exact Or.inl (currentReady.after_complete targetReady equal)
  · exact Or.inl ready

/-- Complete play discharges the stopping premise of the actual chance law.
No opportunity, disclosure-effectiveness, or policy coverage premise is used. -/
theorem sourceServiceTurnPolicy_sample_config_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile) event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (actorless : (graph setup).actor? event = none)
    (action : (graph setup).Action event) :
    ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).map
          (fun final => final.application.config) =
      execution.application.config.step event
        ((ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl) action := by
  let app := application setup leaks
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler
    (sourceServiceTurnPolicy setup leaks bound turns timing profile) _ bounded execution
    boundary.supported
  exact sample_runUntil scheduler _ event actorless execution.application.config event.val
    boundary.ordered _ action _ execution rfl (fun final supported =>
      runUntilHorizon_completes contract.completes bounded trace final supported)

/-- The sampled value and complete typed endpoint have their real source
chance law, jointly. The value is read from the actual completed field. -/
theorem sourceServiceTurnPolicy_sample_value_config_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile) event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (agree : refs.Agrees source.state execution.application.config.store)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs law)) :
    let ready := (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
    let output : EventGraph.FieldRef (graph setup).layout (.publicData payload) :=
      ⟨.inr event, outputEq⟩
    ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).map
          (fun final => (output.get? final.application.config.store, final.application.config)) =
      (L.evalDist law (sourcePublicEnv source.state)).map fun value =>
        (some value, execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) := by
  intro ready output
  have actual := sourceServiceTurnPolicy_sample_config_law setup leaks contract turns timing
    profile event execution boundary bounded (nodeView_sample_actor outputEq codeEq)
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
  have sampled := sample_step execution.application.config event ready outputEq refs law codeEq
    source.state agree
  rw [sampled] at actual
  have read := congrArg (PMF.map fun config => (output.get? config.store, config)) actual
  rw [PMF.map_comp, PMF.map_comp] at read
  calc
    _ = (L.evalDist law (sourcePublicEnv source.state)).map fun value =>
        (output.get? (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)).store,
          execution.application.config.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)) := read
    _ = _ := by
      apply map_congr_on_support _
      intro value _
      refine Prod.ext ?_ rfl
      rw [EventGraph.store_complete]
      simp only [output, EventGraph.FieldRef.get?, Function.update_self]
      have castSome {A B : Type} (same : A = B) (value : A) :
          cast (congrArg Option same) (some value) = some (cast same value) := by
        cases same
        rfl
      rw [castSome (congrArg EventGraph.EventField.Value outputEq)]
      have castInverse {A B : Type} (same : A = B) (value : B) :
          cast same (cast same.symm value) = value := by
        cases same
        rfl
      exact congrArg some (castInverse (congrArg EventGraph.EventField.Value outputEq) _)

end Vegas
