/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSampleCompletion
import Vegas.Pending.ReactiveSamplePhase

/-! # The actual stopped public-sample channel

Silent sample rounds couple the complete focal traffic, and that readout
determines the public stopping test and actual remaining horizon. The sampled
value is read from the same public channel. These laws concern the actual
stopped execution; no sample-time, endpoint or posterior law is postulated.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem sample_completed_of_traffic_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (event : (graph setup).EventId)
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    event ∈ left.application.config.cut.completed ↔
      event ∈ right.application.config.cut.completed := by
  have publics := congrArg (fun read => read.2.2.2.2.2) same
  dsimp only [bindingTraffic] at publics
  rw [← left.application.config.history_exact event, ← right.application.config.history_exact event]
  change event ∈ left.application.publicView.observation.completionOrder ↔
    event ∈ right.application.publicView.observation.completionOrder
  rw [publics]

/-- Equal actual traffic is retained through the public sample's completion
stop, including exhaustion of any finite budget. -/
theorem source_sample_silent_runUntil
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    {left right : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty) (law : EventGraph.PublicDist (graph setup).layout payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload law)
    (node : nodeView (graph setup) event = .sample payload law outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) (count : Nat) :
    ((application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count left).map
          ((runtime setup).bindingTraffic leaks focal) =
      ((application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((runtime setup).bindingTraffic leaks focal) := by
  let app := application setup leaks
  induction count generalizing left right with
  | zero =>
      simpa only [ReactiveApplication.runUntil, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      have leftRunning : event ∉ left.application.config.cut.completed := ready.1
      have rightRunning : event ∉ right.application.config.cut.completed := by
        intro finished
        exact leftRunning ((sample_completed_of_traffic_eq setup leaks focal event same).mpr
          finished)
      have rounds := (runtime setup).bindingTraffic_sample_silent_round leaks scheduler focal
        left right same event payload law outputEq codeEq node
          (soleReady_of_ready setup _ ready)
      simp only [ReactiveApplication.runUntil, leftRunning, rightRunning, ↓reduceIte,
        PMF.map_bind]
      apply bind_eq_of_map_eq _ _ _ _ rounds
      intro nextLeft leftMove nextRight _rightMove nextSame
      by_cases finished : event ∈ nextLeft.application.config.cut.completed
      · have rightFinished :=
          (sample_completed_of_traffic_eq setup leaks focal event nextSame).mp finished
        rw [app.runUntil_of_stop scheduler _ _ count nextLeft finished,
          app.runUntil_of_stop scheduler _ _ count nextRight rightFinished]
        simpa only [PMF.pure_map] using congrArg PMF.pure nextSame
      · apply ih _ nextSame
        rcases round_configStep setup leaks scheduler _ left nextLeft leftMove with
          unchanged | ⟨target, targetReady, action, supported⟩
        · rw [unchanged]
          exact ready
        · rw [left.application.config.step_cut target targetReady action
            nextLeft.application.config supported] at finished ⊢
          apply ready.after_complete targetReady
          intro equal
          exact finished ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl equal))

/-- The public scheduler recall in the retained traffic fixes the actual
remaining horizon, so no external time or remaining-budget equality is needed. -/
theorem source_sample_silent_runUntilHorizon
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    {left right : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty) (law : EventGraph.PublicDist (graph setup).layout payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload law)
    (node : nodeView (graph setup) event = .sample payload law outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ((application setup leaks).runUntilHorizon scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon left).map
          ((runtime setup).bindingTraffic leaks focal) =
      ((application setup leaks).runUntilHorizon scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) horizon right).map
          ((runtime setup).bindingTraffic leaks focal) := by
  have recalled := congrArg (fun read => read.2.2.1) same
  dsimp only [bindingTraffic] at recalled
  unfold ReactiveApplication.runUntilHorizon
  rw [← recalled]
  exact source_sample_silent_runUntil setup leaks scheduler ready payload law outputEq codeEq
    node focal same _

private theorem sample_value_of_traffic_eq
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    {left right : (application setup leaks).Execution}
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout (.publicData payload)).get?
        left.application.config.store =
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout (.publicData payload)).get?
        right.application.config.store := by
  have publics := congrArg (fun read => read.2.2.2.2.2.observation.store) same
  dsimp only [bindingTraffic, State.publicView] at publics
  have fields := congrFun publics (.inr event)
  change (graph setup).publicStore left.application.config.store (.inr event) =
    (graph setup).publicStore right.application.config.store (.inr event) at fields
  have visible : (graph setup).fieldPublic (.inr event) := by
    change ((graph setup).outputLayout event).IsPublic
    rw [outputEq]
    trivial
  rw [(graph setup).publicStore_of_public left.application.config.store _ visible,
    (graph setup).publicStore_of_public right.application.config.store _ visible] at fields
  exact congrArg (cast (congrArg Option (congrArg EventGraph.EventField.Value outputEq))) fields

/-- The prescribed stopped sample channel retains its actual public value
jointly with the same complete traffic sample. -/
theorem sourceServiceTurnPolicy_sample_value_traffic_congr
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    {left right : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty) (law : EventGraph.PublicDist (graph setup).layout payload)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload law)
    (node : nodeView (graph setup) event = .sample payload law outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    let output : EventGraph.FieldRef (graph setup).layout (.publicData payload) :=
      ⟨.inr event, outputEq⟩
    ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon left).map
          (fun final => (output.get? final.application.config.store,
            (runtime setup).bindingTraffic leaks focal final)) =
      ((application setup leaks).runUntilHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) horizon right).map
          (fun final => (output.get? final.application.config.store,
            (runtime setup).bindingTraffic leaks focal final)) := by
  intro output
  have rightReady : right.application.config.cut.Ready event := by
    have publics := congrArg (fun read => read.2.2.2.2.2) same
    dsimp only [bindingTraffic] at publics
    rw [← State.publicView_eventReady, ← publics, State.publicView_eventReady]
    exact ready
  rw [sourceServiceTurnPolicy_sample_runUntilHorizon setup leaks scheduler bound turns timing
      profile horizon left event ready (nodeView_sample_actor outputEq codeEq),
    sourceServiceTurnPolicy_sample_runUntilHorizon setup leaks scheduler bound turns timing
      profile horizon right event rightReady (nodeView_sample_actor outputEq codeEq)]
  have stopped := source_sample_silent_runUntilHorizon setup leaks scheduler horizon ready payload
    law outputEq codeEq node focal same
  rw [← PMF.bind_pure_comp, Function.comp_def, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_eq_of_map_eq _ _ _ _ stopped
  intro finalLeft _ finalRight _ traffic
  exact congrArg PMF.pure (Prod.ext
    (sample_value_of_traffic_eq setup leaks focal event payload outputEq traffic) traffic)

end Vegas
