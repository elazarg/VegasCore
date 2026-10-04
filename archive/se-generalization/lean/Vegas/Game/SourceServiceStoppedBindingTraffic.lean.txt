/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncFactorization
import Vegas.Game.SourceServiceReachedDecoding
import Vegas.Game.SourceServiceRecordedResolutionTraffic
import Interaction.ReactiveStopping

/-! # Binding traffic through actual completion stopping

The silent binding-round law iterates until the current event completes or the
actual round budget is exhausted. The complete traffic readout determines both
the public completion test and the remaining horizon. No packet conformance,
calendar position or private-value-independent scheduling premise is needed.

The carried source is unchanged by this traffic law. Protected completion and
agreement with the source successor require their own proofs.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem completed_of_traffic_eq
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

private theorem ready_after_unfinished_round
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    {execution next : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event)
    (reached : next ∈ ((application setup leaks).round scheduler
      (fun _ => (application setup leaks).silentPolicy) execution).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    next.application.config.cut.Ready event := by
  rcases round_configStep setup leaks scheduler _ execution next reached with
    same | ⟨target, targetReady, action, supported⟩
  · rw [same]
    exact ready
  · rw [execution.application.config.step_cut target targetReady action
      next.application.config supported] at unfinished ⊢
    apply ready.after_complete targetReady
    intro equal
    exact unfinished ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl equal))

/-- Equal full traffic gives equal silent traffic through the actual public
completion stop, including expiry and exhaustion of the finite budget. -/
theorem source_binding_silent_runUntil
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    {left right : (application setup leaks).Execution}
    {event : (graph setup).EventId}
    (ready : left.application.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right)
    (count : Nat) :
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
        exact leftRunning ((completed_of_traffic_eq setup leaks focal event same).mpr finished)
      have rounds := (runtime setup).bindingTraffic_silent_round leaks scheduler focal left right
        same event owner payload outputEq codeEq node (soleReady_of_ready setup _ ready)
      simp only [ReactiveApplication.runUntil, leftRunning, rightRunning, ↓reduceIte,
        PMF.map_bind]
      apply bind_eq_of_map_eq _ _ _ _ rounds
      intro nextLeft leftMove nextRight _rightMove nextSame
      by_cases finished : event ∈ nextLeft.application.config.cut.completed
      · have rightFinished := (completed_of_traffic_eq setup leaks focal event nextSame).mp finished
        rw [app.runUntil_of_stop scheduler _ _ count nextLeft finished,
          app.runUntil_of_stop scheduler _ _ count nextRight rightFinished]
        simpa only [PMF.pure_map] using congrArg PMF.pure nextSame
      · exact ih (ready_after_unfinished_round setup leaks scheduler ready leftMove finished)
          nextSame

/-- The actual remaining horizon is determined by the retained scheduler recall. -/
theorem source_binding_silent_runUntilHorizon
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    {left right : (application setup leaks).Execution}
    {event : (graph setup).EventId}
    (ready : left.application.config.cut.Ready event)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
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
  exact source_binding_silent_runUntil setup leaks scheduler ready owner payload outputEq codeEq
    node focal same _

/-- Existing source-conditioned traffic factorization survives the actual
completion-stopped silent binding kernel. The carried source is retained. -/
theorem source_async_stopped_binding_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (focal : Player) (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra)) :
    ∃ nextNoise : View → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).runUntilHorizon scheduler
          (fun _ => (application setup leaks).silentPolicy)
          (fun final => event ∈ final.application.config.cut.completed) horizon
            (execution seed)).map fun final =>
              (source seed, (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (observe config)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit) (fun config _ => config) observe
    (fun seed _ => ((application setup leaks).runUntilHorizon scheduler
      (fun _ => (application setup leaks).silentPolicy)
      (fun final => event ∈ final.application.config.cut.completed) horizon (execution seed)).map
        ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (by
      intro left leftSupport _ _ right _rightSupport _ _ _ same
      exact source_binding_silent_runUntilHorizon setup leaks scheduler horizon
        (ready left leftSupport) owner payload outputEq codeEq node focal same)
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_id,
    PMF.map_comp, Function.comp_def] using law

/-- After the binding is recorded, the actual policy preserves the carried
source-conditioned traffic law for every timing through completion stopping. -/
theorem sourceServiceTurnPolicy_recorded_binding_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (focal : Player) (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (recorded : ∀ seed ∈ prior.support,
      (runtime setup).eventRecorded leaks ((execution seed).recall owner) event = true)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
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
  obtain ⟨nextNoise, law⟩ := source_async_stopped_binding_factorization setup leaks scheduler
    horizon focal prior source observe execution event owner payload ready outputEq codeEq node
    noise factor
  have owned := binding_actor setup event owner payload outputEq
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
        timing profile horizon (execution seed) owner event (ready seed supported) owned
        (recorded seed supported)]
    _ = _ := law

end Vegas
