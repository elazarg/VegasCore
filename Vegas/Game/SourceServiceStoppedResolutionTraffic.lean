/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionPhaseTraffic
import Interaction.ReactiveStopping

/-! # Actual resolution traffic stopped at completion

All-silent rounds couple the complete focal traffic channel until the current
resolution completes or the actual remaining round budget is spent. The stop
test is public. Initialized traces, packet conformance and actual configuration
progress supply the next round's hypotheses, including after prior deferrals.
Expiry is included in the traffic law; source alignment and protected completion
remain separate conclusions.
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
    (players : Player → (application setup leaks).Policy)
    {execution next : (application setup leaks).Execution} {event : (graph setup).EventId}
    (ready : execution.application.config.cut.Ready event)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (unfinished : event ∉ next.application.config.cut.completed) :
    next.application.config.cut.Ready event := by
  rcases round_configStep setup leaks scheduler players execution next reached with
    same | ⟨target, targetReady, action, supported⟩
  · rw [same]
    exact ready
  · rw [execution.application.config.step_cut target targetReady action
      next.application.config supported] at unfinished ⊢
    apply ready.after_complete targetReady
    intro equal
    exact unfinished ((EventOrder.Cut.mem_complete _ _ _ _).mpr (Or.inl equal))

/-- Equal complete focal traffic gives equal actual completion-stopped traffic
laws. Each side's initialized raw trace supplies enough remaining rounds;
only the left owner's prior packets must conform. -/
theorem source_resolution_conforming_silent_runUntil
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {left right : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId}
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, none, left⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, none, right⟩))
    (conform : FreshCallsConform setup leaks left owner)
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
    (focal : Player)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right)
    (count : Nat) (leftBudget : count ≤ leftRemaining) (rightBudget : count ≤ rightRemaining) :
    ((application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count left).map
          ((runtime setup).bindingTraffic leaks focal) =
      ((application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((runtime setup).bindingTraffic leaks focal) := by
  let app := application setup leaks
  induction count generalizing left right leftRemaining rightRemaining with
  | zero =>
      simpa only [ReactiveApplication.runUntil, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      cases leftRemaining with
      | zero => omega
      | succ leftRemaining =>
          cases rightRemaining with
          | zero => omega
          | succ rightRemaining =>
              have leftRunning : event ∉ left.application.config.cut.completed := ready.1
              have rightRunning : event ∉ right.application.config.cut.completed := by
                intro finished
                exact leftRunning ((completed_of_traffic_eq setup leaks focal event same).mpr
                  finished)
              have rounds := source_resolution_conforming_silent_round setup leaks leftTrace
                rightTrace conform ready payload binding checks outputEq codeEq node focal same
              simp only [ReactiveApplication.runUntil, leftRunning, rightRunning, ↓reduceIte,
                PMF.map_bind]
              apply bind_eq_of_map_eq _ _ _ _ rounds
              intro nextLeft leftMove nextRight rightMove nextSame
              have stopped := completed_of_traffic_eq setup leaks focal event nextSame
              by_cases finished : event ∈ nextLeft.application.config.cut.completed
              · have rightFinished := stopped.mp finished
                rw [app.runUntil_of_stop scheduler _ _ count nextLeft finished,
                  app.runUntil_of_stop scheduler _ _ count nextRight rightFinished]
                simpa only [PMF.pure_map] using congrArg PMF.pure nextSame
              · obtain ⟨nextLeftTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler
                  (fun _ => app.silentPolicy) leftRemaining left nextLeft leftTrace leftMove
                obtain ⟨nextRightTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler
                  (fun _ => app.silentPolicy) rightRemaining right nextRight rightTrace rightMove
                exact ih nextLeftTrace nextRightTrace
                  (freshCallsConform_silent_round setup leaks scheduler owner conform leftMove)
                  (ready_after_unfinished_round setup leaks scheduler _ ready leftMove finished)
                  nextSame (by omega) (by omega)

/-- The actual initialized horizon supplies the round budgets, and equal
scheduler recall gives the same remaining count on both sides. -/
theorem source_resolution_conforming_silent_runUntilHorizon
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {left right : (application setup leaks).Execution}
    {owner : Player} {event : (graph setup).EventId}
    (leftTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨leftRemaining, none, left⟩))
    (rightTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨rightRemaining, none, right⟩))
    (conform : FreshCallsConform setup leaks left owner)
    (ready : left.application.config.cut.Ready event)
    (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq)
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
  have leftAccounted := (application setup leaks).raw_trace_accounted (initialLaw setup)
    horizon scheduler leftTrace
  have rightAccounted := (application setup leaks).raw_trace_accounted (initialLaw setup)
    horizon scheduler rightTrace
  have recalled := congrArg (fun read => read.2.2.1) same
  dsimp only [bindingTraffic] at recalled
  have countEq : horizon - left.environmentRecall.length =
      horizon - right.environmentRecall.length := by rw [recalled]
  unfold ReactiveApplication.runUntilHorizon
  rw [← countEq]
  exact source_resolution_conforming_silent_runUntil setup leaks leftTrace rightTrace conform ready
    payload binding checks outputEq codeEq node focal same _ (by dsimp at leftAccounted; omega)
    (by dsimp at leftAccounted rightAccounted; have := congrArg List.length recalled; omega)

/-- An existing source-conditioned full traffic channel is preserved by the
actual completion-stopped silent kernel. The carrier is unchanged; no source
successor or guaranteed completion is asserted. -/
theorem source_async_stopped_resolution_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler) (horizon : Nat)
    (focal : Player) (prior : PMF Seed) (source : Seed → Source) (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution) (remaining : Seed → Nat)
    (event : (graph setup).EventId) (owner : Player)
    (trace : ∀ seed ∈ prior.support,
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining seed, none, execution seed⟩))
    (conform : ∀ seed ∈ prior.support, FreshCallsConform setup leaks (execution seed) owner)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
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
      intro left leftSupport _ _ right rightSupport _ _ _ same
      exact source_resolution_conforming_silent_runUntilHorizon setup leaks (trace left leftSupport)
        (trace right rightSupport) (conform left leftSupport) (ready left leftSupport)
        payload binding checks outputEq codeEq node focal same)
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure, PMF.map_id,
    PMF.map_comp, Function.comp_def] using law

end Vegas
