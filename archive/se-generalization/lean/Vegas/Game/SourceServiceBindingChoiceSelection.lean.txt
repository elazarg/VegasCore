/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelection
import Vegas.Game.SourceServiceRecordedBindingCompletion

/-! # Canonical binding draws and actual public selection

A canonical packet's typed private value does not affect the actual public
selection or any foreign player's input. Sampling that value therefore joins
the same physical stopped selection kernel, retaining the correlated prefix
parameter. The reference kernel submits failure only as a physical proof
experiment; it need not be an admitted source choice. The aligned-source
specialization uses the residual source commitment policy itself.

The manual first call may be unprotected. Its subsequent owner continuation
follows the recorded turn policy. Completion and uniqueness are separate from
this probability law, which also includes finite-budget exhaustion.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The sampled value and actual stopped selection are conditionally independent
given the same physical prefix. The initial parameter remains in that draw. -/
theorem sourceService_binding_choice_selection
    {Seed Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (horizon : Nat) (prior : PMF Seed) (parameter : Seed → Parameter)
    (execution : Seed → (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (draw : Seed → PMF (PublicationResult (L.Val payload))) (serial : Seed → Nat) :
    (prior.bind fun seed => (draw seed).bind fun value =>
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        ((execution seed).respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload value (serial seed)))).map
        fun final => (parameter seed, value,
          (runtime setup).bindingPublicTraffic leaks owner final)) =
    (prior.bind fun seed =>
      (((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        ((execution seed).respond (application setup leaks) owner
          ((runtime setup).reactiveBinding leaks owner event payload .failure
            (serial seed)))).map ((runtime setup).bindingPublicTraffic leaks owner)).bind
        fun traffic => (draw seed).map fun value => (parameter seed, value, traffic)) := by
  apply bind_congr_on_support prior
  intro seed supported
  calc
    _ = (draw seed).bind (fun value =>
        (((application setup leaks).runUntilHorizon scheduler players
          (fun final => event ∈ final.application.config.cut.completed) horizon
          ((execution seed).respond (application setup leaks) owner
            ((runtime setup).reactiveBinding leaks owner event payload .failure
              (serial seed)))).map ((runtime setup).bindingPublicTraffic leaks owner)).map
                fun traffic => (parameter seed, value, traffic)) := by
      apply bind_congr_on_support (draw seed)
      intro value _selected
      have law := sourceService_binding_selection_independent setup leaks scheduler players bound
        turns timing profile owner follows horizon (execution seed) event (ready seed supported)
        payload outputEq codeEq node value .failure (serial seed)
      simpa only [PMF.map_comp, Function.comp_def] using
        congrArg (fun law => law.map (fun traffic => (parameter seed, value, traffic))) law
    _ = _ := by
      exact PMF.bind_comm (draw seed) _
        (fun value traffic => PMF.pure (parameter seed, value, traffic))

/-- At an actual aligned binding prefix, the draw is exactly the residual
source commitment kernel. The physical continuation uses the same parameter
and public selection kernel for every supported source value. -/
theorem BindingSource.choice_selection
    {Parameter : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (horizon : Nat) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (site : BindingSource setup profile event execution.application.config)
    (follows : players site.owner =
      sourceServiceTurnPolicy setup leaks bound turns timing profile site.owner)
    (parameter : Parameter) (serial : Nat) :
    ((commitKernel site.residual (site.source.view site.owner)).bind fun value =>
      ((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution.respond (application setup leaks) site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload value serial))).map
        fun final => (parameter, value,
          (runtime setup).bindingPublicTraffic leaks site.owner final)) =
    ((((application setup leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon
        (execution.respond (application setup leaks) site.owner
          ((runtime setup).reactiveBinding leaks site.owner event site.payload .failure
            serial))).map ((runtime setup).bindingPublicTraffic leaks site.owner)).bind
      fun traffic => (commitKernel site.residual (site.source.view site.owner)).map
        fun value => (parameter, value, traffic)) := by
  simpa only [PMF.pure_bind] using sourceService_binding_choice_selection setup leaks scheduler
    players bound turns timing profile site.owner follows horizon (PMF.pure ())
    (fun _ => parameter) (fun _ => execution) event (fun _ _ => ready) site.payload
    site.outputEq site.code (nodeView_eq_bind site.outputEq site.code)
    (fun _ => commitKernel site.residual (site.source.view site.owner)) (fun _ => serial)

end Vegas
