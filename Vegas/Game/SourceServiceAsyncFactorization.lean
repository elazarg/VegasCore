/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFactorization
import Vegas.Pending.ReactiveBindingAsyncLikelihood

/-! # Conditional binding traffic for a public asynchronous scheduler

An existing joint source-view/traffic factorization survives an actual silent
round while the current source binding is ready. The round uses the supplied
public scheduler, including its full command recall; no calendar position or
hidden-value-independent grant probability is assumed separately.

The carried source data can retain both original intentions and effective
configurations. They are unchanged by this proof readout; completion-successor
and decision kernels remain separate obligations. The conditional-posterior
result concerns this carried source data at supported observations, rather
than an equilibrium assessment at every native information site.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Public scheduler commands and passive samples preserve conditional traffic
noise during a source binding's silent round, including expiry and inclusion. -/
theorem source_async_silent_binding_factorization
    {Seed Source View : Type}
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (scheduler : (application setup leaks).Scheduler)
    (focal : Player) (prior : PMF Seed) (source : Seed → Source)
    (observe : Source → View)
    (execution : Seed → (application setup leaks).Execution)
    (noise : View → PMF _)
    (factor : prior.map (fun seed => (source seed,
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map source).bind fun config =>
        (noise (observe config)).map fun extra => (config, extra))
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event) :
    ∃ nextNoise : View → PMF _,
      (prior.bind fun seed =>
        ((application setup leaks).round scheduler
          (fun _ => (application setup leaks).silentPolicy) (execution seed)).map fun final =>
            (source seed, (runtime setup).bindingTraffic leaks focal final)) =
      (prior.map source).bind fun config =>
        (nextNoise (observe config)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior source
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    observe noise factor (fun _ => PMF.pure Unit.unit) (fun config _ => config) observe
    (fun seed _ => ((application setup leaks).round scheduler
      (fun _ => (application setup leaks).silentPolicy) (execution seed)).map
        ((runtime setup).bindingTraffic leaks focal))
    (fun _ _ _ _ _ _ _ _ same => same)
    (fun left leftSupport _ _ right _ _ _ _ same =>
      (runtime setup).bindingTraffic_silent_round leaks scheduler focal
        (execution left) (execution right) same event owner payload outputEq codeEq node
        (soleReady_of_ready setup _ (ready left leftSupport)))
  exact ⟨nextNoise, by simpa only [PMF.pure_bind, PMF.pure_map, PMF.bind_pure,
    PMF.map_id, PMF.map_comp, Function.comp_def] using law⟩

end Vegas
