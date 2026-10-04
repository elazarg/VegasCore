/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceStep
import Vegas.Pending.ReactiveSampleLikelihood
import Vegas.Source.ObservationRecall
import GameTheory.Math.Probability.ConditionalObservation

/-! # Source-conditioned traffic after a real public sample

The actual environment command samples the compiled public distribution,
completes its event and appends the scheduler's pre-command observation. Its
typed output supplies the value used to advance both carried source states.
The joint successor and complete focal traffic law factors through the source
successor view, without a roster, independent noise or a supplied posterior.

This is one environment step. Stopped completion laws and transport to source
information sites remain separate obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The public value read from the actual sample step updates the carried
effective and original source states. All traffic comes from the real
environment transition, including its scheduler record and unchanged own
recall. Readiness and source/store agreement are needed only on prior support. -/
theorem source_async_sample_environment_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (refs : ContextRefs (graph setup).layout Γ)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs law))
    (node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs law) outputEq codeEq)
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (ready : ∀ seed ∈ prior.support, (execution seed).application.config.cut.Ready event)
    (agree : ∀ seed ∈ prior.support,
      refs.Agrees (source seed).state (execution seed).application.config.store)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        ((execution seed).environmentStep (application setup leaks)
          (.application (.executeSample event))).map fun final =>
            (((⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
                (.publicData payload)).get? final.application.config.store).map fun value =>
              (sampleSuccessor name (source seed) value,
                sampleSuccessor name (original seed) value),
              (runtime setup).bindingTraffic leaks focal final)) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (L.evalDist law (sourcePublicEnv pair.1.state)).map fun value =>
          (sampleSuccessor name pair.1 value, sampleSuccessor name pair.2 value)).bind fun pair =>
            (nextNoise (pair.1.view focal)).map fun extra => (some pair, extra) := by
  classical
  let app := application setup leaks
  let output : EventGraph.FieldRef (graph setup).layout (.publicData payload) :=
    ⟨.inr event, outputEq⟩
  let sampled := fun seed (value : L.Val payload) =>
    if present : seed ∈ prior.support then
      ({ execution seed with
          application := (execution seed).application.complete event (ready seed present)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)
          environmentRecall := (execution seed).environmentRecall ++
            [⟨(execution seed).observeEnvironment app, .application (.executeSample event)⟩] } :
        app.Execution)
    else execution seed
  have sampleLaw seed (supported : seed ∈ prior.support) :
      (execution seed).environmentStep app (.application (.executeSample event)) =
        (L.evalDist law (sourcePublicEnv (source seed).state)).map (sampled seed) := by
    have applicationLaw : app.environment (execution seed).application (.executeSample event) =
        (L.evalDist law (sourcePublicEnv (source seed).state)).map fun value =>
          (execution seed).application.complete event (ready seed supported)
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value) :=
      source_sample_environment (runtime setup) (execution seed).application event
        (ready seed supported) outputEq refs law codeEq node (source seed).state
        (agree seed supported)
    simp only [ReactiveApplication.Execution.environmentStep, applicationLaw, PMF.map_comp]
    apply map_congr_on_support _
    intro value _valueSupported
    simp only [sampled, dite_eq_left supported, Function.comp_apply]
  have sampledOutput seed (supported : seed ∈ prior.support) (value : L.Val payload) :
      output.get? (sampled seed value).application.config.store = some value := by
    simp only [sampled, dite_eq_left supported]
    rw [EventGraphRuntime.State.complete, EventGraph.store_complete]
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
  have updated := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor
    (fun pair => L.evalDist law (sourcePublicEnv pair.1.state))
    (fun pair value => (sampleSuccessor name pair.1 value, sampleSuccessor name pair.2 value))
    (fun pair => pair.1.view focal)
    (fun seed value => PMF.pure ((runtime setup).bindingTraffic leaks focal (sampled seed value)))
    (by
      intro left _ first _ right _ second _ same
      have earlier := congrArg (DecisionView.back false) same
      simpa only [back_sample_view] using earlier)
    (by
      intro left leftSupport first _ right rightSupport second _ same traffic
      have valueEq : first = second := by
        have cell := congrArg
          (fun view : DecisionView focal ((name, .publicData payload) :: Γ) =>
            view.1.cells.get .here) same
        simpa only [Config.view, sampleSuccessor, sourceObserve, Env.get, Env.cons] using cell
      subst second
      apply congrArg PMF.pure
      simp only [sampled, dite_eq_left leftSupport, dite_eq_left rightSupport]
      exact (runtime setup).bindingTraffic_sample_result leaks (execution left) (execution right)
        focal traffic event (ready left leftSupport) (ready right rightSupport) payload outputEq
          first)
  obtain ⟨nextNoise, joint⟩ := updated
  refine ⟨nextNoise, ?_⟩
  have tagged := congrArg (PMF.map fun pair => (some pair.1, pair.2)) joint
  simp only [PMF.map_bind, PMF.map_comp, PMF.pure_map] at tagged
  calc
    _ = prior.bind (fun seed =>
        (L.evalDist law (sourcePublicEnv (source seed).state)).map fun value =>
          (some (sampleSuccessor name (source seed) value,
            sampleSuccessor name (original seed) value),
            (runtime setup).bindingTraffic leaks focal (sampled seed value))) := by
      apply bind_congr_on_support _
      intro seed supported
      rw [sampleLaw seed supported, PMF.map_comp]
      apply map_congr_on_support _
      intro value _valueSupported
      change (output.get? (sampled seed value).application.config.store |>.map
        (fun value => (sampleSuccessor name (source seed) value,
          sampleSuccessor name (original seed) value)), _) = _
      rw [sampledOutput seed supported value, Option.map_some]
    _ = _ := by
      simpa only [PMF.pure_map, ← PMF.bind_pure_comp, Function.comp_def, PMF.pure_bind]
        using tagged

end Vegas
