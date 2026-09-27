/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettlement
import Vegas.Pending.ReactiveSampleLikelihood
import GameTheoryExtensions.Math.Probability.ConditionalNoise
import Vegas.Source.ObservationRecall

/-! # Public chance and the original source-memory factorization

The sample law is the source distribution evaluated on its public state.
Each sampled value updates the effective and original source configurations
together. The auxiliary traffic is the actual runtime completion, including
the environment's recorded observation; it introduces no extra channel premise.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open Interaction EventGraphRuntime EventLowering GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The readout of the actual sample-completion map at a specified public draw.
The equation below relates this conditional law to the real service step. -/
def samplePhaseTranscript (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (focal : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .publicData payload)
    (value : L.Val payload) :=
  FinDist.pure ((runtime setup).bindingTraffic leaks focal
    { execution with
      application := execution.application.complete event ready
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
        (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)
      environmentRecall := execution.environmentRecall ++
        [⟨execution.observeEnvironment (application setup leaks),
          .application (.executeSample event)⟩] })

/-- Integrating the conditional readout gives exactly the actual native
sampling instruction, with the original public source distribution. -/
theorem source_sample_traffic
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs law))
    (node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs law) outputEq codeEq)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (focal : Player) :
    (((runtime setup).interactionStep leaks players network (.sample event) execution).map
      ((runtime setup).bindingTraffic leaks focal)) =
      (L.evalDist law (sourcePublicEnv source.state)).bind
        (samplePhaseTranscript setup leaks focal execution event ready payload outputEq) := by
  rw [(runtime setup).interactionStep_sample,
    source_sample_environment (runtime setup) execution.application event ready outputEq refs
      law codeEq node source.state agree, FinDist.map_comp]
  rw [FinDist.map_comp, FinDist.map_eq_bind]
  rfl

/-- The full joint source-memory factorization survives public sampling.
Its factor premise concerns the preceding prefix, while the next conditional
law is derived from the actual runtime completion and the public source draw. -/
theorem sample_successor_memory_factorization
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (name : VarId) (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (prior : FinDist Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (ready : ∀ seed, (execution seed).application.config.cut.Ready event)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (noise : DecisionView focal Γ → FinDist _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → FinDist _,
      (prior.bind fun seed => (L.evalDist law (sourcePublicEnv (source seed).state)).bind
        fun value => (samplePhaseTranscript setup leaks focal (execution seed) event (ready seed)
          payload outputEq value).map fun extra =>
            ((sampleSuccessor name (source seed) value,
              sampleSuccessor name (original seed) value), extra)) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (L.evalDist law (sourcePublicEnv pair.1.state)).map fun value =>
          (sampleSuccessor name pair.1 value, sampleSuccessor name pair.2 value)).bind fun pair =>
        (nextNoise (pair.1.view focal)).map fun extra => (pair, extra) := by
  apply FinDist.exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor
    (fun pair => L.evalDist law (sourcePublicEnv pair.1.state))
    (fun pair value => (sampleSuccessor name pair.1 value, sampleSuccessor name pair.2 value))
    (fun pair => pair.1.view focal)
  · intro left _ first _ right _ second _ same
    have earlier := congrArg (DecisionView.back false) same
    simpa only [back_sample_view] using earlier
  · intro left _ first _ right _ second _ same traffic
    have valueEq : first = second := by
      have cell := congrArg
        (fun view : DecisionView focal ((name, .publicData payload) :: Γ) =>
          view.1.cells.get .here) same
      simpa only [Config.view, sampleSuccessor, sourceObserve, Env.get, Env.cons] using cell
    subst second
    apply congrArg FinDist.pure
    exact (runtime setup).bindingTraffic_sample_result leaks (execution left) (execution right)
      focal traffic event (ready left) (ready right) payload outputEq first

end Vegas.SourceProgram.RevealService
