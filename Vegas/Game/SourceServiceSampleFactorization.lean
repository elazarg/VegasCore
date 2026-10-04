/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSettlement
import Vegas.Pending.ReactiveSampleLikelihood
import Vegas.Pending.ReactiveOpeningLikelihood
import GameTheory.Math.Probability.ConditionalObservation
import Vegas.Source.ObservationRecall
import GameTheoryExtensions.Math.Probability.Support
import GameTheoryExtensions.Math.Probability.Expectation
import GameTheoryExtensions.Math.Probability.Uniform

/-! # Public chance and the original source-memory factorization

The sample law is the source distribution evaluated on its public state.
Each sampled value updates the effective and original source configurations
together. The auxiliary traffic is the actual runtime completion, including
the environment's recorded observation; it introduces no extra channel premise.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual replay roster, specified public draw and complete maintenance
tail. The equation below integrates this conditional law into the real phase. -/
def samplePhaseTranscript (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player) (ticks : Nat)
    (focal : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (payload : L.Ty) (outputEq : (graph setup).outputLayout event = .publicData payload)
    (value : L.Val payload) :=
  let app := application setup leaks
  let replay := fun _ : Player => app.replayPolicy
  ((runtime setup).runInteractionPlan leaks replay network
    (roster.map ServiceInstruction.player) execution).bind fun current =>
      ((runtime setup).runInteractionPlan leaks replay network
        (List.replicate ticks .tick ++ [.expire event])
        { current with
          application := execution.application.complete event ready
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
            (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)
          environmentRecall := current.environmentRecall ++
            [⟨current.observeEnvironment app, .application (.executeSample event)⟩] }).map
              ((runtime setup).bindingTraffic leaks focal)

private theorem sample_replays_application
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).replayPolicy) network
        (roster.map ServiceInstruction.player) initial).support) :
    final.application = initial.application := by
  cases roster with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons first rest =>
      exact ((runtime setup).replay_window_preserves leaks
        (fun _ => (application setup leaks).replayPolicy) network first initial
        (fun current who response _ _ supported =>
          (application setup leaks).replayPolicy_cases _ _ response supported)
        (fun _ => True) ⟨by simp, by simp, by simp, by simp⟩ (first :: rest) final reached).1

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
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player) (ticks : Nat)
    (focal : Player) :
    (((runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
      network (roster.map ServiceInstruction.player ++
        (.sample event :: List.replicate ticks .tick ++ [.expire event])) execution).map
          ((runtime setup).bindingTraffic leaks focal)) =
      (L.evalDist law (sourcePublicEnv source.state)).bind
        (samplePhaseTranscript setup leaks network roster ticks focal execution event ready
          payload outputEq) := by
  let app := application setup leaks
  let replay := fun _ : Player => app.replayPolicy
  unfold samplePhaseTranscript
  rw [PMF.bind_comm]
  rw [runInteractionPlan_append, PMF.map_bind]
  apply bind_congr_on_support _
  intro current reached
  have same := sample_replays_application setup leaks network roster execution current reached
  have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
  have currentAgree : refs.Agrees source.state current.application.config.store := by
    rw [same]; exact agree
  change (((runtime setup).interactionStep leaks replay network (.sample event) current).bind
    ((runtime setup).runInteractionPlan leaks replay network
      (List.replicate ticks .tick ++ [.expire event]))).map _ = _
  rw [(runtime setup).interactionStep_sample,
    source_sample_environment (runtime setup) current.application event currentReady outputEq refs
      law codeEq node source.state currentAgree, PMF.map_comp, PMF.bind_map,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro value _
  simp only [same]
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
    (prior : PMF Seed) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (ready : ∀ seed, (execution seed).application.config.cut.Ready event)
    (recalled : ∀ seed ∈ prior.support, (execution seed).InputRecall (application setup leaks))
    (network : (runtime setup).NetworkPolicy leaks) (roster : List Player) (ticks : Nat)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .publicData payload) :: Γ) → PMF _,
      (prior.bind fun seed => (L.evalDist law (sourcePublicEnv (source seed).state)).bind
        fun value => (samplePhaseTranscript setup leaks network roster ticks focal
          (execution seed) event (ready seed) payload outputEq value).map fun extra =>
            ((sampleSuccessor name (source seed) value,
              sampleSuccessor name (original seed) value), extra)) =
      ((prior.map (fun seed => (source seed, original seed))).bind fun pair =>
        (L.evalDist law (sourcePublicEnv pair.1.state)).map fun value =>
          (sampleSuccessor name pair.1 value, sampleSuccessor name pair.2 value)).bind fun pair =>
        (nextNoise (pair.1.view focal)).map fun extra => (pair, extra) := by
  apply exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor
    (fun pair => L.evalDist law (sourcePublicEnv pair.1.state))
    (fun pair value => (sampleSuccessor name pair.1 value, sampleSuccessor name pair.2 value))
    (fun pair => pair.1.view focal)
  · intro left _ first _ right _ second _ same
    have earlier := congrArg (DecisionView.back false) same
    simpa only [back_sample_view] using earlier
  · intro left leftSupport first _ right rightSupport second _ same traffic
    have valueEq : first = second := by
      have cell := congrArg
        (fun view : DecisionView focal ((name, .publicData payload) :: Γ) =>
          view.1.cells.get .here) same
      simpa only [Config.view, sampleSuccessor, sourceObserve, Env.get, Env.cons] using cell
    subst second
    simp only [samplePhaseTranscript]
    apply bind_eq_of_map_eq _ _ _ _
      ((runtime setup).replay_window_focal_law leaks network roster focal
        (execution left) (execution right) (recalled left leftSupport)
        (recalled right rightSupport) traffic)
    intro before beforeSupport after afterSupport equal
    have leftApp := sample_replays_application setup leaks network roster
      (execution left) before beforeSupport
    have rightApp := sample_replays_application setup leaks network roster
      (execution right) after afterSupport
    have beforeReady : before.application.config.cut.Ready event := by
      rw [leftApp]; exact ready left
    have afterReady : after.application.config.cut.Ready event := by
      rw [rightApp]; exact ready right
    apply (runtime setup).settlement_focal_law
    have completed := (runtime setup).bindingTraffic_sample_result leaks before after
      focal equal event beforeReady afterReady payload outputEq first
    simpa only [leftApp, rightApp] using completed

end Vegas
