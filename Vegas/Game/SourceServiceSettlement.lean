/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolution

/-! # Sampling and binding settlement in the existing service

The complete sampling and binding phases execute the actual clock and expiry
instructions. Those instructions preserve an already completed event's typed
configuration and receipts. No publication guard or fixed candidate catalogue
is assumed, and public chance retains its original distribution.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Sampling is the actual application kernel with its environment command
recorded; it invokes no player policy. -/
theorem interactionStep_sample (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (execution : (runtime.reactiveApplication leaks).Execution) (event : graph.EventId) :
    runtime.interactionStep leaks players network (.sample event) execution =
      (environmentStep runtime execution.application (.executeSample event)).map fun state =>
        { execution with
          application := state
          environmentRecall := execution.environmentRecall ++
            [⟨execution.observeEnvironment (runtime.reactiveApplication leaks),
              .application (.executeSample event)⟩] } := by
  simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Command.actor?]
  change (execution.environmentStep (runtime.reactiveApplication leaks)
    (.application (.executeSample event))).bind FinDist.pure = _
  rw [FinDist.bind_pure]
  change ((environmentStep runtime execution.application (.executeSample event)).map
    (fun state => ({ execution with application := state } :
      (runtime.reactiveApplication leaks).Execution))).map _ = _
  rw [FinDist.map_comp]
  rfl

/-- An actual settled clock tail preserves the configuration and receipt law
of any preceding random service step supported on completed configurations. -/
theorem settled_tail_config_receipts (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (law : FinDist (runtime.reactiveApplication leaks).Execution)
    (event : graph.EventId) (ticks : Nat)
    (settled : ∀ execution ∈ law.support, ¬execution.application.config.cut.Ready event) :
    (law.bind (runtime.runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]))).map
        (fun final => (final.application.config, final.receipts)) =
      law.map (fun final => (final.application.config, final.receipts)) := by
  rw [FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro execution supported
  obtain ⟨final, exactLaw, state, _, receipts, _⟩ := runtime.settled_reveal_expiry leaks players
    network execution event (settled execution supported) ticks
  exact (congrArg (FinDist.map (fun final : (runtime.reactiveApplication leaks).Execution =>
    (final.application.config, final.receipts))) exactLaw).trans (by
      rw [FinDist.map_pure, state, receipts])

end Vegas.EventGraphRuntime

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The real sample instruction and its complete settlement tail have exactly
the original public-chance law, including all original correlations. -/
theorem source_sample_settlement
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
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) :
    ((runtime setup).runInteractionPlan leaks players network
      (.sample event :: List.replicate ticks .tick ++ [.expire event]) execution).map
        (fun final => (final.application.config, final.receipts)) =
      (L.evalDist law (sourcePublicEnv source.state)).map fun value =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value),
          execution.receipts) := by
  have sampleLaw : ((runtime setup).interactionStep leaks players network (.sample event)
      execution).map (fun final => (final.application.config, final.receipts)) =
      (L.evalDist law (sourcePublicEnv source.state)).map fun value =>
        (execution.application.config.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value),
          execution.receipts) := by
    rw [(runtime setup).interactionStep_sample]
    rw [source_sample_environment (runtime setup) execution.application event ready outputEq refs
      law codeEq node source.state agree]
    simp only [FinDist.map_comp]
    rfl
  have settled : ∀ middle ∈ ((runtime setup).interactionStep leaks players network
      (.sample event) execution).support, ¬middle.application.config.cut.Ready event := by
    intro middle supported
    have mapped : (middle.application.config, middle.receipts) ∈
        (((runtime setup).interactionStep leaks players network (.sample event) execution).map
          (fun final => (final.application.config, final.receipts))).support :=
      FinDist.support_map .. ▸ ⟨middle, supported, rfl⟩
    rw [sampleLaw, FinDist.support_map] at mapped
    obtain ⟨value, _, same⟩ := mapped
    have configEq := congrArg Prod.fst same
    dsimp only at configEq
    intro active
    rw [← configEq] at active
    exact active.1 (by simp [EventOrder.Cut.complete])
  change (((runtime setup).interactionStep leaks players network (.sample event) execution).bind
    ((runtime setup).runInteractionPlan leaks players network
      (List.replicate ticks .tick ++ [.expire event]))).map _ = _
  exact ((runtime setup).settled_tail_config_receipts leaks players network _ event ticks
    settled).trans sampleLaw

end Vegas.SourceProgram.RevealService
