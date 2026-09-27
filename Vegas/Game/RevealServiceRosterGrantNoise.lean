/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterNoise

/-! # Granting the next roster preserves conditional traffic independence -/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem PublicCheckpoint.grant_noise_congr
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    {leftInitial rightInitial : State L setup.context} {Γ : SourceCtx Player L}
    {leftSource rightSource : Config Player L Γ}
    {refs : ContextRefs (graph setup).layout Γ} {rank : Nat}
    {left right : (application setup leaks).Execution}
    (leftCheckpoint : PublicCheckpoint setup leaks leftInitial leftSource refs rank left)
    (rightCheckpoint : PublicCheckpoint setup leaks rightInitial rightSource refs rank right)
    (event : (graph setup).EventId) (focal : Player)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (grants : left.application.serviceGrant = right.application.serviceGrant)
    (same : leftSource.view focal = rightSource.view focal)
    (readouts : ((application setup leaks).messageView left, left.recall focal) =
      ((application setup leaks).messageView right, right.recall focal)) :
    ((runtime setup).runInteractionPlan leaks players network [.grant event] left).map
        (fun final => ((application setup leaks).messageView final, final.recall focal)) =
      ((runtime setup).runInteractionPlan leaks players network [.grant event] right).map
        (fun final => ((application setup leaks).messageView final, final.recall focal)) := by
  have messages := congrArg Prod.fst readouts
  have recall := congrArg Prod.snd readouts
  have networks := congrArg Prod.fst messages
  have leaked := congrArg (fun net => net.leaked focal) networks
  have observed := leftCheckpoint.observe_eq rightCheckpoint focal grants leaked same
  have publicView := congrArg
    (fun view : (application setup leaks).PlayerView => view.application.publicView) observed
  have receipts := congrArg (fun value => value.2.1) messages
  have environment := congrArg (fun value => value.2.2.1) messages
  have masked := congrArg (fun value => value.2.2.2) messages
  simp only [runInteractionPlan, interactionStep, interactionInstruction, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    reactiveApplication, environmentStep, FinDist.map_pure,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  apply congrArg FinDist.pure
  change ((left.network, left.receipts,
    left.environmentRecall ++ [⟨⟨left.network.publicView, left.application.publicView,
      left.receipts⟩, .application (.grant event)⟩],
    fun who => (application setup leaks).messageRecall (left.recall who)), left.recall focal) = _
  change left.network = right.network at networks
  change left.receipts = right.receipts at receipts
  change left.environmentRecall = right.environmentRecall at environment
  change left.application.publicView = right.application.publicView at publicView
  change left.recall focal = right.recall focal at recall
  change (fun who => (application setup leaks).messageRecall (left.recall who)) =
    (fun who => (application setup leaks).messageRecall (right.recall who)) at masked
  rw [networks, receipts, environment, publicView, recall]
  exact congrArg (fun recalled => ((right.network, right.receipts,
    right.environmentRecall ++ [⟨⟨right.network.publicView, right.application.publicView,
      right.receipts⟩, .application (.grant event)⟩], recalled), right.recall focal)) masked

/-- The grant is part of the observed service transcript. Its exact recorded
public view preserves conditional independence at a supported source checkpoint. -/
theorem roster_grant_observation_kernel
    {Seed : Type*} (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} (refs : ContextRefs (graph setup).layout Γ) (rank : Nat)
    (prior : FinDist Seed) (initial : Seed → State L setup.context)
    (source : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (checkpoint : ∀ seed ∈ prior.support,
      PublicCheckpoint setup leaks (initial seed) (source seed) refs rank (execution seed))
    (event : (graph setup).EventId) (focal : Player)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (grant : Option (graph setup).EventId)
    (granted : ∀ seed ∈ prior.support, (execution seed).application.serviceGrant = grant)
    (noise : DecisionView focal Γ → FinDist ((application setup leaks).MessageReadout ×
      List (application setup leaks).PlayerEntry))
    (factor : prior.map (fun seed => (source seed,
        ((application setup leaks).messageView (execution seed), (execution seed).recall focal))) =
      (prior.map source).bind fun config => (noise (config.view focal)).map fun extra =>
        (config, extra)) :
    ∃ nextNoise : DecisionView focal Γ → FinDist ((application setup leaks).MessageReadout ×
        List (application setup leaks).PlayerEntry),
      (prior.bind fun seed =>
        ((runtime setup).runInteractionPlan leaks players network [.grant event]
          (execution seed)).map fun final =>
            (source seed, ((application setup leaks).messageView final, final.recall focal))) =
      (prior.map source).bind fun config =>
        (nextNoise (config.view focal)).map fun extra => (config, extra) := by
  obtain ⟨nextNoise, nextLaw⟩ :=
    FinDist.exists_updated_observation_kernel_of_readout prior source
      (fun seed => ((application setup leaks).messageView (execution seed),
        (execution seed).recall focal)) (fun config => config.view focal) noise factor
      (fun _ => FinDist.pure ()) (fun config _ => config) (fun config => config.view focal)
      (fun seed _ => ((runtime setup).runInteractionPlan leaks players network [.grant event]
        (execution seed)).map fun final =>
          ((application setup leaks).messageView final, final.recall focal))
      (fun _ _ _ _ _ _ _ _ same => same)
      (fun left leftSupport _ _ right rightSupport _ _ same readouts =>
        (checkpoint left leftSupport).grant_noise_congr (checkpoint right rightSupport)
          event focal players network
          ((granted left leftSupport).trans (granted right rightSupport).symm) same readouts)
  refine ⟨nextNoise, ?_⟩
  simpa only [FinDist.pure_bind, FinDist.map_pure, FinDist.bind_pure,
    FinDist.map_comp, Function.comp_def] using nextLaw

end Vegas.SourceProgram.RevealService
