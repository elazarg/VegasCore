/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterNoise
import Vegas.Game.ServiceRoster
import Vegas.Game.RevealServicePrefixInformation
import Vegas.Pending.ReactiveServiceGrant

/-! # Granting the next roster preserves conditional traffic independence -/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The phase boundary grant is fixed by the public plan, including at
zero-probability histories and under arbitrary raw responses. -/
theorem roster_prefix_serviceGrant
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (count : Nat) (within : count ≤ (graph setup).order.eventCount) :
    ∃ grant, ∀ initial final : (application setup leaks).Execution,
      initial.application.serviceGrant = none →
      final ∈ ((runtime setup).runInteractionPlan leaks players network
        (rosterPlanPrefix setup rosters count) initial).support →
        final.application.serviceGrant = grant := by
  cases count with
  | zero =>
      refine ⟨none, ?_⟩
      intro initial final initialGrant reached
      simp only [rosterPlanPrefix, List.take_zero, List.flatMap_nil, runInteractionPlan,
        FinDist.mem_support_pure] at reached
      simpa only [reached] using initialGrant
  | succ count =>
      let event : (graph setup).EventId := ⟨count, by omega⟩
      refine ⟨some event, ?_⟩
      intro initial final _ reached
      rw [show count + 1 = event.val + 1 from rfl, rosterPlanPrefix_succ,
        runInteractionPlan_append, FinDist.support_bind] at reached
      obtain ⟨boundary, _, reached⟩ := Set.mem_iUnion₂.mp reached
      let tail := (rosters event).map ServiceInstruction.player ++
        (match (graph setup).actor? event with
        | none => [.sample event]
        | some owner => [.includeLatest event owner]) ++
          List.replicate (event.val + 1) .tick ++ [.expire event]
      change final ∈ ((runtime setup).interactionStep leaks players network (.grant event)
        boundary |>.bind ((runtime setup).runInteractionPlan leaks players network tail)).support
        at reached
      obtain ⟨granted, step, reached⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
      have grantEq : granted.application.serviceGrant = some event := by
        simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
          ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
          reactiveApplication, environmentStep, FinDist.map_pure,
          ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          FinDist.mem_support_pure] at step
        cases step
        rfl
      rw [(runtime setup).runInteractionPlan_serviceGrant leaks players network tail ?_ ?_
        granted final reached]
      · exact grantEq
      · cases ownerEq : (graph setup).actor? event <;> simp [tail, ownerEq]
      · intro other
        cases ownerEq : (graph setup).actor? event <;> simp [tail, ownerEq]

private theorem grant_readout_congr
    {setup : Setup (Player := Player) (L := L)}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
    (left right : (application setup leaks).Execution)
    (event : (graph setup).EventId) (focal : Player)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (publicView : left.application.publicView = right.application.publicView)
    (readouts : ((application setup leaks).messageView left, left.recall focal) =
      ((application setup leaks).messageView right, right.recall focal)) :
    ((runtime setup).runInteractionPlan leaks players network [.grant event] left).map
        (fun final => ((application setup leaks).messageView final, final.recall focal)) =
      ((runtime setup).runInteractionPlan leaks players network [.grant event] right).map
        (fun final => ((application setup leaks).messageView final, final.recall focal)) := by
  have messages := congrArg Prod.fst readouts
  have recall := congrArg Prod.snd readouts
  have networks := congrArg Prod.fst messages
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
  have networks := congrArg Prod.fst (congrArg Prod.fst readouts)
  have leaked := congrArg (fun net => net.leaked focal) networks
  have observed := leftCheckpoint.observe_eq rightCheckpoint focal grants leaked same
  exact grant_readout_congr _ _ event focal players network
    (congrArg (fun view : (application setup leaks).PlayerView => view.application.publicView)
      observed) readouts

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

/-- The actual grant preserves ancillary traffic at an existing decoded
source prefix. The previous grant is fixed by the initialized service plan. -/
theorem roster_prefix_grant_observation_kernel
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (prior : FinDist (application setup leaks).Execution) (count : Nat)
    (checkpoint : ∀ execution ∈ prior.support, ∃ initial state,
      PublicPrefixCheckpoint setup leaks initial setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program) 0 count state execution ∧
      sourcePrefix? setup count execution.application.config = some state)
    (event : (graph setup).EventId) (focal : Player)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (grant : Option (graph setup).EventId)
    (granted : ∀ execution ∈ prior.support, execution.application.serviceGrant = grant)
    (noise : setup.ProtocolView focal → FinDist ((application setup leaks).MessageReadout ×
      List (application setup leaks).PlayerEntry))
    (factor : prior.map (fun execution =>
        (sourcePrefix? setup count execution.application.config,
          ((application setup leaks).messageView execution, execution.recall focal))) =
      (prior.map fun execution => sourcePrefix? setup count execution.application.config).bind
        fun state => (noise (setup.protocolObserve focal state)).map fun extra => (state, extra)) :
    ∃ nextNoise : setup.ProtocolView focal →
        FinDist ((application setup leaks).MessageReadout ×
          List (application setup leaks).PlayerEntry),
      let after := prior.bind
        ((runtime setup).runInteractionPlan leaks players network [.grant event])
      after.map (fun execution => (sourcePrefix? setup count execution.application.config,
        ((application setup leaks).messageView execution, execution.recall focal))) =
      (prior.map fun execution => sourcePrefix? setup count execution.application.config).bind
        fun state => (nextNoise (setup.protocolObserve focal state)).map fun extra =>
          (state, extra) :=
    by
  obtain ⟨nextNoise, nextLaw⟩ := FinDist.exists_updated_observation_kernel_of_readout prior
    (fun execution => sourcePrefix? setup count execution.application.config)
    (fun execution => ((application setup leaks).messageView execution, execution.recall focal))
    (setup.protocolObserve focal) noise factor (fun _ => FinDist.pure ())
    (fun state _ => state) (setup.protocolObserve focal)
    (fun execution _ => ((runtime setup).runInteractionPlan leaks players network [.grant event]
      execution).map fun final => ((application setup leaks).messageView final, final.recall focal))
    (fun _ _ _ _ _ _ _ _ same => same) (by
      intro left leftSupport _ _ right rightSupport _ _ same readouts
      obtain ⟨_, leftState, leftCheckpoint, leftDecoded⟩ := checkpoint left leftSupport
      obtain ⟨_, rightState, rightCheckpoint, rightDecoded⟩ := checkpoint right rightSupport
      have views : ProtocolState.observe focal setup.program leftState =
          ProtocolState.observe focal setup.program rightState := by
        rw [leftDecoded, rightDecoded] at same
        exact Option.some.inj same
      have networks := congrArg Prod.fst (congrArg Prod.fst readouts)
      have observed := (PublicPrefixCheckpoint.observe_eq_iff focal setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (Revelations.initial setup.context) (outputRef setup.program) 0 count
        leftState rightState left right leftCheckpoint rightCheckpoint
        ((granted left leftSupport).trans (granted right rightSupport).symm)
        (congrArg (fun net => net.leaked focal) networks)).mp views
      exact grant_readout_congr left right event focal players network
        (congrArg (fun view : (application setup leaks).PlayerView => view.application.publicView)
          observed) readouts)
  refine ⟨nextNoise, ?_⟩
  simpa only [FinDist.pure_bind, FinDist.map_pure, FinDist.bind_pure, FinDist.map_bind,
    FinDist.map_comp, Function.comp_def, runInteractionPlan, interactionStep,
    interactionInstruction, ReactiveApplication.dispatch,
    ReactiveApplication.Execution.environmentStep, reactiveApplication, environmentStep,
    ReactiveApplication.Command.actor?, ReactiveApplication.resume] using nextLaw

end Vegas
