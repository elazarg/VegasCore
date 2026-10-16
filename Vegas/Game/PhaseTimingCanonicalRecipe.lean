/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingPools
import Vegas.Game.PhaseCanonicalSafeInput

/-! # Timing components on actual canonical callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source sourceLimit.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (sourceLimit.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (delay bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler

include copies continuing maximal capacity

/-- Every operational component agrees with the perturbed source prescription
at an actual clear callback whose complete recalls follow the canonical policy.
Protected requests are unkeyed; singleton menus have a unique probability law. -/
theorem phaseTimingComponent_eq_source_of_canonical_callback
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (opportunity : PhaseService.Opportunity runtime leaks start horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (values : ∀ event owner payload,
      ((serviceGraph setup mode).outputLayout event = .binding owner payload ∨
        (serviceGraph setup mode).outputLayout event = .publication payload) →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (agent : (N).InformationAgent (N).playedInformation)
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some agent.1)
    (atInput : agent.2.1 = some
      (current.execution.recall agent.1, current.execution.observe app agent.1))
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ who, (phaseSourcePolicy setup mode runtime leaks bounds wellFormed sourceLimit
      who).Consistent (current.execution.recall who))
    (part : PhaseTimingPart setup mode runtime leaks bounds start horizon scheduler bound
      (phaseTimingPool setup mode runtime leaks bounds start horizon scheduler bound agent)) :
    phaseTimingComponent setup mode runtime leaks bounds start horizon scheduler bound wellFormed
        assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded agent part =
      phaseSourcePerturbedStrategy setup mode runtime leaks bounds start horizon scheduler
        wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
          agent.1 agent.2.1 := by
  classical
  have initialEq : (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) =
      (start) := PMF.map_comp encodeInputs setup.initialLaw (PhaseRuntimeState.initial plan)
  have physicalTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some current) := by
    rw [initialEq]
    exact trace
  have physicalOpportunity : PhaseService.Opportunity runtime leaks
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler delay := by
    rw [initialEq]
    exact opportunity
  have activeTrace : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some ⟨current.remaining, some agent.1, current.execution⟩) := by
    simpa only [← acting] using physicalTrace
  obtain protectedRequest | singleton := phaseSourcePolicy_protected_or_singleton setup mode runtime
    leaks bounds wellFormed source sourceLimit copies continuing plan maximal horizon scheduler
      capacity delay bound physicalOpportunity timely current.remaining agent.1 current.execution
        activeTrace clear consistent values
  · obtain ⟨event, request, _unsent, _kind, fits⟩ := protectedRequest
    have notFree : ¬ PhasePublicExclusion setup mode runtime leaks agent.2.1 := by
      rw [atInput]
      rintro ⟨past, view, same, excluded⟩
      have viewEq := congrArg Prod.snd (Option.some.inj same)
      have flags := congrArg (fun view : (app).PlayerView => view.application.2.excluded) viewEq
      exact excluded (flags.symm.trans clear)
    have notKeyed : ¬ PhaseUnprotected runtime leaks bound agent.1 agent.2.1 := by
      rintro ⟨past, view, other, same, requested, late⟩
      have viewEq := congrArg Prod.snd (Option.some.inj (atInput.symm.trans same))
      cases viewEq
      obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan
        (setup.initialLaw.map encodeInputs) horizon scheduler
          ((menu).toRawTrace _ _ _ physicalTrace)
      have otherRequest := (PhaseRuntimeState.requests_publicView
        current.execution.application valid agent.1
          ⟨current.execution.application.attempt, other⟩).mp requested
      have sameEvent := (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique
        current.execution.application.current.native.config.cut request.2.2.1
          otherRequest.2.2.1 request.2.2.2.1 otherRequest.2.2.2.1
      change other = event at sameEvent
      subst other
      exact late fits
    have notOwned : ¬ ownedKeyed
        (fun agent : (N).InformationAgent (N).playedInformation =>
          PhasePublicExclusion setup mode runtime leaks agent.2.1)
        (fun agent => PhaseUnprotected runtime leaks bound agent.1 agent.2.1) agent :=
      fun owned => notKeyed owned.1
    unfold phaseTimingComponent
    obtain ⟨identify, same⟩ := freeKeyedComponent_of_not_free
      (free := fun agent : (N).InformationAgent (N).playedInformation =>
        PhasePublicExclusion setup mode runtime leaks agent.2.1)
      (keyed := fun agent => PhaseUnprotected runtime leaks bound agent.1 agent.2.1)
      (key := fun agent => phaseTimingKey runtime leaks agent.1 agent.2.1)
      (Opt := LateOption bounds.candidateCount)
      (fun agent choice => mix noise nonnegative bounded
        ((menu).uniformPolicy start horizon scheduler agent.1 agent.2.1) (PMF.pure choice))
      (fun agent => phaseSourcePerturbedStrategy setup mode runtime leaks bounds start horizon
        scheduler wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative
          slotBounded agent.1 agent.2.1)
      (fun agent option => phaseSourceTimingComponent setup mode runtime leaks bounds start horizon
        scheduler wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative
          slotBounded agent.1 agent.2.1 option) notFree
    exact (same part).trans (keyedComponent_of_not_keyed _ _ notOwned (identify part))
  · have singletonMenu : ((N).menu agent.1 agent.2.1).Subsingleton := by
      rw [atInput]
      intro first firstMember second secondMember
      change ∃ action ∈ (menu).actions agent.1 (current.execution.recall agent.1)
        (current.execution.observe app agent.1), first = some action at firstMember
      change ∃ action ∈ (menu).actions agent.1 (current.execution.recall agent.1)
        (current.execution.observe app agent.1), second = some action at secondMember
      obtain ⟨firstAction, firstAllowed, firstEq⟩ := firstMember
      obtain ⟨secondAction, secondAllowed, secondEq⟩ := secondMember
      change firstAction ∈ PhaseCount.onePacketActions runtime leaks bounds _ _ _ at firstAllowed
      change secondAction ∈ PhaseCount.onePacketActions runtime leaks bounds _ _ _ at secondAllowed
      rw [singleton, Finset.mem_singleton] at firstAllowed secondAllowed
      exact firstEq.trans ((congrArg some (firstAllowed.trans secondAllowed.symm)).trans
        secondEq.symm)
    let _ := (N).subsingleton_choice_of_menu_subsingleton agent.2.1 singletonMenu
    exact (eq_pure_of_subsingleton _ (Classical.arbitrary _)).trans
      (eq_pure_of_subsingleton _ (Classical.arbitrary _)).symm

end Vegas
