/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingBindingResponseRatio
import Vegas.Game.PhaseTimingBindingWaitingRatio
import Vegas.Game.PhaseRepairResponseFactor
import Vegas.Game.PhaseRawBindingContribution

/-! # Actual timing strategy factors at chronological binding repair records -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
      scheduler).History]
  [∀ who, DecidableEq
    (((PhaseCount.onePacketMenu runtime leaks bounds).information
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw)) horizon
        scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (initial) horizon scheduler

local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

private theorem played_callback (who : Player) (current : (app).Control)
    (trace : (E).Trace (some current)) (acting : current.actor = some who) :
    some (current.execution.recall who, current.execution.observe app who) ∈
      (N).playedInformation who := by
  let history : (E).History := ⟨some current, trace⟩
  have running : ¬ (E).terminal history.state := by
    change ¬ (current.remaining = 0 ∧ current.actor = none)
    simp only [acting, reduceCtorEq, and_false, not_false_eq_true]
  have present := (N).mem_playedInformation (who := who) (history := history) running
  change ((menu).signals initial horizon scheduler).infoOf who trace ∈ _ at present
  rw [(menu).info initial horizon scheduler who trace] at present
  simpa only [ReactiveApplication.observe, acting, ↓reduceIte] using present

include maximal


/-- Genuine chronological sending pairs obey the uniform source-slot bound
under the SAME actual assembled timing strategy, for arbitrary pool weights. -/
theorem phaseBindingSendingPair.timing_record_ratio
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ (assessment.strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
            slotBounded agent))
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    (((strategy who first.1).map Subtype.val) (some first.2)).toReal ≤
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
        (((strategy who second.1).map Subtype.val) (some second.2)).toReal := by
  classical
  obtain ⟨firstControl, secondControl, _firstTrace, secondTrace, event, payload, binding,
    serial, preparation, evidence, result, original, _firstActor, secondActor, request,
      unsent, values, clear, originalMember, materialMember, rfl, rfl⟩ := paired
  let present := played_callback setup mode runtime leaks bounds plan horizon scheduler who
    secondControl secondTrace secondActor
  let agent : (N).InformationAgent (N).playedInformation :=
    ⟨who, ⟨some (secondControl.execution.recall who, secondControl.execution.observe app who),
      present⟩⟩
  let originalChoice : (N).Choice who (some (firstControl.execution.recall who,
      firstControl.execution.observe app who)) := ⟨some original, ⟨original, originalMember, rfl⟩⟩
  obtain ⟨replacement, selected, compared⟩ :=
    phaseTimingComponent_replacement_ratio_of_floor setup mode runtime leaks bounds plan maximal
      horizon scheduler bound wellFormed assessment mixed floor positive floored noise
        noiseNonnegative noiseSmall slotWeight slotPositive slotBounded agent (weights (pool agent))
          secondControl secondTrace rfl event payload binding request unsent values clear serial
            preparation evidence materialMember result
  have actual := assembled agent
  have firstAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective originalChoice
  have secondAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective replacement
  rw [selected] at secondAtom
  rw [firstAtom, secondAtom, actual]
  exact compared _ (strategy who _) originalChoice

/-- A selected raw-menu send retains its additional noise factor under the
actual timing mixture. Accepted source failures are not marked as raw noise. -/
theorem phaseRawBindingSendingPair.timing_raw_ratio
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ (assessment.strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
            slotBounded agent))
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseRawBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    1 ≤ (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor) ∧
    phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler noise who first ≤
      noise * ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
        (((strategy who second.1).map Subtype.val) (some second.2)).toReal := by
  classical
  obtain ⟨firstControl, secondControl, _firstTrace, secondTrace, event, payload, binding, serial,
    originalPreparation, originalEvidence, preparation, evidence, result, _firstActor, secondActor,
      request, unsent, values, _firstClear, clear, _firstMember, materialMember, rfl, rfl⟩ := paired
  let present := played_callback setup mode runtime leaks bounds plan horizon scheduler who
    secondControl secondTrace secondActor
  let agent : (N).InformationAgent (N).playedInformation :=
    ⟨who, ⟨some (secondControl.execution.recall who, secondControl.execution.observe app who),
      present⟩⟩
  obtain ⟨replacement, selected, compared⟩ :=
    phaseTimingComponent_replacement_ratio_of_floor setup mode runtime leaks bounds plan maximal
      horizon scheduler bound wellFormed assessment mixed floor positive floored noise
        noiseNonnegative noiseSmall slotWeight slotPositive slotBounded agent (weights (pool agent))
          secondControl secondTrace rfl event payload binding request unsent values clear serial
            preparation evidence materialMember result
  let inactive : (N).Choice who none := ⟨none, rfl⟩
  have target := compared none (PMF.pure inactive) inactive
  rw [PMF.pure_apply_self, ENNReal.toReal_one] at target
  have actual := assembled agent
  have atom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective replacement
  rw [selected] at atom
  rw [← actual, ← atom] at target
  have coefficientNonnegative :
      0 ≤ (bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor) := by positivity
  have targetUpper := pmf_toReal_apply_le_one ((strategy who agent.2.1).map Subtype.val)
    (some (phaseBindingResponse runtime leaks who event payload result serial))
  refine ⟨target.trans (mul_le_of_le_one_right coefficientNonnegative targetUpper), ?_⟩
  have rawUpper := pmf_toReal_apply_le_one
    (((menu).uniformPolicy initial horizon scheduler who
      (some (firstControl.execution.recall who, firstControl.execution.observe app who))).map
        Subtype.val)
    (some (⟨some ⟨⟨.commitment event (who, .prepared serial), originalPreparation⟩,
      originalEvidence⟩⟩ : (app).Action))
  have scaled := (mul_le_mul_of_nonneg_left rawUpper noiseNonnegative).trans
    (mul_le_mul_of_nonneg_left target noiseNonnegative)
  dsimp only [phaseRawMixtureAtom]
  nlinarith only [scaled]

/-- Genuine chronological binding waits obey the original source omission
floor under the SAME actual timing strategy; every later callback is retained. -/
theorem phaseBindingWaitingPair.timing_record_ratio
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ (assessment.strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le
            slotBounded agent))
    (finite : setup.program.FiniteBindingTypes)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (n : Nat) (sourceAt : assessment = approximation.sequence n)
    (capacity : horizon ≤ bounds.candidateCount)
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseBindingWaitingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    (((strategy who first.1).map Subtype.val) (some first.2)).toReal ≤
      (1 / ((1 - noise) * slotWeight * floor)) *
        (((strategy who second.1).map Subtype.val) (some second.2)).toReal := by
  classical
  subst assessment
  obtain ⟨event, payload, binding, firstControl, secondControl, _firstTrace, secondTrace,
    _firstActor, secondActor, _firstRequest, request, _firstUnsent, unsent, values, _firstClear,
      clear, rfl, rfl⟩ := paired
  let present := played_callback setup mode runtime leaks bounds plan horizon scheduler who
    secondControl secondTrace secondActor
  let agent : (N).InformationAgent (N).playedInformation :=
    ⟨who, ⟨some (secondControl.execution.recall who, secondControl.execution.observe app who),
      present⟩⟩
  let originalChoice : (N).Choice who (some (firstControl.execution.recall who,
      firstControl.execution.observe app who)) :=
    ⟨some ⟨none⟩, ⟨⟨none⟩, PhaseCount.silence_onePacket runtime leaks bounds _ _ _, rfl⟩⟩
  obtain ⟨silent, selected, _lower, compared⟩ :=
    phaseTimingComponent_waiting_ratio_of_floor setup mode runtime leaks bounds plan horizon
      scheduler bound finite wellFormed target approximation maximal n capacity floor positive
        floored noise noiseNonnegative noiseSmall slotWeight slotPositive slotBounded agent
          (weights (pool agent)) secondControl secondTrace secondActor rfl event payload binding
            request unsent values clear
  have actual := assembled agent
  have firstAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective originalChoice
  have secondAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective silent
  rw [selected] at secondAtom
  rw [firstAtom, secondAtom, actual]
  exact compared _ (strategy who _) originalChoice

end Vegas
