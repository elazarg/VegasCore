/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairResponseFactor
import Vegas.Game.PhaseTimingOpeningResponse
import Vegas.Game.PhaseTimingKeyProperties
import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPoolObservation

/-! # Actual timing mixture opening laws along chronological repair -/

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



/-- Earlier opening records have identical laws under the actual assembled
timing strategy. Genuine chronological repair supplies the shared complete key,
and the original common pool weights are retained, including globally silent
WAIT options and all raw-menu evidence aliases. -/
theorem phaseOpeningResponsePair.timing_record_eq
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : (p : Pool) → PMF (Parts p))
    (strategy : ∀ who, (N).BehavioralPolicy who)
    (assembled : ∀ agent : (N).InformationAgent (N).playedInformation,
      strategy agent.1 agent.2.1 = (weights (pool agent)).bind
        (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
          wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded agent))
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseOpeningResponsePair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    ((strategy who first.1).map Subtype.val) (some first.2) =
      ((strategy who second.1).map Subtype.val) (some second.2) := by
  classical
  obtain ⟨remaining, original, repaired, memory, frame, leftTrace, rightTrace, final, finalTrace,
    isPrefix, event, payload, binding, checks, outputEq, codeEq, node, bindingEvent, bindingOwner,
      bindingPayload, bindingOutput, action, clear, leftRequest, rightRequest, leftUnsent,
        rightUnsent, values, requested, rfl, rfl, sameKey⟩ := paired
  let firstAgent : (N).InformationAgent (N).playedInformation :=
    ⟨who, ⟨some (original.recall who, original.observe app who),
      played_callback setup mode runtime leaks bounds plan horizon scheduler who _ leftTrace rfl⟩⟩
  let secondAgent : (N).InformationAgent (N).playedInformation :=
    ⟨who, ⟨some (repaired.recall who, repaired.observe app who),
      played_callback setup mode runtime leaks bounds plan horizon scheduler who _ rightTrace rfl⟩⟩
  have notFree : ¬ PhasePublicExclusion setup mode runtime leaks firstAgent.2.1 := by
    rintro ⟨past, view, equal, excluded⟩
    have same := congrArg Prod.snd (Option.some.inj equal)
    change original.observe app who = view at same
    rw [← same] at excluded
    exact excluded frame.clearOriginal
  have secondNotFree : ¬ PhasePublicExclusion setup mode runtime leaks secondAgent.2.1 := by
    rintro ⟨past, view, equal, excluded⟩
    have same := congrArg Prod.snd (Option.some.inj equal)
    change repaired.observe app who = view at same
    rw [← same] at excluded
    exact excluded frame.clearRepaired
  have classified := phaseUnprotected_iff_of_timingKey_eq runtime leaks bound who
    (original.recall who) (repaired.recall who) (original.observe app who)
      (repaired.observe app who) sameKey
  have samePool : pool firstAgent = pool secondAgent :=
    freeKeyedPool_eq_of_not_free notFree secondNotFree classified sameKey
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  obtain ⟨left, right, finalHistory, path⟩ :
      ∃ (left : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
            (some ⟨remaining, some who, original⟩))
        (_right : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
            (some ⟨remaining, some who, repaired⟩))
        (last : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
          (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some final)),
        TracePrefix left last := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact ⟨leftTrace, rightTrace, finalTrace, isPrefix⟩
  have laws (raw : ℝ) (rawNonnegative : 0 ≤ raw) (rawBounded : raw ≤ 1)
      (slot : ℝ) (slotNonnegative : 0 ≤ slot) (slotBounded : slot ≤ 1) :
      ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment raw rawNonnegative rawBounded slot slotNonnegative slotBounded
          who firstAgent.2.1).map Subtype.val) =
      ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment raw rawNonnegative rawBounded slot slotNonnegative slotBounded
          who secondAgent.2.1).map Subtype.val) := by
    have compared := phaseSourcePerturbedStrategy_opening_raw_eq_before_binding setup mode runtime
      leaks bounds plan inputs horizon scheduler wellFormed assessment maximal who remaining
        original repaired memory frame left right final finalHistory path clear event payload
          binding checks outputEq codeEq node leftRequest rightRequest leftUnsent rightUnsent
            values bindingEvent bindingOwner bindingPayload bindingOutput requested slot
              slotNonnegative slotBounded raw rawNonnegative rawBounded
    dsimp only [inputs] at compared
    rw [PMF.map_comp] at compared
    exact compared.1
  have uniformLaw := laws 1 zero_le_one le_rfl 0 le_rfl zero_le_one
  have slotLaw := laws 0 le_rfl zero_le_one 1 zero_le_one le_rfl
  have sourceLaw := laws 0 le_rfl zero_le_one 0 le_rfl zero_le_one
  simp only [phaseSourcePerturbedStrategy, mix_one] at uniformLaw
  simp only [phaseSourcePerturbedStrategy, mix_zero, mix_one] at slotLaw
  simp only [phaseSourcePerturbedStrategy, mix_zero] at sourceLaw
  obtain ⟨leftDraw, leftValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler ((menu).toRawTrace _ horizon scheduler left)
  obtain ⟨rightDraw, rightValid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler ((menu).toRawTrace _ horizon scheduler right)
  have timingLaw (option : LateOption bounds.candidateCount) :
      ((phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option who firstAgent.2.1).map Subtype.val) =
      ((phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option who secondAgent.2.1).map Subtype.val) := by
    change ((phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option who (some (original.recall who, original.observe app who))).map
          Subtype.val) =
      ((phaseSourceTimingStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler option who (some (repaired.recall who, repaired.observe app who))).map
          Subtype.val)
    rw [phaseSourceTimingStrategy_map_val, phaseSourceTimingStrategy_map_val]
    cases option with
    | none => rfl
    | some serial =>
      rw [phaseSourceTimingPolicy_opening_eq_source setup mode runtime leaks bounds wellFormed
        assessment serial original leftValid who event payload binding checks outputEq codeEq
          leftRequest,
        phaseSourceTimingPolicy_opening_eq_source setup mode runtime leaks bounds wellFormed
          assessment serial repaired rightValid who event payload binding checks outputEq codeEq
            rightRequest]
      simpa only [firstAgent, secondAgent, phaseSourceStrategy_map_val] using sourceLaw
  have keyedLaw (option : LateOption bounds.candidateCount) :
      ((phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded who firstAgent.2.1 option).map Subtype.val) =
      ((phaseSourceTimingComponent setup mode runtime leaks bounds initial horizon scheduler
        wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
          slotBounded who secondAgent.2.1 option).map Subtype.val) := by
    simp only [phaseSourceTimingComponent, mix_map]
    rw [uniformLaw, slotLaw, timingLaw]
  have compared : ((strategy who firstAgent.2.1).map Subtype.val) =
      ((strategy who secondAgent.2.1).map Subtype.val) := by
    rw [assembled firstAgent, assembled secondAgent]
    unfold phaseTimingComponent
    exact @bind_freeKeyedComponent_map_eq_of_not_free Player E N inferInstance inferInstance
      _ _ (Option (app).Action) _ _ _
      (fun agent choice => mix noise noiseNonnegative noiseBounded
        ((menu).uniformPolicy initial horizon scheduler agent.1 agent.2.1) (PMF.pure choice))
      (fun agent => phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
        scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent.1 agent.2.1)
      (fun agent option => phaseSourceTimingComponent setup mode runtime leaks bounds initial
        horizon scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded agent.1 agent.2.1 option) weights
      (fun agent (choice : (N).Choice agent.1 agent.2.1) => (choice.1 : Option (app).Action))
        firstAgent secondAgent notFree samePool
        (laws noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded) keyedLaw
  exact congrArg (fun law => law (some action)) compared

end Vegas
