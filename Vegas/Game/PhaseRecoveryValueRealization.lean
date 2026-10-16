/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueJoint

/-! # Original source-policy mixtures realize the actual assembled callback -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

private theorem average_mix {Index Action : Type} (prior : PMF Index)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (first second : Index → PMF Action) :
    prior.bind (fun index => mix weight nonnegative bounded (first index) (second index)) =
      mix weight nonnegative bounded (prior.bind first) (prior.bind second) := by
  ext action
  rw [PMF.bind_apply, mix_apply, PMF.bind_apply, PMF.bind_apply]
  rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← ENNReal.tsum_add]
  apply tsum_congr
  intro index
  rw [mix_apply]
  ring

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial runtimePlan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial runtimePlan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound

open Classical in
/-- Averaging the SAME original global source-policy prior recovers the
literal complete finite timing-plan response at an authentic clear binding.
The original omission, selected WAIT/serial, independent slot and RAW tiers
are all retained; no conditional callback law is assumed. -/
theorem phaseTimingPlanPolicy_value_readout_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩) :
    let decoded := phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (app) who)
    (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).map
        (fun member => member decoded) =
      setup.commitRecoveryNonmissingSourcePolicy wellFormed assessment.strategy who decoded ∧
    ∀ plan : (p : Pool) → Parts p,
      (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).bind
        (fun member => phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
          scheduler bound fallback wellFormed
            (setup.commitRecoveryValueAssessment wellFormed assessment who member) noise
              noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
                (control.execution.recall who) (control.execution.observe (app) who)) =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded plan who (control.execution.recall who)
            (control.execution.observe (app) who) := by
  let prior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
  let changed := fun member => setup.commitRecoveryValueAssessment wellFormed assessment who member
  let past := control.execution.recall who
  let view := control.execution.observe (app) who
  let decoded := phaseSourceView? setup mode runtime leaks who event view
  let information := setup.commitRecoveryClearInformation wellFormed who decoded
  let choices := fun member => (changed member).strategy who information
  let original := assessment.strategy who information
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, absent⟩
    rw [active] at absent
    cases absent
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some control, trace⟩) running
  have observed : (N).infoOf who trace = some (past, view) :=
    ((menu).info initial horizon scheduler who trace).trans (by
      simp only [ReactiveApplication.observe, active, ite_true]
      rfl)
  rw [observed] at played
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  have sourceTrace : ((app).protocol (setup.initialLaw.map fun draw =>
      PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) horizon scheduler).Trace
        (some control) := by
    have initialEq : initial = setup.initialLaw.map (fun draw =>
        PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) := PMF.map_comp ..
    exact initialEq ▸ raw
  obtain ⟨source, history, sourceClear, _generation, actor, same⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks runtimePlan maximal horizon scheduler
      sourceTrace who event payload binding request.2.2.1 clear
  have sourceRunning : ¬ setup.commitRecoveryProtocol.terminal (some source) := by
    intro stopped
    have absent := ProtocolState.terminal_actor_none who setup.program source.point stopped
    rw [ProtocolState.actor_observe_eq, actor] at absent
    cases absent
  have averaged := setup.commitRecoveryValuePlan_clear_law finite wellFormed assessment mixed
    ⟨some source, history⟩ sourceClear sourceRunning who
  change decoded = setup.commitRecoveryPrivate who (some source) at same
  rw [← same] at averaged
  have average : prior.bind choices = original := by
    simpa only [prior, choices, changed, information, Setup.commitRecoveryValueAssessment,
      InformationModel.BehavioralAssessment.ofStrategy, Function.update_self] using averaged
  have readout := setup.commitRecoveryValuePlan_clear_readout finite wellFormed
    assessment.strategy ⟨some source, history⟩ sourceClear sourceRunning who
  rw [← same] at readout
  refine ⟨readout, ?_⟩
  intro plan
  have slotAverage : prior.bind (fun member => phaseRecoverySlotPolicy setup mode runtime leaks
      bounds wellFormed (changed member) who event payload binding past view) =
    phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload binding past view := by
    let encode := fun choice : setup.commitRecoveryModel.Choice who information =>
      let data := phaseRecoveryBindingData setup mode event who payload binding choice.val
      if data.2 then PMF.pure ⟨none⟩ else PhaseCount.phaseBindingSlotPolicy runtime leaks bounds who
        event payload (fun _ _ => PMF.pure data.1) past view
    change prior.bind (fun member => (choices member).bind encode) = original.bind encode
    exact (PMF.bind_bind prior choices encode).symm.trans
      (congrArg (fun law => law.bind encode) average)
  have canonicalAverage : prior.bind (fun member => phaseRecoveryBindingPolicy setup mode runtime
      leaks bounds wellFormed (changed member) who event payload binding past view) =
    phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed assessment who event
      payload binding past view := by
    cases selected : reactiveFreshSlot view.application.1 with
    | none => simp only [phaseRecoveryBindingPolicy, selected, PMF.bind_const]
    | some serial =>
        by_cases guard : ∀ move, phaseRecoveryBindingResponse setup mode runtime leaks who event
          payload binding serial move ∈ PhaseCount.onePacketActions runtime leaks bounds who past
            view
        · simp only [phaseRecoveryBindingPolicy, selected, ite_eq_left guard]
          let encode := fun choice : setup.commitRecoveryModel.Choice who information =>
            phaseRecoveryBindingResponse setup mode runtime leaks who event payload binding serial
              choice.val
          change prior.bind (fun member => (choices member).map encode) = original.map encode
          exact (PMF.map_bind prior choices encode).symm.trans
            (congrArg (PMF.map encode) average)
        · simp only [phaseRecoveryBindingPolicy, selected, ite_eq_right guard, PMF.bind_const]
  have timingAverage (option : LateOption bounds.candidateCount) :
      prior.bind (fun member => phaseRecoveryTimingPolicy setup mode runtime leaks bounds
        wellFormed (changed member) who event payload binding option past view) =
      phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment who event
        payload binding option past view := by
    let encode := fun choice : setup.commitRecoveryModel.Choice who information =>
      phaseBindingTimingResponse setup mode runtime leaks bounds who event payload option past view
        (phaseRecoveryBindingData setup mode event who payload binding choice.val)
    have normalized (profile : setup.commitRecoveryModel.BehavioralAssessment) :
        phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed profile who event
            payload binding option past view =
          (profile.strategy who information).map encode := PMF.map_comp ..
    have first : prior.bind (fun member => phaseRecoveryTimingPolicy setup mode runtime leaks
        bounds wellFormed (changed member) who event payload binding option past view) =
      prior.bind (fun member => (choices member).map encode) :=
        congrArg (PMF.bind prior) (funext fun member => normalized (changed member))
    exact first.trans ((PMF.map_bind prior choices encode).symm.trans
      ((congrArg (PMF.map encode) average).trans (normalized assessment).symm))
  obtain ⟨selected, response⟩ := phaseTimingPlanPolicy_binding_readout setup mode runtime leaks
    bounds initial horizon scheduler bound fallback wellFormed noise noiseNonnegative noiseBounded
      slotWeight slotNonnegative slotBounded plan who control.execution valid clear event payload
        binding request played
  let uniform := ((menu).uniformPolicy initial horizon scheduler who (some (past, view))).map
    (fun choice => choice.1.getD ⟨none⟩)
  let rest := fun profile : setup.commitRecoveryModel.BehavioralAssessment =>
    mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed profile who event payload
        binding past view)
      (selected.elim
        (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed profile who
          event payload binding past view)
        (fun option => phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed profile
          who event payload binding option past view))
  have restAverage : prior.bind (fun member => rest (changed member)) = rest assessment := by
    dsimp only [rest]
    rw [average_mix, slotAverage]
    congr 1
    clear rest response
    cases selected with
    | none => exact canonicalAverage
    | some option => exact timingAverage option
  have evaluated (profile : setup.commitRecoveryModel.BehavioralAssessment) :
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
          fallback wellFormed profile noise noiseNonnegative noiseBounded slotWeight
            slotNonnegative slotBounded plan who past view =
        mix noise noiseNonnegative noiseBounded uniform (rest profile) := by
    cases selected <;> exact response profile
  calc
    _ = prior.bind (fun member => mix noise noiseNonnegative noiseBounded uniform
        (rest (changed member))) :=
      congrArg (PMF.bind prior) (funext fun member => evaluated (changed member))
    _ = mix noise noiseNonnegative noiseBounded (prior.bind fun _ => uniform)
        (prior.bind fun member => rest (changed member)) := average_mix ..
    _ = mix noise noiseNonnegative noiseBounded uniform (rest assessment) := by
      rw [PMF.bind_const, restAverage]
    _ = _ := (evaluated assessment).symm

end Vegas
