/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueRealization

/-! # Immutable source members retain the original silent atom -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

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
/-- Each fixed immutable value policy retains the BASE source silent atom.
Only the original auxiliary assessment is fully mixed; sparse members need not be. -/
theorem phaseTimingPlanPolicy_value_silence_base_of_history
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
      ⟨control.execution.application.attempt, event⟩)
    (plan : (p : Pool) → Parts p)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who member)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (control.execution.recall who) (control.execution.observe (app) who) ⟨none⟩ =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
          slotNonnegative slotBounded plan who (control.execution.recall who)
            (control.execution.observe (app) who) ⟨none⟩ := by
  let prior := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
  let family := fun value => phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon
    scheduler bound fallback wellFormed
      (setup.commitRecoveryValueAssessment wellFormed assessment who value) noise noiseNonnegative
        noiseBounded slotWeight slotNonnegative slotBounded plan who
          (control.execution.recall who) (control.execution.observe (app) who)
  have averaged := (phaseTimingPlanPolicy_value_readout_of_history setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed finite noise
      noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded who control trace
        active clear event payload binding request).2 plan
  have raw := (menu).toRawTrace initial horizon scheduler trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks runtimePlan inputs horizon
    scheduler raw
  have running : ¬ ((menu).protocol initial horizon scheduler).terminal (some control) := by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    rintro ⟨_, absent⟩
    rw [active] at absent
    cases absent
  have played := (N).mem_playedInformation (who := who)
    (history := ⟨some control, trace⟩) running
  have observed : (N).infoOf who trace =
      some (control.execution.recall who, control.execution.observe (app) who) :=
    ((menu).info initial horizon scheduler who trace).trans (by
      simp only [ReactiveApplication.observe, active, ite_true])
  rw [observed] at played
  have sourceTrace : ((app).protocol (setup.initialLaw.map fun draw =>
      PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) horizon scheduler).Trace
        (some control) := by
    have initialEq : initial = setup.initialLaw.map (fun draw =>
        PhaseRuntimeState.initial runtimePlan (encodeInputs draw)) := PMF.map_comp ..
    exact initialEq ▸ raw
  have constant (other) : family other ⟨none⟩ = family member ⟨none⟩ :=
    phaseTimingPlanPolicy_value_silence_of_history setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed assessment mixed noise noiseNonnegative noiseBounded
        slotWeight slotNonnegative slotBounded plan who other member runtimePlan maximal control
          sourceTrace valid clear event payload binding request played
  have atom := congrArg (fun law : PMF (app).Action => law ⟨none⟩) averaged
  change (prior.bind family) ⟨none⟩ = _ at atom
  rw [PMF.bind_apply] at atom
  simp_rw [constant] at atom
  simpa only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul] using atom

end Vegas
