/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServiceAliases
import Vegas.Pending.PhaseBindingSlotSupport

/-! # Ordinary mass at the fresh slots of actual counted exploration

The selected source-domain kernel retains every typed value at every actual
fresh slot. Operational classes sum their original request aliases before
comparison; a particular raw request need not have an ordinary atom.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

omit [Fintype Player] in
private theorem atom_le_operational_atom (normal : (app).SubmissionNormalization)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (law : PMF (app).Action) (response : (app).Action) :
    (law response).toReal <=
      ((law.map (normal.action who past view)) (normal.action who past view response)).toReal := by
  classical
  apply ENNReal.toReal_mono (PMF.apply_ne_top _ _)
  rw [PMF.map_apply]
  simpa only [ite_eq_left rfl, ite_true] using
    (ENNReal.le_tsum (f := fun action =>
      if normal.action who past view response = normal.action who past view action
      then law action else 0) response)

section Policy

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (values : ∀ who info, PMF (setup.CommitRecoveryValueChoice who info))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (failureNonnegative : 0 ≤ failure)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (sendFloor : failure + 2 * timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)

local notation "domain" => phaseObservableDomainValues setup mode runtime leaks plan values
local notation "selected" => phaseCountServicePolicy setup mode runtime leaks bounds domain choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded
  slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded

include plan values choose failure timing failureNonnegative firstNonnegative firstBounded
  timingNonnegative timingBounded sendFloor slotWeight slotNonnegative slotBounded
  rawWeight rawNonnegative rawBounded

/-- At an actual unsent binding, every bounded fresh slot retains the SAME
queried domain mass. Neither a raw evidence alias nor a menu-size equality is
assumed. The first-only failure and local timing coefficients remain explicit. -/
theorem phaseCountServicePolicy_binding_slot_mass
    (inputs : PMF (graph).Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) (value : L.Val payload) :
    let past := control.execution.recall who
    let view := control.execution.observe app who
    (1 - rawWeight) * timing * slotWeight *
        (((domain who event payload binding past view) value).toReal /
          (bounds.candidateCount : ℝ)) ≤
      (selected who past view
        (phaseBindingResponse runtime leaks who event payload (.success value) serial)).toReal := by
  classical
  intro past view
  let results := fun past view =>
    (domain who event payload binding past view).map PublicationResult.success
  let response := phaseBindingResponse runtime leaks who event payload (.success value) serial
  let encoder := PhaseCount.bindingResultEncoder runtime leaks bounds who event payload results
    slotWeight slotNonnegative slotBounded past view
  have eligible := PhaseCount.mem_phaseBindingSlots_of_history runtime leaks bounds
    (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler control trace
      who event payload binding request unsent catalogue serial bounded fresh
  have lower := ENNReal.toReal_mono (PMF.apply_ne_top _ _)
    (PhaseCount.phaseBindingSlotPolicy_bounded_mass runtime leaks bounds who event payload
      results past view serial eligible (.success value))
  have resultMass : (results past view) (.success value) =
      (domain who event payload binding past view) value :=
    pmf_map_apply_of_injective _ (fun _ _ same => PublicationResult.success.inj same) value
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, resultMass] at lower
  have slotLower : slotWeight *
      (((domain who event payload binding past view) value).toReal /
        (bounds.candidateCount : ℝ)) ≤ (encoder response).toReal := by
    have multiplied := mul_le_mul_of_nonneg_left lower slotNonnegative
    dsimp only [encoder, PhaseCount.bindingResultEncoder]
    rw [mix_apply_toReal]
    have remaining := mul_nonneg (sub_nonneg.mpr slotBounded)
      (ENNReal.toReal_nonneg (a := PhaseCount.phaseBindingPolicy runtime leaks bounds who
        event payload results past view response))
    simpa only [div_eq_mul_inv, mul_comm] using multiplied.trans (le_add_of_nonneg_right remaining)
  let base := PhaseCount.bindingServiceBase runtime leaks bounds who
    ⟨view.application.2.attempt, event⟩ payload results
    (choose who ⟨view.application.2.attempt, event⟩) failure timing firstNonnegative firstBounded
    timingNonnegative timingBounded slotWeight slotNonnegative slotBounded past view
  have baseLower : timing * (encoder response).toReal ≤ (base response).toReal := by
    have positive := ENNReal.toReal_nonneg (a := encoder response)
    have silent := ENNReal.toReal_nonneg (a := (PMF.pure (⟨none⟩ : (app).Action)) response)
    dsimp only [base, PhaseCount.bindingServiceBase]
    split
    · rw [mix_apply_toReal]
      have bound := mul_le_mul_of_nonneg_right
        (show timing ≤ 1 - (failure + timing) by linarith) positive
      nlinarith [mul_nonneg firstNonnegative silent]
    · split
      · rw [mix_apply_toReal]
        have bound := mul_le_mul_of_nonneg_right
          (show timing ≤ 1 - timing by linarith) positive
        nlinarith [mul_nonneg timingNonnegative silent]
      · rw [mix_apply_toReal]
        exact le_add_of_nonneg_right
          (mul_nonneg (sub_nonneg.mpr timingBounded) silent)
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace)
  rw [phaseCountServicePolicy_binding setup mode runtime leaks bounds domain choose failure timing
    firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
    slotBounded rawWeight rawNonnegative rawBounded control.execution valid who event payload
    binding request]
  change _ ≤ (PhaseCount.bindingServiceReference runtime leaks bounds who
    ⟨view.application.2.attempt, event⟩ payload results
    (choose who ⟨view.application.2.attempt, event⟩) failure timing firstNonnegative firstBounded
    timingNonnegative timingBounded slotWeight slotNonnegative slotBounded rawWeight
    rawNonnegative rawBounded past view response).toReal
  rw [PhaseCount.bindingServiceReference, mix_apply_toReal]
  have ordinary := (mul_le_mul_of_nonneg_left slotLower timingNonnegative).trans baseLower
  have retained := mul_le_mul_of_nonneg_left ordinary (sub_nonneg.mpr rawBounded)
  have raw := mul_nonneg rawNonnegative (ENNReal.toReal_nonneg
    (a := PhaseCount.countedSendLaw runtime leaks bounds who past view response))
  nlinarith

/-- Grouping the actual request aliases retains the same lower mass. This is
an operational-class estimate, including aliases with zero ordinary raw mass. -/
theorem phaseCountServicePolicy_binding_operational_mass
    (normal : (app).SubmissionNormalization)
    (inputs : PMF (graph).Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) (value : L.Val payload) :
    let past := control.execution.recall who
    let view := control.execution.observe app who
    let response := phaseBindingResponse runtime leaks who event payload (.success value) serial
    (1 - rawWeight) * timing * slotWeight *
        (((domain who event payload binding past view) value).toReal /
          (bounds.candidateCount : ℝ)) ≤
      (((selected who past view).map (normal.action who past view))
        (normal.action who past view response)).toReal := by
  intro past view response
  exact (phaseCountServicePolicy_binding_slot_mass setup mode runtime leaks bounds plan values
    choose failure timing failureNonnegative firstNonnegative firstBounded timingNonnegative
    timingBounded sendFloor slotWeight slotNonnegative slotBounded rawWeight rawNonnegative
    rawBounded inputs horizon scheduler control trace who event payload binding request unsent
    catalogue serial bounded fresh value).trans
      (atom_le_operational_atom setup mode runtime leaks normal who past view _ response)

/-- Every actual permitted RAW binding admits an ordinary replacement at its
own fresh slot. The numerator is the SUM of original RAW request aliases;
only the genuine source-domain atom floor appears in the denominator. -/
theorem phaseCountServicePolicy_binding_raw_ratio
    (normal : (app).SubmissionNormalization)
    (inputs : PMF (graph).Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (preparation : Option (Raw L)) (evidence : EvidenceRequest (graph))
    (permitted : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (control.execution.recall who) (control.execution.observe app who))
    (value : L.Val payload) (floor : ℝ) (floorPositive : 0 < floor)
    (timingPositive : 0 < timing) (slotPositive : 0 < slotWeight) (rawSmall : rawWeight < 1)
    (floored : floor ≤ ((domain who event payload binding (control.execution.recall who)
      (control.execution.observe app who)) value).toReal) :
    let past := control.execution.recall who
    let view := control.execution.observe app who
    let original : (app).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩
    let replacement := phaseBindingResponse runtime leaks who event payload (.success value) serial
    rawWeight * (((PhaseCount.countedSendLaw runtime leaks bounds who past view).map
        (normal.action who past view)) (normal.action who past view original)).toReal ≤
      (rawWeight * (bounds.candidateCount : ℝ) /
        ((1 - rawWeight) * timing * slotWeight * floor)) *
        (((selected who past view).map (normal.action who past view))
          (normal.action who past view replacement)).toReal := by
  intro past view original replacement
  obtain ⟨bounded, fresh, _eligible⟩ := PhaseCount.binding_slot_mem_of_onePacket runtime leaks
    bounds plan inputs horizon scheduler trace who event payload binding request unsent catalogue
      serial preparation evidence permitted
  have capacity : 0 < (bounds.candidateCount : ℝ) := by
    exact_mod_cast (show 0 < bounds.candidateCount by omega)
  have denominator : 0 < (1 - rawWeight) * timing * slotWeight * floor :=
    mul_pos (mul_pos (mul_pos (sub_pos.mpr rawSmall) timingPositive) slotPositive) floorPositive
  have lower := phaseCountServicePolicy_binding_operational_mass setup mode runtime leaks bounds
    plan values choose failure timing failureNonnegative firstNonnegative firstBounded
    timingNonnegative timingBounded sendFloor slotWeight slotNonnegative slotBounded rawWeight
    rawNonnegative rawBounded normal inputs horizon scheduler control trace who event payload
    binding request unsent catalogue serial bounded fresh value
  have floorLower : ((1 - rawWeight) * timing * slotWeight * floor) /
      (bounds.candidateCount : ℝ) ≤
      (((selected who past view).map (normal.action who past view))
        (normal.action who past view replacement)).toReal := by
    apply le_trans ?_ lower
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left
      (div_le_div_of_nonneg_right floored capacity.le)
      (mul_nonneg (mul_nonneg (sub_nonneg.mpr rawBounded) timingNonnegative) slotNonnegative)
  have upper := mul_le_mul_of_nonneg_left (pmf_toReal_apply_le_one
    ((PhaseCount.countedSendLaw runtime leaks bounds who past view).map
      (normal.action who past view)) (normal.action who past view original)) rawNonnegative
  rw [mul_one] at upper
  apply upper.trans
  have scaled := mul_le_mul_of_nonneg_left floorLower
    (div_nonneg (mul_nonneg rawNonnegative capacity.le) denominator.le)
  have identity : rawWeight * (bounds.candidateCount : ℝ) /
      ((1 - rawWeight) * timing * slotWeight * floor) *
        (((1 - rawWeight) * timing * slotWeight * floor) /
          (bounds.candidateCount : ℝ)) = rawWeight := by
    field_simp [ne_of_gt (sub_pos.mpr rawSmall)]
  rwa [identity] at scaled

/-- With the selected cubic RAW and independent slot weights, the actual
operational-class replacement ratio is at most twice capacity times timing
over the original source floor. No raw-menu cardinality enters this rate. -/
theorem phaseCountServicePolicy_binding_cubic_raw_ratio
    (normal : (app).SubmissionNormalization)
    (inputs : PMF (graph).Inputs) (horizon : Nat) (scheduler : (app).Scheduler)
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (graph).EventId) (payload : L.Ty)
    (binding : (graph).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (catalogue : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (preparation : Option (Raw L)) (evidence : EvidenceRequest (graph))
    (permitted : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (control.execution.recall who) (control.execution.observe app who))
    (value : L.Val payload) (floor : ℝ) (floorPositive : 0 < floor)
    (timingPositive : 0 < timing) (slotPositive : 0 < slotWeight) (rawSmall : rawWeight < 1)
    (slotEq : slotWeight = timing) (rawEq : rawWeight = timing ^ 3)
    (rawHalf : rawWeight ≤ 1 / 2)
    (floored : floor ≤ ((domain who event payload binding (control.execution.recall who)
      (control.execution.observe app who)) value).toReal) :
    let past := control.execution.recall who
    let view := control.execution.observe app who
    let original : (app).Action :=
      ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩
    let replacement := phaseBindingResponse runtime leaks who event payload (.success value) serial
    rawWeight * (((PhaseCount.countedSendLaw runtime leaks bounds who past view).map
        (normal.action who past view)) (normal.action who past view original)).toReal ≤
      (2 * (bounds.candidateCount : ℝ) * timing / floor) *
        (((selected who past view).map (normal.action who past view))
          (normal.action who past view replacement)).toReal := by
  intro past view original replacement
  have compared := phaseCountServicePolicy_binding_raw_ratio setup mode runtime leaks bounds
    plan values choose failure timing failureNonnegative firstNonnegative firstBounded
    timingNonnegative timingBounded sendFloor slotWeight slotNonnegative slotBounded rawWeight
    rawNonnegative rawBounded normal inputs horizon scheduler control trace who event payload
    binding request unsent catalogue serial preparation evidence permitted value floor floorPositive
    timingPositive slotPositive rawSmall floored
  apply compared.trans
  apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
  have retained : 0 < 1 - rawWeight := sub_pos.mpr rawSmall
  have reduced : rawWeight * (bounds.candidateCount : ℝ) /
      ((1 - rawWeight) * timing * slotWeight * floor) =
        ((bounds.candidateCount : ℝ) * timing) / ((1 - rawWeight) * floor) := by
    rw [slotEq, rawEq]
    field_simp [ne_of_gt timingPositive, ne_of_gt floorPositive,
      ne_of_gt (show 0 < 1 - timing ^ 3 by simpa only [rawEq] using retained)]
  rw [reduced]
  apply (div_le_div_iff₀ (mul_pos retained floorPositive) floorPositive).mpr
  have nonnegative := mul_nonneg (mul_nonneg (Nat.cast_nonneg bounds.candidateCount)
    timingNonnegative) floorPositive.le
  have scaled := mul_le_mul_of_nonneg_right
    (show 1 ≤ 2 * (1 - rawWeight) by linarith) nonnegative
  nlinarith

end Policy

end Vegas
