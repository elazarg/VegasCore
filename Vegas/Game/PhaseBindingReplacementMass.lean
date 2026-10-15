/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePerturbation
import Vegas.Game.PhaseSourceSlotPolicyLaw
import Vegas.Game.PhaseRecoveryBindingChoice
import Vegas.Pending.PhaseBindingSlotSupport

/-! # Original source-result mass at every admissible fresh replacement slot -/

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

private theorem slotStrategy_atom (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (choice : ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).Choice who (some (past, view)))
    (response : (phaseApplication runtime leaks).Action) (selected : choice.1 = some response) :
    phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who (some (past, view)) choice =
      phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who past view
        response := by
  calc
    _ = (((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who (some (past, view))).map Subtype.val) choice.1) :=
      (pmf_map_apply_of_injective _ Subtype.val_injective choice).symm
    _ = ((phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        past view).map some) (some response) := by
      rw [phaseSourceSlotStrategy_map_val, selected]
      rfl
    _ = _ := pmf_map_apply_of_injective _ (Option.some_injective _) response

private theorem sourceSlotPolicy_fixed_mass (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) (result : PublicationResult (L.Val payload)) :
    (bounds.candidateCount : ENNReal)⁻¹ *
      ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) (result, false) ≤
      phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who) (control.execution.observe (phaseApplication runtime leaks)
          who) (phaseBindingResponse runtime leaks who event payload result serial) := by
  classical
  have cards : (PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).card ≤
      bounds.candidateCount := by
    unfold PhaseCount.phaseBindingSlots
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have inverse : (bounds.candidateCount : ENNReal)⁻¹ ≤
      ((PhaseCount.phaseBindingSlots runtime leaks bounds who event payload
        (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).card : ENNReal)⁻¹ :=
    ENNReal.inv_le_inv.mpr (by exact_mod_cast cards)
  exact (mul_le_mul' inverse le_rfl).trans
    (phaseSourceSlotPolicy_result_mass_of_history setup mode runtime leaks bounds wellFormed
      assessment who event payload binding (PhaseCount.onePacketMenu runtime leaks bounds)
      plan inputs horizon scheduler control trace request unsent values serial bounded fresh result)

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

include maximal

/-- Every typed result has positive original source mass at an actual clear
unsent binding. Its canonical response at any bounded fresh slot retains that
mass divided by the fixed wire capacity, times the independent slot weight. -/
theorem phaseSourcePerturbedStrategy_binding_mass (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (phaseApplication runtime leaks).Control) (trace : (E).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : control.execution.application.current.excluded = ∅)
    (serial : Nat) (bounded : serial < bounds.candidateCount)
    (fresh : control.execution.application.current.native.candidates.lookup
      (who, .prepared serial) = .fresh) (result : PublicationResult (L.Val payload))
    (choice : (N).Choice who (some (control.execution.recall who,
      control.execution.observe (phaseApplication runtime leaks) who)))
    (selected : choice.1 = some (phaseBindingResponse runtime leaks who event payload result
      serial)) :
    let sourceMass := ((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) (result, false)
    0 < sourceMass.toReal ∧
      (1 - noise) * slotWeight * (sourceMass.toReal / (bounds.candidateCount : ℝ)) ≤
        ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
          wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded who (some (control.execution.recall who,
              control.execution.observe (phaseApplication runtime leaks) who))) choice).toReal := by
  intro sourceMass
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physicalTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have supported := phaseRecoveryBindingChoice_supported_of_history setup mode runtime leaks
    wellFormed assessment mixed plan maximal horizon scheduler physicalTrace who event payload
      binding request clear result
  have positive : 0 < sourceMass.toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff _ _).mp supported) (PMF.apply_ne_top _ _)
  have typedTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have rawLower := sourceSlotPolicy_fixed_mass setup mode runtime leaks bounds wellFormed
    assessment who event payload binding plan inputs horizon scheduler control typedTrace request
      unsent values serial bounded fresh result
  have realLower := ENNReal.toReal_mono (PMF.apply_ne_top _ _) rawLower
  have atom := slotStrategy_atom setup mode runtime leaks bounds wellFormed assessment initial
    horizon scheduler who (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) choice _ selected
  have slotLower : sourceMass.toReal / (bounds.candidateCount : ℝ) ≤
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who (some (control.execution.recall who,
          control.execution.observe (phaseApplication runtime leaks) who))) choice).toReal := by
    rw [atom]
    simpa only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast, sourceMass,
      div_eq_mul_inv, mul_comm] using realLower
  refine ⟨positive, ?_⟩
  exact (mul_le_mul_of_nonneg_left slotLower
    (mul_nonneg (sub_nonneg.mpr noiseBounded) slotNonnegative)).trans
      (phaseSourcePerturbedStrategy_ge_slot setup mode runtime leaks bounds initial horizon
        scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded who _ choice)

/-- Any actually permitted raw binding names a slot with a canonical replacement
of every typed result. The replacement is an actual finite-menu choice whose
original perturbed mass has the fixed-capacity bound; preparation and evidence
of the raw response need not be canonical or well typed. -/
theorem phaseSourcePerturbedStrategy_replacement_mass (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (control : (phaseApplication runtime leaks).Control) (trace : (E).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : control.execution.application.current.excluded = ∅)
    (serial : Nat) (preparation : Option (Raw L))
    (evidence : EvidenceRequest (serviceGraph setup mode))
    (member : (⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        who (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who))
    (result : PublicationResult (L.Val payload)) :
    let sourceMass := ((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) (result, false)
    ∃ choice : (N).Choice who (some (control.execution.recall who,
        control.execution.observe (phaseApplication runtime leaks) who)),
      choice.1 = some (phaseBindingResponse runtime leaks who event payload result serial) ∧
      0 < sourceMass.toReal ∧
      (1 - noise) * slotWeight * (sourceMass.toReal / (bounds.candidateCount : ℝ)) ≤
        ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
          wellFormed assessment noise noiseNonnegative noiseBounded slotWeight slotNonnegative
            slotBounded who (some (control.execution.recall who,
              control.execution.observe (phaseApplication runtime leaks) who))) choice).toReal := by
  intro sourceMass
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have typedTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨bounded, fresh, _eligible⟩ := PhaseCount.binding_slot_mem_of_onePacket runtime leaks
    bounds plan inputs horizon scheduler typedTrace who event payload binding request unsent
      values serial preparation evidence member
  have physicalTrace := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler trace
  have sourceSupported := phaseRecoveryBindingChoice_supported_of_history setup mode runtime leaks
    wellFormed assessment mixed plan maximal horizon scheduler physicalTrace who event payload
      binding request clear result
  let response := phaseBindingResponse runtime leaks who event payload result serial
  have rawLower := sourceSlotPolicy_fixed_mass setup mode runtime leaks bounds wellFormed
    assessment who event payload binding plan inputs horizon scheduler control typedTrace request
      unsent values serial bounded fresh result
  have positive : 0 < (bounds.candidateCount : ENNReal)⁻¹ * sourceMass := by
    apply pos_iff_ne_zero.mpr
    exact mul_ne_zero (by simp) ((PMF.mem_support_iff _ _).mp sourceSupported)
  have rawSupported : response ∈ (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed
      assessment who (control.execution.recall who)
        (control.execution.observe (phaseApplication runtime leaks) who)).support :=
    (PMF.apply_pos_iff _ _).mp (positive.trans_le rawLower)
  have mapped : some response ∈
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who (some (control.execution.recall who,
          control.execution.observe (phaseApplication runtime leaks) who))).map
            Subtype.val).support :=
    by
      rw [phaseSourceSlotStrategy_map_val]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨response, rawSupported, rfl⟩
  obtain ⟨choice, _supported, selected⟩ := (PMF.mem_support_map_iff _ _ _).mp mapped
  refine ⟨choice, selected, ?_⟩
  exact phaseSourcePerturbedStrategy_binding_mass setup mode runtime leaks bounds plan maximal
    horizon scheduler wellFormed assessment mixed noise noiseNonnegative noiseBounded slotWeight
    slotNonnegative slotBounded control trace who event payload binding request unsent values clear
    serial bounded fresh result choice selected

end Vegas
