/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingSwapWaiting
import Vegas.Game.PhaseTimingSwapCallback
import Vegas.Game.PhaseRecoveryValueLikelihood

/-! # Actual nonsend likelihood factors across guarded hidden swaps -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [histories : Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
      scheduler).History]
  [infos : ∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
      scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "initial" => PMF.map (PhaseRuntimeState.initial plan)
  (PMF.map encodeInputs setup.initialLaw)
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
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

local instance phaseTimingSwapRecallPoolFintype : Fintype Pool := Fintype.ofFinite _

omit histories infos in
private theorem silence_of_binding_nonsend
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (who : Player) (control : (app).Control) (trace : (E).Trace (some control))
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (response : (app).Action)
    (offered : response ∈ (menu).actions who (control.execution.recall who)
      (control.execution.observe app who))
    (nonsend : ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler
      who (some (control.execution.recall who, control.execution.observe app who), response)) :
    response = ⟨none⟩ := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      have raw := (menu).toRawTrace initial horizon scheduler trace
      obtain ⟨phase, remaining, installed, committing, _inside⟩ :=
        phase_ready_binding_phase runtime leaks plan
          (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler raw
            who event payload binding request.2.2.1
      obtain ⟨sentEvent, serial, named⟩ := PhaseCount.onePacket_commitment_shape runtime
        leaks bounds control.execution who phase remaining installed committing material offered
      rcases material with ⟨⟨packet, preparation⟩, evidence⟩
      change packet = .commitment sentEvent (who, .prepared serial) at named
      cases named
      exact (nonsend ⟨sentEvent, serial, preparation, evidence, rfl⟩).elim

/-- Every literal nonsend occurrence of an actual whole recall has a derived
two-sided swap bound under ONE full timing plan. Genuine binding WAIT uses
the original omission floor; opening WAIT and other nonbinding atoms remain exact. -/
theorem phaseTimingPlanPolicy_value_nonsend_record_swap_ratio
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    [setup.FiniteInitialLaw]
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (owner : Player) (site : setup.commitRecoveryModel.InformationSite owner)
      (choice : setup.commitRecoveryModel.Choice owner site.1),
      floor ≤ ((approximation.sequence n).strategy owner site.1 choice).toReal)
    (fallback : (who : Player) → (N).Policy who)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p)
    (swap : HiddenSwap (serviceGraph setup mode))
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (guarded : PhaseSwapGuard runtime leaks swap (phaseSwapAllowed swap initial) final.execution)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (requested : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (who : Player) (reference : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (past : List (app).PlayerEntry) (entry : (app).PlayerEntry) (later : List (app).PlayerEntry)
    (recalled : final.execution.recall who = past ++ entry :: later)
    (nonsend : ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler
      who (some (past, entry.beforeView), entry.action)) :
    let family := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who reference)
          noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts who
    let first := (family past entry.beforeView entry.action).toReal
    let second := (family (past.map swap.phaseEntry) (swap.phaseView entry.beforeView)
      (swap.phaseAction entry.action)).toReal
    let coefficient := 1 + noise / ((1 - noise) * (slotWeight * floor))
    first ≤ coefficient * second ∧ second ≤ coefficient * first := by
  classical
  intro family first second coefficient
  by_cases usable : ∃ event payload,
      (serviceGraph setup mode).outputLayout event = .binding who payload ∧
      PhaseRuntimeState.requests entry.beforeView.application.2 who
        ⟨entry.beforeView.application.2.attempt, event⟩ ∧
      ∀ message ∈ (app).outputs past, PhaseCount.event? message.payload ≠
        some ⟨entry.beforeView.application.2.attempt, event⟩
  · obtain ⟨event, payload, binding, request, unsent⟩ := usable
    obtain ⟨before, prior, isPrefix, active, pastEq, viewed, offered⟩ :=
      (menu).recorded_response_at initial horizon scheduler final finalTrace who past entry later
        recalled
    have raw := (menu).toRawTrace initial horizon scheduler prior
    obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
      raw
    have genuine : before.execution.application.SeedRequest who
        ⟨before.execution.application.attempt, event⟩ := by
      rw [viewed] at request
      change PhaseRuntimeState.requests before.execution.application.publicView who
        ⟨before.execution.application.attempt, event⟩ at request
      exact (PhaseRuntimeState.requests_publicView _ valid _ _).mp request
    have beforeUnsent : ∀ message ∈ (app).outputs (before.execution.recall who),
        PhaseCount.event? message.payload ≠ some ⟨before.execution.application.attempt, event⟩ := by
      rw [viewed, ← pastEq] at unsent
      exact unsent
    have beforeNonsend : ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon
        scheduler who (some (before.execution.recall who, before.execution.observe app who),
          entry.action) := by
      simpa only [pastEq, ← viewed] using nonsend
    have silent := silence_of_binding_nonsend setup mode runtime leaks bounds plan horizon scheduler
      maximal who before prior event payload binding genuine entry.action
        (by simpa only [pastEq] using offered) beforeNonsend
    have beforeGuard := swap.phaseSwapGuard_of_tracePrefix bounds plan inputs horizon scheduler
      before final prior finalTrace isPrefix guarded bounded expiry
    have beforeEq : before = ⟨before.remaining, some who, before.execution⟩ := by
      cases before with
      | mk remaining actor execution => cases active; rfl
    let actual : (E).Trace (some ⟨before.remaining, some who, before.execution⟩) := beforeEq ▸ prior
    let symmetry := phaseOnePacketSwapSymmetry bounds initial
      (phase_initial_support_invariant plan inputs) horizon scheduler swap
        (phaseSwapAllowed swap initial) (phase_initialClosed_swapAllowed swap plan inputs)
          bounded expiry
    have swappedTrace : (E).Trace
        (some ⟨before.remaining, some who, swap.phaseExecution before.execution⟩) :=
      symmetry.mapTrace actual beforeGuard
    have compared := phaseTimingPlanPolicy_value_binding_waiting_swap_of_floor setup mode runtime
      leaks bounds plan initial (by exact PMF.map_comp ..) horizon scheduler bound finite wellFormed
        target approximation maximal n capacity swap before.remaining who before.execution actual
          swappedTrace event payload binding genuine beforeUnsent (values payload) beforeGuard.clear
            fallback floor floorPositive floored noise noiseNonnegative noiseSmall slotWeight
              slotPositive slotBounded parts reference reference
    rw [swap.observe_phaseExecution, pastEq, ← viewed] at compared
    simpa only [family, first, second, coefficient, silent, HiddenSwap.phaseExecution,
      HiddenSwap.phaseAction, pastEq, Option.map_none] using compared.2.2
  · have same := phaseTimingPlanPolicy_nonbinding_record_swap setup mode runtime leaks bounds
      plan inputs horizon scheduler bound maximal wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who reference)
          fallback noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts
            swap bounded expiry final finalTrace guarded bindingEvent bindingOwner bindingPayload
              bindingOutput requested values who past entry later recalled usable
    have scalar : first = second := congrArg ENNReal.toReal same
    have coefficientOne : 1 ≤ coefficient := by
      dsimp only [coefficient]
      exact le_add_of_nonneg_right (div_nonneg noiseNonnegative
        (mul_pos (sub_pos.mpr noiseSmall) (mul_pos slotPositive floorPositive)).le)
    have nonnegative : 0 ≤ second := ENNReal.toReal_nonneg
    constructor <;> nlinarith [mul_nonneg (sub_nonneg.mpr coefficientOne) nonnegative]

omit histories infos in
private theorem binding_syntax_swap (swap : HiddenSwap (serviceGraph setup mode))
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action) :
    phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
        (some (past, view), response) ↔
      phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
        (some (past.map swap.phaseEntry, swap.phaseView view), swap.phaseAction response) := by
  unfold phaseRawBindingRecord
  have forward (action : (app).Action)
      (sent : ∃ event serial preparation evidence, action =
        ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩) :
      ∃ event serial preparation evidence, swap.phaseAction action =
        ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ := by
    obtain ⟨event, serial, preparation, evidence, rfl⟩ := sent
    exact ⟨event, serial, preparation.map (swap.raw (who, .prepared serial)), evidence, rfl⟩
  constructor
  · exact forward response
  · intro sent
    obtain ⟨event, serial, preparation, evidence, same⟩ :=
      forward (swap.phaseAction response) sent
    exact ⟨event, serial, preparation, evidence,
      (swap.phaseAction_involutive response).symm.trans same⟩

open Classical in
omit histories infos in
private theorem operational_map_eq (swap : HiddenSwap (serviceGraph setup mode))
    (who : Player) (family : (app).Policy) (recalled : List (app).PlayerEntry) :
    (∏ index : Fin (recalled.map swap.phaseEntry).length with
      ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
        (some ((recalled.map swap.phaseEntry).take index.val,
          (recalled.map swap.phaseEntry)[index.val].beforeView),
            (recalled.map swap.phaseEntry)[index.val].action),
      (family ((recalled.map swap.phaseEntry).take index.val)
        (recalled.map swap.phaseEntry)[index.val].beforeView
          (recalled.map swap.phaseEntry)[index.val].action).toReal) =
    ∏ index : Fin recalled.length with
      ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
        (some (recalled.take index.val, recalled[index.val].beforeView),
          recalled[index.val].action),
      (family ((recalled.take index.val).map swap.phaseEntry)
        (swap.phaseView recalled[index.val].beforeView)
          (swap.phaseAction recalled[index.val].action)).toReal := by
  refine Finset.prod_bij (fun (index : Fin (recalled.map swap.phaseEntry).length) _ =>
    (⟨index.val, by simpa only [List.length_map] using index.isLt⟩ : Fin recalled.length))
      ?_ ?_ ?_ ?_
  · intro index member
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have notImage : ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler
        who (some ((recalled.take index.val).map swap.phaseEntry,
          swap.phaseView recalled[index.val].beforeView),
            swap.phaseAction recalled[index.val].action) := by
      simpa only [← List.map_take, List.getElem_map, HiddenSwap.phaseEntry] using
        (Finset.mem_filter.mp member).2
    exact (not_congr (binding_syntax_swap setup mode runtime leaks bounds plan horizon scheduler
      swap who (recalled.take index.val) recalled[index.val].beforeView
        recalled[index.val].action)).mpr notImage
  · intro first _firstMember second _secondMember same
    exact Fin.ext (congrArg (fun value : Fin recalled.length => value.val) same)
  · intro index member
    let original : Fin (recalled.map swap.phaseEntry).length :=
      ⟨index.val, by simpa only [List.length_map] using index.isLt⟩
    refine ⟨original, ?_, rfl⟩
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    have notImage := (not_congr (binding_syntax_swap setup mode runtime leaks bounds plan horizon
      scheduler swap who (recalled.take index.val) recalled[index.val].beforeView
        recalled[index.val].action)).mp (Finset.mem_filter.mp member).2
    simpa only [original, ← List.map_take, List.getElem_map, HiddenSwap.phaseEntry] using notImage
  · intro index _member
    simp only [← List.map_take, List.getElem_map, HiddenSwap.phaseEntry]

open Classical in
/-- The ENTIRE actual nonsend operational likelihood has a two-sided near-one
bound across the guarded history exchange. The product is the literal
operational factor in value-policy recall disintegration; the image is
reindexed by the unchanged recall length. No per-record likelihood bound is a premise. -/
theorem phaseTimingPlanPolicy_value_operational_swap_bounds
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    [setup.FiniteInitialLaw]
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
        setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor)
    (floored : ∀ (owner : Player) (site : setup.commitRecoveryModel.InformationSite owner)
      (choice : setup.commitRecoveryModel.Choice owner site.1),
      floor ≤ ((approximation.sequence n).strategy owner site.1 choice).toReal)
    (fallback : (who : Player) → (N).Policy who)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p)
    (swap : HiddenSwap (serviceGraph setup mode))
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (final : (app).Control) (finalTrace : (E).Trace (some final))
    (guarded : PhaseSwapGuard runtime leaks swap (phaseSwapAllowed swap initial) final.execution)
    (bindingEvent : (serviceGraph setup mode).EventId) (bindingOwner : Player)
    (bindingPayload : L.Ty)
    (bindingOutput : (serviceGraph setup mode).outputLayout bindingEvent =
      .binding bindingOwner bindingPayload)
    (requested : final.execution.application.SeedRequest bindingOwner
      ⟨final.execution.application.attempt, bindingEvent⟩)
    (values : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (who : Player) (reference : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
 :
    let recalled := final.execution.recall who
    let family := phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler
      bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who reference)
          noise noiseNonnegative noiseSmall.le slotWeight slotPositive.le slotBounded parts who
    let binding := fun index : Fin recalled.length => phaseRawBindingRecord setup mode runtime
      leaks bounds plan horizon scheduler who
        (some (recalled.take index.val, recalled[index.val].beforeView), recalled[index.val].action)
    let firstAtom := fun index : Fin recalled.length =>
      (family (recalled.take index.val) recalled[index.val].beforeView
        recalled[index.val].action).toReal
    let firstOperational := ∏ index ∈ Finset.univ.filter (fun index => ¬ binding index),
      firstAtom index
    let secondOperational := ∏ index : Fin (recalled.map swap.phaseEntry).length with
      ¬ phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
        (some ((recalled.map swap.phaseEntry).take index.val,
          (recalled.map swap.phaseEntry)[index.val].beforeView),
            (recalled.map swap.phaseEntry)[index.val].action),
      (family ((recalled.map swap.phaseEntry).take index.val)
        (recalled.map swap.phaseEntry)[index.val].beforeView
          (recalled.map swap.phaseEntry)[index.val].action).toReal
    let coefficient := 1 + noise / ((1 - noise) * (slotWeight * floor))
    firstOperational ≤ coefficient ^ recalled.length * secondOperational ∧
      secondOperational ≤ coefficient ^ recalled.length * firstOperational ∧
      |firstOperational - secondOperational| ≤
        (coefficient ^ recalled.length - 1) * secondOperational := by
  classical
  intro recalled family binding firstAtom firstOperational secondOperational coefficient
  let secondAtom := fun index : Fin recalled.length =>
      (family ((recalled.take index.val).map swap.phaseEntry)
        (swap.phaseView recalled[index.val].beforeView)
          (swap.phaseAction recalled[index.val].action)).toReal
  let selected := Finset.univ.filter fun index : Fin recalled.length => ¬ binding index
  have secondIndexed : secondOperational = ∏ index ∈ selected, secondAtom index :=
    operational_map_eq setup mode runtime leaks bounds plan horizon scheduler swap who family
      recalled
  rw [secondIndexed]
  let secondProduct := ∏ index ∈ selected, secondAtom index
  change firstOperational ≤ coefficient ^ recalled.length * secondProduct ∧
    secondProduct ≤ coefficient ^ recalled.length * firstOperational ∧
    |firstOperational - secondProduct| ≤ (coefficient ^ recalled.length - 1) * secondProduct
  have pointwise (index : Fin recalled.length) (member : index ∈ selected) :
      firstAtom index ≤ coefficient * secondAtom index ∧
        secondAtom index ≤ coefficient * firstAtom index := by
    have cut : recalled.take (index.val + 1) ++ recalled.drop (index.val + 1) = recalled :=
      List.take_append_drop ..
    rw [List.take_succ_eq_append_getElem index.isLt] at cut
    have split : final.execution.recall who = recalled.take index.val ++ recalled[index.val] ::
        recalled.drop (index.val + 1) := by
      simpa only [recalled, List.append_assoc, List.singleton_append] using cut.symm
    exact phaseTimingPlanPolicy_value_nonsend_record_swap_ratio setup mode runtime leaks bounds
      plan horizon scheduler bound finite wellFormed target approximation maximal n capacity
        floor floorPositive floored fallback noise noiseNonnegative noiseSmall slotWeight
          slotPositive slotBounded parts swap bounded expiry final finalTrace guarded bindingEvent
            bindingOwner bindingPayload bindingOutput requested values who reference
              (recalled.take index.val) recalled[index.val] (recalled.drop (index.val + 1)) split
                (Finset.mem_filter.mp member).2
  have coefficientOne : 1 ≤ coefficient := by
    dsimp only [coefficient]
    exact le_add_of_nonneg_right (div_nonneg noiseNonnegative
      (mul_pos (sub_pos.mpr noiseSmall) (mul_pos slotPositive floorPositive)).le)
  have countBound : selected.card ≤ recalled.length := by
    calc
      selected.card ≤ (Finset.univ : Finset (Fin recalled.length)).card :=
        Finset.card_le_card (Finset.filter_subset ..)
      _ = recalled.length := by simp
  have powered := pow_le_pow_right₀ coefficientOne countBound
  have firstNonnegative (index : Fin recalled.length) : 0 ≤ firstAtom index :=
    ENNReal.toReal_nonneg
  have secondNonnegative (index : Fin recalled.length) : 0 ≤ secondAtom index :=
    ENNReal.toReal_nonneg
  have compared : firstOperational ≤ coefficient ^ recalled.length * secondProduct ∧
      secondProduct ≤ coefficient ^ recalled.length * firstOperational := by
    constructor
    · calc
        firstOperational = ∏ index ∈ selected, firstAtom index := rfl
        _ ≤ ∏ index ∈ selected, coefficient * secondAtom index :=
          Finset.prod_le_prod₀ (fun index _ => firstNonnegative index)
            (fun index member => (pointwise index member).1)
        _ = coefficient ^ selected.card * secondProduct := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ coefficient ^ recalled.length * secondProduct :=
          mul_le_mul_of_nonneg_right powered
            (Finset.prod_nonneg fun index _ => secondNonnegative index)
    · calc
        secondProduct = ∏ index ∈ selected, secondAtom index := rfl
        _ ≤ ∏ index ∈ selected, coefficient * firstAtom index :=
          Finset.prod_le_prod₀ (fun index _ => secondNonnegative index)
            (fun index member => (pointwise index member).2)
        _ = coefficient ^ selected.card * firstOperational := by
          rw [Finset.prod_mul_distrib, Finset.prod_const]
        _ ≤ coefficient ^ recalled.length * firstOperational :=
          mul_le_mul_of_nonneg_right powered
            (Finset.prod_nonneg fun index _ => firstNonnegative index)
  refine ⟨compared.1, compared.2, ?_⟩
  have poweredOne : 1 ≤ coefficient ^ recalled.length := by
    simpa only [one_pow] using
      pow_le_pow_left₀ (show (0 : ℝ) ≤ 1 by norm_num) coefficientOne recalled.length
  rcases le_total firstOperational secondProduct with increasing | decreasing
  · rw [abs_of_nonpos (sub_nonpos.mpr increasing)]
    have scaled := mul_le_mul_of_nonneg_left increasing (sub_nonneg.mpr poweredOne)
    nlinarith only [compared.2, scaled]
  · rw [abs_of_nonneg (sub_nonneg.mpr decreasing)]
    nlinarith only [compared.1]

end Vegas
