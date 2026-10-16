/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRecoveryValueStrategy
import Vegas.Pending.PhaseBindingMemoryCallback
import Vegas.Pending.PhaseCommitmentMenuShape
import Vegas.Pending.PhaseBindingReadiness
import Vegas.Game.PhaseRepairMarkedRecords
import Vegas.Pending.PhaseClearTraceProgress
import Interaction.ReactiveRecordedResponse

/-! # Source-policy factors in actual chronological native response likelihoods -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

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

local instance phaseRecoveryValueLikelihoodPoolFintype : Fintype Pool := Fintype.ofFinite _

open Classical in
/-- At a genuine clear callback, any legal response other than a binding SEND
has the SAME atom for every original immutable source-value policy. RAW opening
WAIT, physical menu guards and the entire fixed timing plan are retained. -/
theorem phaseTimingPlanPolicy_value_nonsend_atom_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (first second : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (response : (app).Action)
    (offered : response ∈ (menu).actions who (control.execution.recall who)
      (control.execution.observe (app) who))
    (nonsend : ¬ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
      scheduler who (some (control.execution.recall who,
        control.execution.observe (app) who), response)) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who first)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (control.execution.recall who) (control.execution.observe (app) who) response =
      phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who second)
          noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
            (control.execution.recall who) (control.execution.observe (app) who) response := by
  let past := control.execution.recall who
  let view := control.execution.observe (app) who
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
  have controlEq : control = ⟨control.remaining, some who, control.execution⟩ := by
    cases control with
    | mk remaining actor execution => cases active; rfl
  have actual : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨control.remaining, some who, control.execution⟩) := controlEq ▸ trace
  by_cases usable : ∃ coordinate, control.execution.application.SeedRequest who coordinate ∧
      ∀ message ∈ (app).outputs past, PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨⟨attempt, event⟩, request, unsent⟩ := usable
    have address : attempt = control.execution.application.attempt := request.1
    subst attempt
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        have silent : response = ⟨none⟩ := by
          rcases response with ⟨transmission⟩
          cases transmission with
          | none => rfl
          | some material =>
              obtain ⟨phase, remaining, installed, committing, _inside⟩ :=
                phase_ready_binding_phase runtime leaks runtimePlan
                  (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon scheduler
                    raw who event payload outputEq request.2.2.1
              obtain ⟨sentEvent, serial, named⟩ := PhaseCount.onePacket_commitment_shape runtime
                leaks bounds control.execution who phase remaining installed committing material
                  offered
              rcases material with ⟨⟨packet, preparation⟩, evidence⟩
              change packet = .commitment sentEvent (who, .prepared serial) at named
              cases named
              exact (nonsend ⟨sentEvent, serial, preparation, evidence, rfl⟩).elim
        subst response
        exact phaseTimingPlanPolicy_value_silence_of_history setup mode runtime leaks bounds
          initial horizon scheduler bound fallback wellFormed assessment mixed noise
            noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who first
              second runtimePlan maximal control sourceTrace valid clear event payload outputEq
                request played
    | resolve owner payload field checks outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        exact congrArg (fun law : PMF (app).Action => law response)
          (phaseTimingPlanPolicy_opening_congr setup mode runtime leaks bounds initial horizon
            scheduler bound fallback wellFormed
              (setup.commitRecoveryValueAssessment wellFormed assessment who first)
              (setup.commitRecoveryValueAssessment wellFormed assessment who second) noise
                noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
                  control.execution valid clear event payload field checks outputEq codeEq request
                    played)
    | sample payload law outputEq codeEq =>
        have noOwner : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have owned := request.2.2.2.1
        rw [noOwner] at owned
        cases owned
  · have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      runtimePlan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler
        control.remaining who control.execution actual clear usable
    have forced (source : setup.commitRecoveryModel.BehavioralAssessment) :
        phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound
            fallback wellFormed source noise noiseNonnegative noiseBounded slotWeight
              slotNonnegative slotBounded plan who past view = PMF.pure ⟨none⟩ := by
      apply pmf_eq_pure_of_support_subset_singleton
      intro action supported
      have offered := phaseTimingPlanPolicy_covered setup mode runtime leaks bounds initial
        horizon scheduler bound fallback wellFormed source noise noiseNonnegative noiseBounded
          slotWeight slotNonnegative slotBounded plan who past view action supported
      change action ∈ PhaseCount.onePacketActions runtime leaks bounds who past view at offered
      rw [singleton] at offered
      exact Finset.mem_singleton.mp offered
    exact congrArg (fun law : PMF (app).Action => law response)
      ((forced _).trans (forced _).symm)

open Classical in
/-- An actual legal nonbinding response does not update the ORIGINAL source
value-policy posterior when the full private timing plan is held fixed. All
previous raw recall remains in that posterior, and the physical emitted entry
is retained literally. Positive RAW noise supplies the observed atom. -/
theorem phaseTimingPlanPolicy_value_nonsend_posterior_of_history
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (noise : ℝ) (positive : 0 < noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (active : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (response : (app).Action)
    (offered : response ∈ (menu).actions who (control.execution.recall who)
      (control.execution.observe (app) who))
    (nonsend : ¬ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
      scheduler who (some (control.execution.recall who,
        control.execution.observe (app) who), response)) :
    let original := setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who
    let family := fun member => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who member) noise positive.le
          noiseBounded slotWeight slotNonnegative slotBounded plan who
    ((app).policyMixture original family).posterior
        ((control.execution.respond (app) who response).recall who) =
      ((app).policyMixture original family).posterior (control.execution.recall who) := by
  intro original family
  let reference := original.support_nonempty.choose
  have controlEq : control = ⟨control.remaining, some who, control.execution⟩ := by
    cases control with
    | mk remaining actor execution => cases active; rfl
  have actual : ((menu).protocol initial horizon scheduler).Trace
      (some ⟨control.remaining, some who, control.execution⟩) := controlEq ▸ trace
  obtain ⟨afterTrace⟩ := (menu).trace_respond initial horizon scheduler control.remaining
    control.execution who response actual offered
  obtain ⟨emitted, recalled⟩ := (app).respond_recall_entry control.execution who response
  have consistent := phaseTimingPlanPolicy_consistent_of_history setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound fallback wellFormed
      (setup.commitRecoveryValueAssessment wellFormed assessment who reference) noise positive
        noiseBounded slotWeight slotNonnegative slotBounded plan who _ afterTrace
  rw [recalled] at consistent
  have supported := ((family reference).consistent_snoc_iff _ _).mp consistent |>.2
  have likelihoodPositive : family reference (control.execution.recall who)
      (control.execution.observe (app) who) response ≠ 0 := (PMF.mem_support_iff _ _).mp supported
  rw [recalled]
  apply (app).policyMixture_posterior_snoc_of_likelihood original family
    (control.execution.recall who) ⟨control.execution.observe (app) who, response, emitted⟩
      (family reference (control.execution.recall who)
        (control.execution.observe (app) who) response) _ likelihoodPositive
  intro member _supported
  exact phaseTimingPlanPolicy_value_nonsend_atom_of_history setup mode runtime leaks bounds
    runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed noise
      positive.le noiseBounded slotWeight slotNonnegative slotBounded plan who member reference
        control trace active clear response offered nonsend

private theorem actual_nonsend_record_atom
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (reference : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (index : Fin (control.execution.recall who).length)
    (notBinding : ¬ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
      scheduler who (some ((control.execution.recall who).take index.val,
        (control.execution.recall who)[index.val].beforeView),
          (control.execution.recall who)[index.val].action))
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    let family := fun source => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who source) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
    (family member ((control.execution.recall who).take index.val)
        (control.execution.recall who)[index.val].beforeView
          (control.execution.recall who)[index.val].action).toReal =
      (family reference ((control.execution.recall who).take index.val)
        (control.execution.recall who)[index.val].beforeView
          (control.execution.recall who)[index.val].action).toReal := by
  intro family
  let recalled := control.execution.recall who
  have cut : recalled.take (index.val + 1) ++ recalled.drop (index.val + 1) = recalled :=
    List.take_append_drop ..
  rw [List.take_succ_eq_append_getElem index.isLt] at cut
  have split : recalled = recalled.take index.val ++ recalled[index.val] ::
      recalled.drop (index.val + 1) := by
    simpa only [List.append_assoc, List.singleton_append] using cut.symm
  obtain ⟨before, prior, isPrefix, active, pastEq, viewed, offered⟩ :=
    (menu).recorded_response_at initial horizon scheduler control trace who
      (recalled.take index.val) recalled[index.val] (recalled.drop (index.val + 1)) split
  have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
    scheduler before control prior trace isPrefix clear).1
  have notSent : ¬ phaseRawBindingRecord setup mode runtime leaks bounds runtimePlan horizon
      scheduler who (some (before.execution.recall who,
        before.execution.observe (app) who), recalled[index.val].action) := by
    simpa only [pastEq, ← viewed] using notBinding
  have same := phaseTimingPlanPolicy_value_nonsend_atom_of_history setup mode runtime leaks
    bounds runtimePlan horizon scheduler bound maximal fallback wellFormed assessment mixed
      noise noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who member
        reference before prior active beforeClear recalled[index.val].action
          (by simpa only [pastEq] using offered) notSent
  simpa only [family, pastEq, ← viewed] using congrArg ENNReal.toReal same

open Classical in
private theorem product_split_complement {Index Member : Type} [Fintype Index]
    (binding : Index → Prop) (atom : Member → Index → ℝ) (reference : Member)
    (same : ∀ index, ¬ binding index → ∀ member, atom member index = atom reference index)
    (member : Member) :
    (∏ index, atom member index) =
      (∏ index ∈ Finset.univ.filter (fun index => ¬ binding index), atom reference index) *
        ∏ index ∈ Finset.univ.filter binding, atom member index := by
  classical
  rw [← Finset.prod_filter_not_mul_prod_filter Finset.univ binding (atom member)]
  congr 1
  apply Finset.prod_congr rfl
  intro index inside
  exact same index (Finset.mem_filter.mp inside).2 member

open Classical in
/-- The likelihood of the ENTIRE actual own recall factors into binding-SEND
atoms and one explicit remaining-response product independent of the ORIGINAL
pure source-value policy. The latter retains timing, omission, RAW opening
WAIT and all actual physical inputs; it is not asserted equal across histories. -/
theorem phaseTimingPlanPolicy_value_recall_factors
    (maximal : runtimePlan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : (p : Pool) → Parts p) (who : Player)
    (reference : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (control : (app).Control)
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅) :
    let recalled := control.execution.recall who
    let family := fun member => phaseTimingPlanPolicy setup mode runtime leaks bounds initial
      horizon scheduler bound fallback wellFormed
        (setup.commitRecoveryValueAssessment wellFormed assessment who member) noise
          noiseNonnegative noiseBounded slotWeight slotNonnegative slotBounded plan who
    let binding := fun index : Fin recalled.length => phaseRawBindingRecord setup mode runtime
      leaks bounds runtimePlan horizon scheduler who
        (some (recalled.take index.val, recalled[index.val].beforeView), recalled[index.val].action)
    let atom := fun member (index : Fin recalled.length) =>
      (family member (recalled.take index.val) recalled[index.val].beforeView
        recalled[index.val].action).toReal
    let operational := ∏ index ∈ Finset.univ.filter (fun index => ¬ binding index),
      atom reference index
    0 ≤ operational ∧ ∀ member,
      (∏ index : Fin recalled.length, atom member index) =
        operational * ∏ index ∈ Finset.univ.filter binding, atom member index := by
  intro recalled family binding atom operational
  have constant (index : Fin recalled.length) (notBinding : ¬ binding index) (member) :
      atom member index = atom reference index :=
    actual_nonsend_record_atom setup mode runtime leaks bounds runtimePlan horizon scheduler
      bound maximal fallback wellFormed assessment mixed noise noiseNonnegative noiseBounded
        slotWeight slotNonnegative slotBounded plan who reference control trace clear index
          notBinding member
  refine ⟨Finset.prod_nonneg fun _ _ => ENNReal.toReal_nonneg, ?_⟩
  intro member
  exact product_split_complement binding atom reference constant member

end Vegas
