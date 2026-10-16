/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseRepairOwnPlay
import Vegas.Pending.PhaseBindingIdleMenu

/-! # Actual individual response factors under directed repair -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

variable (wellFormed : setup.WellFormed)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

/-- Actual legal replacement material supplies the send factor, including
accepted failed typed results. Both callbacks are genuine initialized histories. -/
theorem phaseBindingSendingPair.record_ratio
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (mixed : assessment.IsFullyMixed)
    (floor : ℝ) (positive : 0 < floor)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ (assessment.strategy player site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseBindingSendingPair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseSmall.le slotWeight
        slotPositive.le slotBounded
    (((strategy who first.1).map Subtype.val) (some first.2)).toReal ≤
      ((bounds.candidateCount : ℝ) / ((1 - noise) * slotWeight * floor)) *
        (((strategy who second.1).map Subtype.val) (some second.2)).toReal := by
  obtain ⟨firstControl, secondControl, _firstTrace, secondTrace, event, payload, binding,
    serial, preparation, evidence, result, original, _firstActor, _secondActor, request,
      unsent, values, clear, originalMember, materialMember, rfl, rfl⟩ := paired
  intro strategy
  let originalChoice : (N).Choice who (some (firstControl.execution.recall who,
      firstControl.execution.observe app who)) := ⟨some original, ⟨original, originalMember, rfl⟩⟩
  obtain ⟨replacement, selected, compared⟩ :=
    phaseSourcePerturbedStrategy_replacement_ratio_of_floor setup mode runtime leaks bounds plan
      maximal horizon scheduler wellFormed assessment mixed floor positive floored noise
        noiseNonnegative noiseSmall slotWeight slotPositive slotBounded secondControl secondTrace
          who event payload binding request unsent values clear serial preparation evidence
            materialMember result
  have firstAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective originalChoice
  have secondAtom := pmf_map_apply_of_injective (strategy who _) Subtype.val_injective replacement
  rw [selected] at secondAtom
  rw [firstAtom, secondAtom]
  exact compared _ originalChoice

/-- The opening factor is exactly one, including all raw-menu noise aliases.
The successful binding is derived from the actual final clear binding callback. -/
theorem phaseOpeningResponsePair.record_eq
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseBounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseOpeningResponsePair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    let strategy := phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon
      scheduler wellFormed assessment noise noiseNonnegative noiseBounded slotWeight
        slotNonnegative slotBounded
    ((strategy who first.1).map Subtype.val) (some first.2) =
      ((strategy who second.1).map Subtype.val) (some second.2) := by
  obtain ⟨remaining, original, repaired, memory, frame, leftTrace, rightTrace, final, finalTrace,
    isPrefix, event, payload, binding, checks, outputEq, codeEq, node, bindingEvent, bindingOwner,
      bindingPayload, bindingOutput, action, clear, leftRequest, rightRequest, leftUnsent,
        rightUnsent, values, requested, rfl, rfl, _key⟩ := paired
  intro strategy
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
  have compared := phaseSourcePerturbedStrategy_opening_raw_eq_before_binding setup mode runtime
    leaks bounds plan inputs horizon scheduler wellFormed assessment maximal who remaining
      original repaired memory frame left right final finalHistory path clear event payload
        binding checks outputEq codeEq node leftRequest rightRequest leftUnsent rightUnsent
          values bindingEvent bindingOwner bindingPayload bindingOutput requested slotWeight
            slotNonnegative slotBounded noise noiseNonnegative noiseBounded
  have laws :
      (strategy who (some (original.recall who, original.observe app who))).map Subtype.val =
      (strategy who (some (repaired.recall who, repaired.observe app who))).map Subtype.val := by
    dsimp only [inputs] at compared
    rw [PMF.map_comp] at compared
    exact compared.1
  exact congrArg (fun law => law (some action)) laws

omit maximal

private theorem raw_policy_eq_pure_of_singleton (who : Player)
    (policy : (N).BehavioralPolicy who) (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (singleton : PhaseCount.onePacketActions runtime leaks bounds who past view = {⟨none⟩}) :
    (policy (some (past, view))).map Subtype.val = PMF.pure (some ⟨none⟩) := by
  have unique (choice : (N).Choice who (some (past, view))) : choice.1 = some ⟨none⟩ := by
    obtain ⟨action, member, same⟩ := choice.2
    change action ∈ PhaseCount.onePacketActions runtime leaks bounds who past view at member
    rw [singleton] at member
    exact same.trans (congrArg some (Finset.mem_singleton.mp member))
  calc
    _ = (policy (some (past, view))).map (fun _ => some ⟨none⟩) :=
      map_congr_on_support _ (fun choice _ => unique choice)
    _ = _ := PMF.map_const _ _

/-- Actual request absence or a prior own packet forces both response factors
to one, for every policy on the globally legal counted menus. -/
theorem phaseInertResponsePair.record_eq (strategy : ∀ player, (N).BehavioralPolicy player)
    (who : Player) (first second : (N).InfoState who × (E).Action who)
    (paired : phaseInertResponsePair setup mode runtime leaks bounds plan horizon scheduler who
      first second) :
    ((strategy who first.1).map Subtype.val) (some first.2) =
      ((strategy who second.1).map Subtype.val) (some second.2) := by
  obtain ⟨firstControl, secondControl, firstTrace, secondTrace, firstActor, secondActor,
    firstClear, secondClear, firstAbsent, secondAbsent, rfl, rfl⟩ := paired
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have singleton (control : (app).Control) (trace : (E).Trace (some control))
      (actor : control.actor = some who)
      (clear : control.execution.application.current.excluded = ∅)
      (inert : (∀ coordinate, ¬control.execution.application.SeedRequest who coordinate) ∨
        ∃ coordinate, control.execution.application.SeedRequest who coordinate ∧
          ∃ message ∈ (app).outputs (control.execution.recall who),
            PhaseSeedScheduler.ownPacket coordinate who message = true) :
      PhaseCount.onePacketActions runtime leaks bounds who (control.execution.recall who)
        (control.execution.observe app who) = {⟨none⟩} := by
    have current : control = ⟨control.remaining, some who, control.execution⟩ := by
      cases control
      simp_all only
    have typed : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
          (some ⟨control.remaining, some who, control.execution⟩) := by
      rw [← current]
      dsimp only [inputs]
      rw [PMF.map_comp]
      exact trace
    rcases inert with absent | ⟨coordinate, request, sent⟩
    · exact PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds plan inputs
        horizon scheduler control.remaining who control.execution typed clear absent
    · exact PhaseCount.onePacketActions_eq_singleton_of_sent runtime leaks bounds plan
        (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler control.remaining
          who control.execution typed coordinate request sent
  have firstLaw := raw_policy_eq_pure_of_singleton setup mode runtime leaks bounds plan horizon
    scheduler who (strategy who) _ _ (singleton firstControl firstTrace firstActor firstClear
      firstAbsent)
  have secondLaw := raw_policy_eq_pure_of_singleton setup mode runtime leaks bounds plan horizon
    scheduler who (strategy who) _ _ (singleton secondControl secondTrace secondActor secondClear
      secondAbsent)
  rw [firstLaw, secondLaw]

end Vegas
