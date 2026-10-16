/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingCommitmentProduct
import Vegas.Game.PhaseRecoveryValueSilence

/-! # Original omission mass for sparse immutable source members -/

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
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "Pool" => FreeKeyedPool
  (fun agent : (N).InformationAgent (N).playedInformation =>
    PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
  (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
    (Subtype.val (Sigma.snd agent)))
  (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent) (Subtype.val (Sigma.snd agent)))
local notation "pool" => phaseTimingPool setup mode runtime leaks bounds initial horizon
  scheduler bound
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

private theorem value_silence_base_initial
    (law : PMF (app).State)
    (same : law = (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan))
    [Fintype ((menu).protocol law horizon scheduler).History]
    [∀ who, DecidableEq (((menu).information law horizon scheduler).InfoState who)]
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, ((menu).information law horizon scheduler).Policy who)
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw]
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (current : (app).Control)
    (trace : ((menu).protocol law horizon scheduler).Trace (some current))
    (acting : current.actor = some who) (clear : current.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : current.execution.application.SeedRequest who
      ⟨current.execution.application.attempt, event⟩)
    (parts : (p : _) →
      PhaseTimingPart setup mode runtime leaks bounds law horizon scheduler bound p)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds law horizon scheduler bound fallback
        wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who member) noise
          nonnegative bounded slotWeight slotNonnegative slotBounded parts who
            (current.execution.recall who) (current.execution.observe app who) ⟨none⟩ =
      phaseTimingPlanPolicy setup mode runtime leaks bounds law horizon scheduler bound fallback
        wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
          parts who (current.execution.recall who) (current.execution.observe app who) ⟨none⟩ := by
  subst law
  exact phaseTimingPlanPolicy_value_silence_base_of_history setup mode runtime leaks bounds plan
    horizon scheduler bound maximal fallback wellFormed assessment mixed finite noise nonnegative
      bounded slotWeight slotNonnegative slotBounded who current trace acting clear event payload
        binding request parts member

private theorem decode_choice_injective (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) :
    Function.Injective (fun choice : (N).Choice who (some (past, view)) =>
      choice.1.getD ⟨none⟩) := by
  intro first second same
  obtain ⟨firstAction, _firstLegal, firstValue⟩ := first.2
  obtain ⟨secondAction, _secondLegal, secondValue⟩ := second.2
  apply Subtype.ext
  simpa only [firstValue, secondValue, Option.getD_some, Option.some.injEq] using same

private theorem finite_plan_silent_atom
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who)
    (silent : (N).Choice who (some (past, view))) (value : silent.1 = some ⟨none⟩) :
    phaseTimingPlanPolicy setup mode runtime leaks bounds initial horizon scheduler bound fallback
        wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
          parts who past view ⟨none⟩ =
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
          ⟨who, ⟨some (past, view), played⟩⟩
            (parts (pool ⟨who, ⟨some (past, view), played⟩⟩))) silent := by
  rw [phaseTimingPlanPolicy_apply, dite_eq_left played]
  have atom := pmf_map_apply_of_injective
    (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
        ⟨who, ⟨some (past, view), played⟩⟩
          (parts (pool ⟨who, ⟨some (past, view), played⟩⟩)))
    (decode_choice_injective setup mode runtime leaks bounds plan horizon scheduler who past view)
      silent
  simp only [value, Option.getD_some] at atom
  convert! atom using 1

/-- A sparse immutable source-value member retains the exact BASE finite
silent atom at a genuine binding callback. Full mixing is required only of
the original auxiliary assessment, never of the predrawn member. -/
theorem phaseTimingComponent_value_silent_base
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)] [setup.FiniteInitialLaw]
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (finite : setup.program.FiniteBindingTypes)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some who) (clear : current.execution.application.current.excluded = ∅)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : current.execution.application.SeedRequest who
      ⟨current.execution.application.attempt, event⟩)
    (played : some (current.execution.recall who, current.execution.observe app who) ∈
      (N).playedInformation who)
    (silent : (N).Choice who
      (some (current.execution.recall who, current.execution.observe app who)))
    (value : silent.1 = some ⟨none⟩) :
    (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed (setup.commitRecoveryValueAssessment wellFormed assessment who member)
        noise nonnegative bounded slotWeight slotNonnegative slotBounded
          ⟨who, ⟨_, played⟩⟩ (parts (pool ⟨who, ⟨_, played⟩⟩))) silent =
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded
          ⟨who, ⟨_, played⟩⟩ (parts (pool ⟨who, ⟨_, played⟩⟩))) silent := by
  have scalar := value_silence_base_initial setup mode runtime leaks bounds plan horizon scheduler
    bound initial (by simp only [PMF.map_comp, Function.comp_def]) maximal fallback wellFormed
      assessment mixed finite noise
      nonnegative bounded slotWeight slotNonnegative slotBounded who current trace acting clear
        event payload binding request parts member
  rw [finite_plan_silent_atom setup mode runtime leaks bounds plan horizon scheduler bound fallback
    wellFormed _ noise nonnegative bounded slotWeight slotNonnegative slotBounded parts who _ _
      played silent value,
    finite_plan_silent_atom setup mode runtime leaks bounds plan horizon scheduler bound fallback
      wellFormed _ noise nonnegative bounded slotWeight slotNonnegative slotBounded parts who _ _
        played silent value] at scalar
  exact scalar

/-- Every actual clear commitment callback retains original omission mass
even after predrawing an arbitrary sparse source-value policy. Sent and absent
requests use the actual singleton menu. No member full-mixing premise occurs. -/
theorem phaseTimingComponent_value_commitment_silence_lower
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)] [setup.FiniteInitialLaw]
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, (N).Policy who)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some who)
    (played : some (current.execution.recall who, current.execution.observe app who) ∈
      (N).playedInformation who)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : current.execution.application.current.excluded = ∅) :
    let agent : (N).InformationAgent (N).playedInformation := ⟨who, ⟨_, played⟩⟩
    let conditional := phaseTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed
        (setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n) who member)
          0 (by norm_num) (by norm_num) slotWeight slotPositive.le slotBounded agent
            (parts (pool agent))
    ∃ silent : (N).Choice who agent.2.1, silent.1 = some ⟨none⟩ ∧
      slotWeight * floor ≤ (conditional silent).toReal := by
  classical
  intro agent conditional
  obtain ⟨silent, value, lower, _retained, _upper⟩ :=
    phaseTimingComponent_commitment_silence_noise setup mode runtime leaks bounds plan horizon
      scheduler bound finite wellFormed target approximation maximal n capacity floor positive
        floorBounded floored 0 (by norm_num) (by norm_num) slotWeight slotPositive slotBounded
          agent (PMF.pure (parts (pool agent))) current trace acting rfl phase remaining installed
            committing allValues clear
  refine ⟨silent, value, ?_⟩
  by_cases usable : ∃ coordinate, current.execution.application.SeedRequest who coordinate ∧
      ∀ message ∈ (app).outputs (current.execution.recall who),
        PhaseCount.event? message.payload ≠ some coordinate
  · obtain ⟨coordinate, request, _unsent⟩ := usable
    obtain ⟨actual, head, inside⟩ := request.2.1
    have same : actual = phase := by
      simpa only [installed, List.head?_cons, Option.mem_def, Option.some.injEq] using head.symm
    subst actual
    have fields := phase.fields coordinate.event ((phase.mem_events coordinate.event).mp inside).1
      ((phase.mem_events coordinate.event).mp inside).2
    rw [committing] at fields
    obtain ⟨owner, payload, binding⟩ := fields
    have actorEq := ((serviceGraph setup mode).actor?_of_outputLayout_binding binding).symm.trans
      request.2.2.2.1
    cases Option.some.inj actorEq
    have currentTag : coordinate = ⟨current.execution.application.attempt, coordinate.event⟩ := by
      cases coordinate with
      | mk tag event =>
          simp only [CommitAttemptEvent.mk.injEq]
          exact ⟨request.1, trivial⟩
    rw [currentTag] at request
    have scalar := phaseTimingComponent_value_silent_base setup mode runtime leaks bounds plan
      horizon scheduler bound maximal fallback wellFormed (approximation.sequence n)
        (approximation.mixed n) finite 0 (by norm_num) (by norm_num) slotWeight slotPositive.le
          slotBounded parts who member current trace acting clear coordinate.event payload binding
            request played silent value
    dsimp only [conditional]
    rw [scalar]
    simpa only [PMF.pure_bind] using lower
  · let inputs := setup.initialLaw.map (fun draw => encodeInputs draw)
    have initialEq : inputs.map (PhaseRuntimeState.initial plan) = initial := by
      simp only [inputs, PMF.map_comp, Function.comp_def]
    have counted : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some current) := by rw [initialEq]; exact trace
    have sameControl : current = ⟨current.remaining, some who, current.execution⟩ := by
      cases current with
      | mk fuel actor execution => cases acting; rfl
    have activeTrace : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some ⟨current.remaining, some who, current.execution⟩) :=
      sameControl ▸ counted
    have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_unsent runtime leaks bounds
      plan (serviceGraph_revealRelaxedOrdered setup mode) inputs horizon scheduler current.remaining
        who current.execution activeTrace usable
    have valueEq (choice : (N).Choice who agent.2.1) : choice.1 = some ⟨none⟩ := by
      obtain ⟨action, offered, equal⟩ := choice.2
      change action ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (current.execution.recall who) (current.execution.observe app who) at offered
      rw [singleton] at offered
      exact equal.trans (congrArg some (Finset.mem_singleton.mp offered))
    let : Subsingleton ((N).Choice who agent.2.1) :=
      ⟨fun first second => Subtype.ext ((valueEq first).trans (valueEq second).symm)⟩
    have one : conditional silent = 1 := by
      rw [eq_pure_of_subsingleton conditional silent, PMF.pure_apply_self]
    rw [one, ENNReal.toReal_one]
    calc
      slotWeight * floor ≤ 1 * floor := mul_le_mul_of_nonneg_right slotBounded positive.le
      _ ≤ 1 := by simpa only [one_mul] using floorBounded

/-- Removing only the RAW transmission summand at an actual commitment
callback leaves the SAME sparse member's zero-noise response, up to the
near-one omission factor. Original accepted failure atoms remain retained. -/
theorem phaseTimingComponent_value_commitment_trimmed_atom
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)] [setup.FiniteInitialLaw]
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, (N).Policy who)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (small : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : (p : Pool) → Parts p) (who : Player)
    (member : (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (current : (app).Control) (trace : (E).Trace (some current))
    (acting : current.actor = some who)
    (played : some (current.execution.recall who, current.execution.observe app who) ∈
      (N).playedInformation who)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : current.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : current.execution.application.current.excluded = ∅)
    (choice : (N).Choice who
      (some (current.execution.recall who, current.execution.observe app who))) :
    let agent : (N).InformationAgent (N).playedInformation := ⟨who, ⟨_, played⟩⟩
    let source := setup.commitRecoveryValueAssessment wellFormed (approximation.sequence n)
      who member
    let residual := phaseTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed source 0 (by norm_num) (by norm_num) slotWeight slotPositive.le
        slotBounded agent (parts (pool agent))
    let perturbed := phaseTimingComponent setup mode runtime leaks bounds initial horizon
      scheduler bound wellFormed source noise nonnegative small.le slotWeight slotPositive.le
        slotBounded agent (parts (pool agent))
    let removed := if (choice.1.getD ⟨none⟩).transmission ≠ none then noise *
      (((menu).uniformPolicy initial horizon scheduler who agent.2.1) choice).toReal else 0
    0 ≤ (perturbed choice).toReal - removed ∧
      (perturbed choice).toReal - removed ≤ (perturbed choice).toReal ∧
      (perturbed choice).toReal - removed ≤
        (1 + noise / (slotWeight * floor)) * (residual choice).toReal := by
  classical
  intro agent source residual perturbed removed
  have denominator : 0 < slotWeight * floor := mul_pos slotPositive positive
  have factorNonnegative : 0 ≤ noise / (slotWeight * floor) :=
    div_nonneg nonnegative denominator.le
  have mixture := phaseTimingComponent_raw_mixture setup mode runtime leaks bounds initial
    horizon
    scheduler bound wellFormed source noise nonnegative small.le slotWeight slotPositive.le
      slotBounded agent (parts (pool agent))
  by_cases sent : (choice.1.getD ⟨none⟩).transmission ≠ none
  · have atom : (perturbed choice).toReal - removed =
        (1 - noise) * (residual choice).toReal := by
      dsimp only [perturbed, removed]
      rw [mixture, mix_apply_toReal, ite_eq_left sent]
      ring
    refine ⟨?_, ?_, ?_⟩
    · rw [atom]
      exact mul_nonneg (sub_nonneg.mpr small.le) ENNReal.toReal_nonneg
    · exact sub_le_self _ (by dsimp only [removed]; rw [ite_eq_left sent]; positivity)
    · rw [atom]
      exact mul_le_mul_of_nonneg_right (by linarith) ENNReal.toReal_nonneg
  · have value : choice.1 = some ⟨none⟩ := by
      obtain ⟨action, _legal, equal⟩ := choice.2
      have noTransmission : action.transmission = none := by
        simpa only [equal, Option.getD_some] using not_ne_iff.mp sent
      have actionEq : action = ⟨none⟩ := by
        cases action with
        | mk transmission => cases noTransmission; rfl
      exact equal.trans (congrArg some actionEq)
    obtain ⟨silent, silentValue, lower⟩ :=
      phaseTimingComponent_value_commitment_silence_lower setup mode runtime leaks bounds plan
        horizon scheduler bound finite wellFormed target approximation maximal fallback n capacity
          floor positive floorBounded floored slotWeight slotPositive slotBounded parts who member
            current trace acting played phase remaining installed committing allValues clear
    have same : choice = silent := Subtype.ext (value.trans silentValue.symm)
    have lowerChoice : slotWeight * floor ≤ (residual choice).toReal := by
      simpa only [same] using lower
    have amplified := mul_le_mul_of_nonneg_left lowerChoice factorNonnegative
    rw [div_mul_cancel₀ _ denominator.ne'] at amplified
    have rawBound := mul_le_mul_of_nonneg_left
      (pmf_toReal_apply_le_one
        ((menu).uniformPolicy initial horizon scheduler who agent.2.1) choice)
        nonnegative
    have retainedBound : (1 - noise) * (residual choice).toReal ≤
        (residual choice).toReal :=
      mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
    have atom : (perturbed choice).toReal =
        noise * (((menu).uniformPolicy initial horizon scheduler who agent.2.1) choice).toReal +
          (1 - noise) * (residual choice).toReal := by
      dsimp only [perturbed]
      rw [mixture, mix_apply_toReal]
    dsimp only [removed]
    rw [ite_eq_right sent, sub_zero]
    refine ⟨ENNReal.toReal_nonneg, le_rfl, ?_⟩
    calc
      _ ≤ noise + (residual choice).toReal := by linarith
      _ ≤ _ := by nlinarith

/-- Original per-owner source-policy and full timing-plan tags can be kept
through the whole response product. Predrawn members may be sparse, and may
differ between owners. Only actual RAW transmission summands are marked. -/
theorem phaseTimingComponent_value_commitment_product_noise
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)] [setup.FiniteInitialLaw]
    (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
    (target : setup.commitRecoveryModel.BehavioralAssessment)
    (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
      (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
      setup.commitRecoveryContinuingChoice)
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (fallback : ∀ who, (N).Policy who)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (positive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (player : Player) (site : setup.commitRecoveryModel.InformationSite player)
      (choice : setup.commitRecoveryModel.Choice player site.1),
      floor ≤ ((approximation.sequence n).strategy player site.1 choice).toReal)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (small : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (owners : Index → Player) (current : Index → (app).Control)
    (traces : ∀ index, (E).Trace (some (current index)))
    (acting : ∀ index, (current index).actor = some (owners index))
    (played : ∀ index, some ((current index).execution.recall (owners index),
      (current index).execution.observe app (owners index)) ∈
        (N).playedInformation (owners index))
    (parts : Index → (p : Pool) → Parts p)
    (members : ∀ index, (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy (owners index))
    (phases : Index → RuntimePhase (serviceGraph setup mode))
    (remaining : Index → List (RuntimePhase (serviceGraph setup mode)))
    (installed : ∀ index, (current index).execution.application.phases =
      phases index :: remaining index)
    (committing : ∀ index, (phases index).kind = .commitment)
    (clear : ∀ index, (current index).execution.application.current.excluded = ∅)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (choices : ∀ index, (N).Choice (owners index)
      (some ((current index).execution.recall (owners index),
        (current index).execution.observe app (owners index)))) :
    let agents := fun index =>
      (⟨owners index, ⟨_, played index⟩⟩ : (N).InformationAgent (N).playedInformation)
    let sources := fun index => setup.commitRecoveryValueAssessment wellFormed
      (approximation.sequence n) (owners index) (members index)
    let residual := fun index => phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (sources index) 0 (by norm_num) (by norm_num) slotWeight
        slotPositive.le slotBounded (agents index) (parts index (pool (agents index)))
    let perturbed := fun index => phaseTimingComponent setup mode runtime leaks bounds initial
      horizon scheduler bound wellFormed (sources index) noise nonnegative small.le slotWeight
        slotPositive.le slotBounded (agents index) (parts index (pool (agents index)))
    let removed := fun index =>
      if ((choices index).1.getD ⟨none⟩).transmission ≠ none then noise *
        (((menu).uniformPolicy initial horizon scheduler (owners index)
          (agents index).2.1) (choices index)).toReal else 0
    (∏ index, (perturbed index (choices index)).toReal) ≤
      (1 + noise / (slotWeight * floor)) ^ Fintype.card Index *
        (∏ index, (residual index (choices index)).toReal) +
      ∑ index, removed index *
        ∏ other ∈ Finset.univ.erase index, (perturbed other (choices other)).toReal := by
  classical
  intro agents sources residual perturbed removed
  have localBound (index : Index) :
      0 ≤ (perturbed index (choices index)).toReal - removed index ∧
      (perturbed index (choices index)).toReal - removed index ≤
        (perturbed index (choices index)).toReal ∧
      (perturbed index (choices index)).toReal - removed index ≤
        (1 + noise / (slotWeight * floor)) * (residual index (choices index)).toReal :=
    phaseTimingComponent_value_commitment_trimmed_atom setup mode runtime leaks bounds plan horizon
      scheduler bound finite wellFormed target approximation maximal fallback n capacity floor
        positive floorBounded floored noise nonnegative small slotWeight slotPositive slotBounded
          (parts index) (owners index) (members index) (current index) (traces index) (acting index)
            (played index) (phases index) (remaining index) (installed index) (committing index)
              allValues (clear index) (choices index)
  have peeling := prod_le_trimmed_add_marked Finset.univ
    (fun index => (perturbed index (choices index)).toReal) removed
    (fun index _ => by dsimp only [removed]; split_ifs <;> positivity)
    (fun index _ => by linarith [(localBound index).1])
  have retained : (∏ index, ((perturbed index (choices index)).toReal - removed index)) ≤
      (1 + noise / (slotWeight * floor)) ^ Fintype.card Index *
        (∏ index, (residual index (choices index)).toReal) := by
    calc
      _ ≤ ∏ index, (1 + noise / (slotWeight * floor)) *
          (residual index (choices index)).toReal :=
        Finset.prod_le_prod₀ (fun index _ => (localBound index).1)
          (fun index _ => (localBound index).2.2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  exact peeling.trans (add_le_add retained le_rfl)

end Vegas
