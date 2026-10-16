/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingCommitmentNoise

/-! # Exact marked transmission contributions across commitment callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Peeling retained nonnegative atoms leaves at most the sum of exact single-coordinate
marked contributions, with every other factor kept at its original value. -/
theorem prod_le_trimmed_add_marked {Index : Type} [DecidableEq Index]
    (indices : Finset Index) (prob removed : Index → ℝ)
    (nonnegative : ∀ index ∈ indices, 0 ≤ removed index)
    (bounded : ∀ index ∈ indices, removed index ≤ prob index) :
    ∏ index ∈ indices, prob index ≤
      (∏ index ∈ indices, (prob index - removed index)) +
        ∑ index ∈ indices, removed index * ∏ other ∈ indices.erase index, prob other := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index rest fresh ih =>
      have restNonnegative : ∀ other ∈ rest, 0 ≤ removed other :=
        fun other member => nonnegative other (Finset.mem_insert_of_mem member)
      have restBounded : ∀ other ∈ rest, removed other ≤ prob other :=
        fun other member => bounded other (Finset.mem_insert_of_mem member)
      have markNonnegative : 0 ≤ ∑ other ∈ rest,
          removed other * ∏ later ∈ rest.erase other, prob later := by
        apply Finset.sum_nonneg
        intro other member
        apply mul_nonneg (restNonnegative other member)
        exact Finset.prod_nonneg fun later laterMember =>
          (restNonnegative later (Finset.mem_of_mem_erase laterMember)).trans
            (restBounded later (Finset.mem_of_mem_erase laterMember))
      have headNonnegative := nonnegative index (Finset.mem_insert_self index rest)
      have headBounded := bounded index (Finset.mem_insert_self index rest)
      have upper := mul_le_mul_of_nonneg_left (ih restNonnegative restBounded)
        (sub_nonneg.mpr headBounded)
      have replacement := mul_le_mul_of_nonneg_right
        (sub_le_self (prob index) headNonnegative) markNonnegative
      have erased :
          (∑ other ∈ insert index rest,
            removed other * ∏ later ∈ (insert index rest).erase other, prob later) =
          removed index * (∏ later ∈ rest, prob later) +
            prob index * ∑ other ∈ rest,
              removed other * ∏ later ∈ rest.erase other, prob later := by
        rw [Finset.sum_insert fresh, Finset.erase_insert fresh, Finset.mul_sum]
        congr 1
        apply Finset.sum_congr rfl
        intro other member
        have different : index ≠ other := fun equal => fresh (equal ▸ member)
        rw [Finset.erase_insert_of_ne different,
          Finset.prod_insert (fun present => fresh (Finset.mem_of_mem_erase present))]
        ring
      rw [Finset.prod_insert fresh, Finset.prod_insert fresh, erased]
      nlinarith

private theorem ownPlay_ofFn
    {Player : Type} {Protocol : GameTheory.Protocol.ExecutionProtocol Player}
    (model : GameTheory.Protocol.InformationModel Protocol)
    (who : Player) (policy : model.BehavioralPolicy who)
    {count : Nat} (records : Fin count → model.InfoState who × Protocol.Action who) :
    model.ownPlayReachProbability policy (List.ofFn records) =
      ∏ index, (((policy (records index).1).map Subtype.val)
        (some (records index).2)).toReal := by
  induction count with
  | zero => simp [InformationModel.ownPlayReachProbability]
  | succ count ih =>
      rw [List.ofFn_succ, InformationModel.ownPlayReachProbability, Fin.prod_univ_succ]
      rw [ih]

private theorem ownPlay_agents_of_records
    {Player : Type} {Protocol : GameTheory.Protocol.ExecutionProtocol Player}
    (model : GameTheory.Protocol.InformationModel Protocol)
    (sites : ∀ who, Finset (model.InfoState who))
    (fallback : ∀ who, model.Policy who)
    (laws : ∀ agent : model.InformationAgent sites, PMF (model.Choice agent.1 agent.2.1))
    (who : Player) (records : List (model.InfoState who × Protocol.Action who))
    (present : ∀ index : Fin records.length, (records[index.val]).1 ∈ sites who)
    (choices : ∀ index : Fin records.length, model.Choice who (records[index.val]).1)
    (values : ∀ index, (choices index).1 = some (records[index.val]).2) :
    model.ownPlayReachProbability (model.agentBehavior sites fallback laws who) records =
      ∏ index : Fin records.length,
        (laws ⟨who, ⟨(records[index.val]).1, present index⟩⟩ (choices index)).toReal := by
  classical
  have array := ownPlay_ofFn model who (model.agentBehavior sites fallback laws who)
    (fun index : Fin records.length => records[index.val])
  simp only [List.ofFn_getElem] at array
  rw [array]
  apply Finset.prod_congr rfl
  intro index _
  rw [← values index, pmf_map_apply_of_injective _ Subtype.val_injective]
  exact congrArg (fun law : PMF (model.Choice who (records[index.val]).1) =>
    (law (choices index)).toReal)
      (model.agentBehavior_at sites fallback laws ⟨who, ⟨(records[index.val]).1, present index⟩⟩)

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

include maximal

/-- At finitely many genuine clear commitment callbacks, the SAME zero-noise
response product bounds all retained mass. The error is exactly the sum of
marked RAW transmissions times every other original noisy response atom.
No lower bound on an information-fiber mass is required. -/
theorem phaseTimingComponent_commitment_product_noise
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ ((approximation.sequence n).strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (agents : Index → (N).InformationAgent (N).playedInformation)
    (weights : ∀ index, PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon
      scheduler bound (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler
        bound (agents index))))
    (choices : ∀ index, (N).Choice (agents index).1 (agents index).2.1)
    (callbacks : ∀ index, ∃ (current : (app).Control) (_trace : (E).Trace (some current))
      (phase : RuntimePhase (serviceGraph setup mode))
      (remaining : List (RuntimePhase (serviceGraph setup mode))),
      current.actor = some (agents index).1 ∧
      (agents index).2.1 = some (current.execution.recall (agents index).1,
        current.execution.observe app (agents index).1) ∧
      current.execution.application.phases = phase :: remaining ∧ phase.kind = .commitment ∧
      current.execution.application.current.excluded = ∅)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    let residual := fun index => weights index |>.bind
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotPositive.le slotBounded (agents index))
    let perturbed := fun index => weights index |>.bind
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
          slotPositive.le slotBounded (agents index))
    let removed := fun index =>
      if ((choices index).1.getD ⟨none⟩).transmission ≠ none then noise *
        (((menu).uniformPolicy initial horizon scheduler (agents index).1
          (agents index).2.1) (choices index)).toReal else 0
    (∏ index, (perturbed index (choices index)).toReal) ≤
      (1 + noise / (slotWeight * floor)) ^ Fintype.card Index *
        (∏ index, (residual index (choices index)).toReal) +
      ∑ index, removed index *
        ∏ other ∈ Finset.univ.erase index, (perturbed other (choices other)).toReal := by
  classical
  intro residual perturbed removed
  have localBound index :
      0 ≤ (perturbed index (choices index)).toReal - removed index ∧
      (perturbed index (choices index)).toReal - removed index ≤
        (perturbed index (choices index)).toReal ∧
      (perturbed index (choices index)).toReal - removed index ≤
        (1 + noise / (slotWeight * floor)) * (residual index (choices index)).toReal := by
    obtain ⟨current, trace, phase, remaining, acting, atInput, installed, committing, clear⟩ :=
      callbacks index
    exact phaseTimingComponent_commitment_trimmed_atom setup mode runtime leaks bounds plan
      horizon scheduler bound finite wellFormed target approximation maximal n capacity floor
        floorPositive floorBounded floored noise noiseNonnegative noiseSmall slotWeight
          slotPositive slotBounded (agents index) (weights index) current trace acting atInput
            phase remaining installed committing allValues clear (choices index)
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

/-- The marked product estimate applies to actual own-response records, with
the literal assembled policy at each full input. Earlier and later factors
in each marked term remain the original noisy policy, including omissions
and accepted source failures. -/
theorem phaseTimingComponent_commitment_ownPlay_noise
    [Fintype (E).History] [∀ who, DecidableEq ((N).InfoState who)]
    (fallback : (who : Player) → (N).Policy who)
    (n : Nat) (capacity : horizon ≤ bounds.candidateCount)
    (floor : ℝ) (floorPositive : 0 < floor) (floorBounded : floor ≤ 1)
    (floored : ∀ (who : Player) (site : setup.commitRecoveryModel.InformationSite who)
      (choice : setup.commitRecoveryModel.Choice who site.1),
      floor ≤ ((approximation.sequence n).strategy who site.1 choice).toReal)
    (noise : ℝ) (noiseNonnegative : 0 ≤ noise) (noiseSmall : noise < 1)
    (slotWeight : ℝ) (slotPositive : 0 < slotWeight) (slotBounded : slotWeight ≤ 1)
    (weights : ∀ agent : (N).InformationAgent (N).playedInformation,
      PMF (PhaseTimingPart setup mode runtime leaks bounds initial horizon scheduler bound
        (phaseTimingPool setup mode runtime leaks bounds initial horizon scheduler bound agent)))
    (who : Player) (records : List ((N).InfoState who × (E).Action who))
    (callbacks : ∀ record ∈ records, ∃ (current : (app).Control)
      (_trace : (E).Trace (some current)) (phase : RuntimePhase (serviceGraph setup mode))
      (remaining : List (RuntimePhase (serviceGraph setup mode))),
      current.actor = some who ∧
      record.1 = some (current.execution.recall who, current.execution.observe app who) ∧
      record.2 ∈ PhaseCount.onePacketActions runtime leaks bounds who
        (current.execution.recall who) (current.execution.observe app who) ∧
      current.execution.application.phases = phase :: remaining ∧ phase.kind = .commitment ∧
      current.execution.application.current.excluded = ∅)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    let zero := (N).agentBehavior (N).playedInformation fallback fun agent => weights agent |>.bind
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
          slotPositive.le slotBounded agent)
    let noisy := (N).agentBehavior (N).playedInformation fallback fun agent => weights agent |>.bind
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
          slotPositive.le slotBounded agent)
    let atom := fun record : (N).InfoState who × (E).Action who =>
      (((noisy who record.1).map Subtype.val) (some record.2)).toReal
    let raw := fun record : (N).InfoState who × (E).Action who =>
      if record.2.transmission ≠ none then noise *
        ((((menu).uniformPolicy initial horizon scheduler who record.1).map Subtype.val)
          (some record.2)).toReal else 0
    (N).ownPlayReachProbability (noisy who) records ≤
      (1 + noise / (slotWeight * floor)) ^ records.length *
        (N).ownPlayReachProbability (zero who) records +
      ∑ index : Fin records.length, raw records[index.val] *
        ∏ other ∈ Finset.univ.erase index, atom records[other.val] := by
  classical
  intro zero noisy atom raw
  have played (index : Fin records.length) :
      (records[index.val]).1 ∈ (N).playedInformation who := by
    obtain ⟨current, trace, phase, remaining, acting, atInput, _⟩ :=
      callbacks records[index.val] (List.getElem_mem index.isLt)
    let history : (E).History := ⟨some current, trace⟩
    have running : ¬ (E).terminal history.state := by
      change ¬ (current.remaining = 0 ∧ current.actor = none)
      simp only [acting, reduceCtorEq, and_false, not_false_eq_true]
    have present := (N).mem_playedInformation (who := who) (history := history) running
    change ((menu).signals initial horizon scheduler).infoOf who trace ∈ _ at present
    rw [(menu).info initial horizon scheduler who trace] at present
    rw [atInput]
    simpa only [ReactiveApplication.observe, acting, ↓reduceIte] using present
  let agents : Fin records.length → (N).InformationAgent (N).playedInformation :=
    fun index => ⟨who, ⟨(records[index.val]).1, played index⟩⟩
  let choices : ∀ index, (N).Choice (agents index).1 (agents index).2.1 := fun index =>
    ⟨some (records[index.val]).2, by
      obtain ⟨current, trace, phase, remaining, acting, atInput, legal, _⟩ :=
        callbacks records[index.val] (List.getElem_mem index.isLt)
      change some (records[index.val]).2 ∈ (N).menu who (records[index.val]).1
      rw [atInput]
      exact ⟨(records[index.val]).2, legal, rfl⟩⟩
  have actual (index : Fin records.length) : ∃ (current : (app).Control)
      (_trace : (E).Trace (some current))
      (phase : RuntimePhase (serviceGraph setup mode))
      (remaining : List (RuntimePhase (serviceGraph setup mode))),
      current.actor = some (agents index).1 ∧
      (agents index).2.1 = some (current.execution.recall (agents index).1,
        current.execution.observe app (agents index).1) ∧
      current.execution.application.phases = phase :: remaining ∧ phase.kind = .commitment ∧
      current.execution.application.current.excluded = ∅ := by
    obtain ⟨current, trace, phase, remaining, acting, atInput, _legal, installed, committing,
      clear⟩ := callbacks records[index.val] (List.getElem_mem index.isLt)
    exact ⟨current, trace, phase, remaining, acting, atInput, installed, committing, clear⟩
  let residual := fun index : Fin records.length => weights (agents index) |>.bind
    (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed (approximation.sequence n) 0 (by norm_num) (by norm_num) slotWeight
        slotPositive.le slotBounded (agents index))
  let perturbed := fun index : Fin records.length => weights (agents index) |>.bind
    (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
      wellFormed (approximation.sequence n) noise noiseNonnegative noiseSmall.le slotWeight
        slotPositive.le slotBounded (agents index))
  have noisyEq (index : Fin records.length) : noisy who (records[index.val]).1 = perturbed index :=
    (N).agentBehavior_at _ _ _ (agents index)
  have mapped (index : Fin records.length) (law : PMF ((N).Choice who (records[index.val]).1)) :
      ((law.map Subtype.val) (some (records[index.val]).2)) = law (choices index) :=
    pmf_map_apply_of_injective law Subtype.val_injective (choices index)
  have rawAtom (index : Fin records.length) : raw records[index.val] =
      if ((choices index).1.getD ⟨none⟩).transmission ≠ none then noise *
        (((menu).uniformPolicy initial horizon scheduler (agents index).1
          (agents index).2.1) (choices index)).toReal else 0 := by
    dsimp only [raw]
    rw [mapped]
    rfl
  have noisyProduct : (N).ownPlayReachProbability (noisy who) records =
      ∏ index : Fin records.length, (perturbed index (choices index)).toReal :=
    ownPlay_agents_of_records (N) (N).playedInformation fallback _ who records played choices
      (fun _ => rfl)
  have zeroProduct : (N).ownPlayReachProbability (zero who) records =
      ∏ index : Fin records.length, (residual index (choices index)).toReal :=
    ownPlay_agents_of_records (N) (N).playedInformation fallback _ who records played choices
      (fun _ => rfl)
  have atomEq (index : Fin records.length) : atom records[index.val] =
      (perturbed index (choices index)).toReal := by
    dsimp only [atom]
    rw [noisyEq, mapped]
  have product := phaseTimingComponent_commitment_product_noise setup mode runtime leaks bounds
    plan horizon scheduler bound finite wellFormed target approximation maximal n capacity floor
      floorPositive floorBounded floored noise noiseNonnegative noiseSmall slotWeight slotPositive
        slotBounded agents (fun index => weights (agents index)) choices actual allValues
  change (∏ index, (perturbed index (choices index)).toReal) ≤ _ at product
  rw [noisyProduct, zeroProduct]
  simp only [Fintype.card_fin, ← rawAtom] at product
  simpa only [atomEq] using product

end Vegas
