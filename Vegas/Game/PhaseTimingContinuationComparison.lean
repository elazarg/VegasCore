/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingContinuationNoise
import Vegas.Game.PhaseTimingTaggedNoise
import Vegas.Pending.PhaseCommitmentMenuShape

/-! # Same original member profiles on actual current-block continuation paths -/

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
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).InfoState who)]

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

private theorem plan_profile_atom
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (played : some (past, view) ∈ (N).playedInformation who)
    (choice : (N).Choice who (some (past, view))) :
    (((phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
      fallback wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
        parts who (some (past, view))).map Subtype.val) choice.1) =
      (phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
        wellFormed source noise nonnegative bounded slotWeight slotNonnegative slotBounded
          ⟨who, ⟨_, played⟩⟩ (parts who (pool ⟨who, ⟨_, played⟩⟩))) choice := by
  rw [pmf_map_apply_of_injective _ Subtype.val_injective]
  exact congrArg (fun law : PMF ((N).Choice who (some (past, view))) => law choice)
    ((N).agentBehavior_at _ _ _ ⟨who, ⟨some (past, view), played⟩⟩)

/-- On an actual full-entry to clear ready commitment path, removing only
foreign RAW transmissions compares the SAME immutable source members and full
timing plans. The focal intervention is fixed in both laws. The exact marked
terms retain every other original noisy response and the genuine common
transition factor; no information-fiber denominator is assumed. -/
theorem phase_timing_continuation_path_noise
    [setup.FiniteInitialLaw]
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
    (parts : Player → (p : Pool) → Parts p)
    (members : ∀ who, (setup.informationModel
      (CommitmentInterface.forfeiture setup.program)).Policy who)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix entryTrace finalTrace)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : entry.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : final.execution.application.current.excluded = ∅)
    (ready : final.execution.application.current.native.config.cut.Ready event) :
    let sources := fun who => setup.commitRecoveryValueAssessment wellFormed
      (approximation.sequence n) who (members who)
    let zero := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) 0 (by norm_num) (by norm_num) slotWeight
          slotPositive.le slotBounded parts who) focal intervention
    let noisy := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) noise nonnegative small.le slotWeight
          slotPositive.le slotBounded parts who) focal intervention
    ∃ records : ∀ who, List ((N).InfoState who × (E).Action who),
      (∀ who, (N).ownPlay who finalTrace = records who ++ (N).ownPlay who entryTrace) ∧
      (∀ who record, record ∈ records who → record.2.transmission ≠ none →
        ∃ event serial preparation evidence,
          record.2 = ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩,
            evidence⟩⟩) ∧
      ∃ chance : ℝ, 0 ≤ chance ∧
        (∀ profile : ∀ who, (N).BehavioralPolicy who,
          (((N).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
            ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal =
            chance * ∏ who, (N).ownPlayReachProbability (profile who) (records who)) ∧
        let positions := Σ who, Fin (records who).length
        let atom := fun index : positions =>
          (((noisy index.1 (records index.1)[index.2.val].1).map Subtype.val)
            (some (records index.1)[index.2.val].2)).toReal
        let removed := fun index : positions =>
          if index.1 ≠ focal ∧ (records index.1)[index.2.val].2.transmission ≠ none then noise *
            ((((menu).uniformPolicy initial horizon scheduler index.1
              (records index.1)[index.2.val].1).map Subtype.val)
                (some (records index.1)[index.2.val].2)).toReal else 0
        (((N).runBehavioralFrom noisy (finalTrace.length - entryTrace.length)
          ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal ≤
          (1 + noise / (slotWeight * floor)) ^ Fintype.card positions *
            (((N).runBehavioralFrom zero (finalTrace.length - entryTrace.length)
              ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal +
          chance * ∑ index, removed index * ∏ other ∈ Finset.univ.erase index, atom other := by
  classical
  intro sources zero noisy
  obtain ⟨records, recordEq, callbacks, chance, chanceNonnegative, factor⟩ :=
    phase_timing_continuation_callback_factor runtime leaks bounds initial horizon scheduler entry
      final entryTrace finalTrace isPrefix phase remaining installed committing event inside clear
        ready
  have bindingRecord (who : Player) (record : (N).InfoState who × (E).Action who)
      (member : record ∈ records who) (sent : record.2.transmission ≠ none) :
      ∃ event serial preparation evidence,
        record.2 = ⟨some ⟨⟨.commitment event (who, .prepared serial), preparation⟩, evidence⟩⟩ := by
    obtain ⟨current, trace, _earlier, _later, _acting, _atInput, offered, currentInstalled,
      currentCommitting, _currentClear⟩ := callbacks who record member
    cases transmitted : record.2.transmission with
    | none => exact (sent transmitted).elim
    | some material =>
        have actionEq : record.2 = ⟨some material⟩ := by
          exact congrArg (fun packet => (⟨packet⟩ : (app).Action)) transmitted
        rw [actionEq] at offered
        obtain ⟨event, serial, call⟩ := PhaseCount.onePacket_commitment_shape runtime leaks
          bounds current.execution who phase remaining currentInstalled currentCommitting material
            offered
        rcases material with ⟨⟨packet, preparation⟩, evidence⟩
        change packet = .commitment event (who, .prepared serial) at call
        cases call
        exact ⟨event, serial, preparation, evidence, actionEq⟩
  refine ⟨records, recordEq, bindingRecord, chance, chanceNonnegative, factor, ?_⟩
  intro positions atom removed
  let referenceAtom := fun index : positions =>
    (((zero index.1 (records index.1)[index.2.val].1).map Subtype.val)
      (some (records index.1)[index.2.val].2)).toReal
  have ratioNonnegative : 0 ≤ noise / (slotWeight * floor) :=
    div_nonneg nonnegative (mul_pos slotPositive positive).le
  have localBound (index : positions) :
      0 ≤ atom index - removed index ∧ atom index - removed index ≤ atom index ∧
      atom index - removed index ≤
        (1 + noise / (slotWeight * floor)) * referenceAtom index := by
    let record := (records index.1)[index.2.val]
    by_cases same : index.1 = focal
    · have lawEq : noisy index.1 record.1 = zero index.1 record.1 := by
        subst focal
        simp only [noisy, zero, Function.update_self]
      have marked : removed index = 0 := by simp only [removed, same, ne_self_iff_false,
        false_and, ↓reduceIte]
      have atomEq : atom index = referenceAtom index := by
        dsimp only [atom, referenceAtom]
        rw [lawEq]
      rw [marked, sub_zero, atomEq]
      refine ⟨ENNReal.toReal_nonneg, le_rfl, ?_⟩
      have nonnegativeAtom : 0 ≤ referenceAtom index := ENNReal.toReal_nonneg
      nlinarith [mul_nonneg ratioNonnegative nonnegativeAtom]
    · obtain ⟨current, trace, _earlier, _later, acting, atInput, offered, currentInstalled,
        currentCommitting, currentClear⟩ :=
        callbacks index.1 record (List.getElem_mem index.2.isLt)
      have running : ¬ (E).terminal (some current) := by
        change ¬ (current.remaining = 0 ∧ current.actor = none)
        simp only [acting, reduceCtorEq, and_false, not_false_eq_true]
      have played := (N).mem_playedInformation (who := index.1)
        (history := ⟨some current, trace⟩) running
      have input : (N).infoOf index.1 trace =
          some (current.execution.recall index.1, current.execution.observe app index.1) :=
        ((menu).info initial horizon scheduler index.1 trace).trans (by
          simp only [ReactiveApplication.observe, acting, ite_true])
      rw [input] at played
      let choice : (N).Choice index.1
          (some (current.execution.recall index.1, current.execution.observe app index.1)) :=
        ⟨some record.2, ⟨record.2, offered, rfl⟩⟩
      have noisyAtom : atom index =
          ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed (sources index.1) noise nonnegative small.le slotWeight slotPositive.le
              slotBounded ⟨index.1, ⟨_, played⟩⟩
                (parts index.1 (pool ⟨index.1, ⟨_, played⟩⟩))) choice).toReal := by
        dsimp only [atom, noisy]
        rw [Function.update_of_ne same, atInput]
        exact congrArg ENNReal.toReal (plan_profile_atom setup mode runtime leaks bounds plan
          horizon scheduler bound fallback wellFormed (sources index.1) noise nonnegative small.le
            slotWeight slotPositive.le slotBounded parts index.1 _ _ played choice)
      have zeroAtom : referenceAtom index =
          ((phaseTimingComponent setup mode runtime leaks bounds initial horizon scheduler bound
            wellFormed (sources index.1) 0 (by norm_num) (by norm_num) slotWeight slotPositive.le
              slotBounded ⟨index.1, ⟨_, played⟩⟩
                (parts index.1 (pool ⟨index.1, ⟨_, played⟩⟩))) choice).toReal := by
        dsimp only [referenceAtom, zero]
        rw [Function.update_of_ne same, atInput]
        exact congrArg ENNReal.toReal (plan_profile_atom setup mode runtime leaks bounds plan
          horizon scheduler bound fallback wellFormed (sources index.1) 0 (by norm_num)
            (by norm_num) slotWeight slotPositive.le slotBounded parts index.1 _ _ played choice)
      have rawAtom : removed index =
          if (choice.1.getD ⟨none⟩).transmission ≠ none then noise *
            (((menu).uniformPolicy initial horizon scheduler index.1
              (some (current.execution.recall index.1, current.execution.observe app index.1)))
                choice).toReal else 0 := by
        dsimp only [removed]
        by_cases sent : record.2.transmission ≠ none
        · rw [ite_eq_left ⟨same, sent⟩, atInput]
          simp only [choice, Option.getD_some]
          rw [ite_eq_left sent]
          exact congrArg (fun mass : ENNReal => noise * mass.toReal)
            (pmf_map_apply_of_injective _ Subtype.val_injective choice)
        · rw [ite_eq_right (fun pair => sent pair.2)]
          simp only [choice, Option.getD_some]
          rw [ite_eq_right sent]
      rw [noisyAtom, zeroAtom, rawAtom]
      exact phaseTimingComponent_value_commitment_trimmed_atom setup mode runtime leaks bounds
        plan horizon scheduler bound finite wellFormed target approximation maximal fallback n
          capacity floor positive floorBounded floored noise nonnegative small slotWeight
            slotPositive slotBounded (parts index.1) index.1 (members index.1) current trace acting
              played phase remaining currentInstalled currentCommitting allValues currentClear
                choice
  have peeling := prod_le_trimmed_add_marked Finset.univ atom removed
    (fun index _ => by dsimp only [removed]; split_ifs <;> positivity)
    (fun index _ => by linarith [(localBound index).1])
  have retained : (∏ index, (atom index - removed index)) ≤
      (1 + noise / (slotWeight * floor)) ^ Fintype.card positions *
        ∏ index, referenceAtom index := by
    calc
      _ ≤ ∏ index, (1 + noise / (slotWeight * floor)) * referenceAtom index :=
        Finset.prod_le_prod₀ (fun index _ => (localBound index).1)
          (fun index _ => (localBound index).2.2)
      _ = _ := by rw [Finset.prod_mul_distrib]; simp
  have products (profile : ∀ who, (N).BehavioralPolicy who) :
      (∏ index : positions, (((profile index.1 (records index.1)[index.2.val].1).map Subtype.val)
        (some (records index.1)[index.2.val].2)).toReal) =
        ∏ who, (N).ownPlayReachProbability (profile who) (records who) := by
    rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro who _
    have equal := (N).ownPlayReachProbability_ofFn who (profile who)
      (fun index : Fin (records who).length => (records who)[index.val])
    simpa only [List.ofFn_getElem] using equal.symm
  have bounded := peeling.trans (add_le_add retained le_rfl)
  have weighted := mul_le_mul_of_nonneg_left bounded chanceNonnegative
  dsimp only [atom, referenceAtom] at weighted
  rw [products noisy, products zero, mul_add] at weighted
  rw [factor noisy, factor zero]
  nlinarith only [weighted]

end Vegas
