/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingStoppedComparison
import Vegas.Game.PhaseOpponentRawBindingMass
import Vegas.Game.PhaseTimingTaggedNoise
import Vegas.Pending.PhaseCommitmentMenuShape
import Vegas.Pending.PhaseAttemptInputAtom

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
  (initial : PMF (phaseApplication runtime leaks).State)
  (initialLaw : initial = setup.initialLaw.map fun draw =>
    PhaseRuntimeState.initial plan (encodeInputs draw))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)
  [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    initial horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    initial horizon scheduler).InfoState who)]

local notation "app" => phaseApplication runtime leaks
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

local notation "baseInitial" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "baseN" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) baseInitial horizon scheduler
local notation "baseE" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) baseInitial horizon scheduler

include initialLaw in
/-- The actual complete information fiber inherits the stopped path bound.
All geometry and literal RAW-binding marks are derived from genuine counted
histories; every other noisy factor and the full original entry are retained. -/
theorem phase_timing_continuation_fiber_noise
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
    (entry original : (app).Control)
    (entryTrace : (E).Trace (some entry)) (originalTrace : (E).Trace (some original))
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : entry.execution.application.phases = phase :: remaining)
    (committing : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (allValues : ∀ payload, ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩)
    (active : original.actor = some focal)
    (certificate : (E).WellFoundedHistories) (site : (N).InformationSite focal)
    (atSite : (N).infoOf focal originalTrace = site.1)
    (rows : Finset ((N).InformationHistory focal site.1)) :
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
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ original.execution.application.attempt ∨
          (N).infoOf focal history.trace = site.1
    ∃ records : (N).InformationHistory focal site.1 →
        ∀ who, List ((N).InfoState who × (E).Action who),
      ∃ chance : (N).InformationHistory focal site.1 → ℝ,
        (∀ history, 0 ≤ chance history) ∧
        (∀ history who record, record ∈ records history who → record.2.transmission ≠ none →
          phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who
            record) ∧
        (∀ history, chance history ≠ 0 →
          TracePrefix entryTrace history.1.trace ∧
          (∀ who, (N).ownPlay who history.1.trace =
            (records history) who ++ (N).ownPlay who entryTrace) ∧
          (∀ who record, record ∈ (records history) who →
            ∃ (before : (E).History) (joint : ∀ player, Option ((E).Action player))
              (legal : (E).Legal before.state joint) (next : (E).State)
              (realized : next ∈ ((E).step before.state ⟨joint, legal⟩).support),
              TracePrefix entryTrace before.trace ∧
              TracePrefix (before.trace.extend joint legal realized) history.1.trace ∧
              (N).infoOf who before.trace = record.1 ∧ joint who = some record.2) ∧
          (∀ profile : ∀ who, (N).BehavioralPolicy who,
            (((N).runBehavioralFrom profile (history.1.trace.length - entryTrace.length)
              ⟨some entry, entryTrace⟩) history.1).toReal =
                chance history *
                  ∏ who, (N).ownPlayReachProbability (profile who) ((records history) who))) ∧
        let error := fun history : (N).InformationHistory focal site.1 =>
          chance history * ∑ index : (Σ who, Fin (records history who).length),
            (if index.1 ≠ focal ∧ (records history index.1)[index.2.val].2.transmission ≠ none
              then phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler
                noise index.1 (records history index.1)[index.2.val] else 0) *
              ∏ other ∈ Finset.univ.erase index,
                (((noisy other.1 (records history other.1)[other.2.val].1).map Subtype.val)
                  (some (records history other.1)[other.2.val].2)).toReal
        ((∑ history ∈ rows,
          (((N).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
            history.1).toReal) ≤
          (1 + noise / (slotWeight * floor)) ^ (Fintype.card Player * (2 * horizon + 1)) *
            (∑ history ∈ rows,
              (((N).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
                history.1).toReal) + (∑ history ∈ rows, error history)) ∧
          (∀ history : (N).InformationHistory focal site.1,
            (((N).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
              history.1).toReal ≤
                (1 + noise / (slotWeight * floor)) ^
                    (Fintype.card Player * (2 * horizon + 1)) *
                  (((N).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
                    history.1).toReal + error history) := by
  classical
  subst initial
  intro sources zero noisy stopped
  let B := 1 + noise / (slotWeight * floor)
  have one_le_B : 1 ≤ B := by
    have positiveRatio := div_nonneg nonnegative (mul_pos slotPositive positive).le
    dsimp only [B]
    linarith
  have genuine := phase_binding_fiber_genuine setup mode runtime leaks bounds plan horizon scheduler
    focal site original originalTrace atSite active event clear request
  have each (history : (baseN).InformationHistory focal site.1) :
      ∃ records : ∀ who, List ((baseN).InfoState who × (baseE).Action who), ∃ chance : ℝ,
        0 ≤ chance ∧
        (∀ who record, record ∈ records who → record.2.transmission ≠ none →
          phaseRawBindingRecord setup mode runtime leaks bounds plan horizon scheduler who record) ∧
        (chance ≠ 0 →
          TracePrefix entryTrace history.1.trace ∧
          (∀ who, (baseN).ownPlay who history.1.trace =
            records who ++ (baseN).ownPlay who entryTrace) ∧
          (∀ who record, record ∈ records who →
            ∃ (before : (baseE).History) (joint : ∀ player, Option ((baseE).Action player))
              (legal : (baseE).Legal before.state joint) (next : (baseE).State)
              (realized : next ∈ ((baseE).step before.state ⟨joint, legal⟩).support),
              TracePrefix entryTrace before.trace ∧
              TracePrefix (before.trace.extend joint legal realized) history.1.trace ∧
              (baseN).infoOf who before.trace = record.1 ∧ joint who = some record.2) ∧
          (∀ profile : ∀ who, (baseN).BehavioralPolicy who,
            (((baseN).runBehavioralFrom profile (history.1.trace.length - entryTrace.length)
              ⟨some entry, entryTrace⟩) history.1).toReal =
                chance * ∏ who, (baseN).ownPlayReachProbability (profile who) (records who))) ∧
        (((baseN).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
          history.1).toReal ≤
          B ^ (Fintype.card Player * (2 * horizon + 1)) *
            (((baseN).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
              history.1).toReal + chance *
            ∑ index : (Σ who, Fin (records who).length),
              (if index.1 ≠ focal ∧ (records index.1)[index.2.val].2.transmission ≠ none
                then phaseRawMixtureAtom setup mode runtime leaks bounds plan horizon scheduler
                  noise index.1 (records index.1)[index.2.val] else 0) *
                ∏ other ∈ Finset.univ.erase index,
                  (((noisy other.1 (records other.1)[other.2.val].1).map Subtype.val)
                    (some (records other.1)[other.2.val].2)).toReal := by
    by_cases isPrefix : TracePrefix entryTrace history.1.trace
    · obtain ⟨current, stateEq, acting, currentClear, currentRequest⟩ := genuine history
      rcases history with ⟨⟨state, trace⟩, same⟩
      cases stateEq
      have infoEq := same.trans atSite.symm
      change ((menu).signals baseInitial horizon scheduler).infoOf focal trace =
        ((menu).signals baseInitial horizon scheduler).infoOf focal originalTrace at infoEq
      rw [ReactiveApplication.ResponseMenu.info, ReactiveApplication.ResponseMenu.info] at infoEq
      simp only [ReactiveApplication.observe, acting, active, ↓reduceIte] at infoEq
      have publicEq := congrArg (fun input => input.2.application.2) (Option.some.inj infoEq)
      have attemptEq := congrArg PhasePublicView.attempt publicEq
      change current.execution.application.attempt = original.execution.application.attempt
        at attemptEq
      obtain ⟨records, recordEq, bindings, chance, chanceNonnegative, factor, bounded⟩ :=
        phase_timing_continuation_stopped_noise setup mode runtime leaks bounds plan horizon
          scheduler bound finite wellFormed target approximation maximal fallback n capacity floor
            positive floorBounded floored noise nonnegative small slotWeight slotPositive
              slotBounded
              parts members focal intervention entry current entryTrace trace isPrefix phase
                remaining installed committing event inside allValues currentClear
                  currentRequest.2.2.1 certificate site same
      obtain ⟨actualRecords, actualEq, provenance, _chance, _nonnegative, _factor⟩ :=
        (baseN).exists_continuation_ownPlay_factor entryTrace trace isPrefix
      have recordsEq : actualRecords = records := by
        funext who
        exact List.append_cancel_right ((actualEq who).symm.trans (recordEq who))
      subst actualRecords
      refine ⟨records, chance, chanceNonnegative, bindings, ?_, ?_⟩
      · intro _nonzero
        exact ⟨isPrefix, recordEq, provenance, factor⟩
      have counts (who : Player) : (records who).length ≤ 2 * horizon + 1 := by
        have lengths := congrArg List.length (recordEq who)
        have full := phase_ownPlay_length_le setup mode runtime leaks bounds plan horizon scheduler
          who ⟨some current, trace⟩
        simp only [List.length_append] at lengths
        change ((baseN).ownPlay who trace).length =
          (records who).length + ((baseN).ownPlay who entryTrace).length at lengths
        change ((baseN).ownPlay who trace).length ≤ 2 * horizon + 1 at full
        omega
      have total : Fintype.card (Σ who, Fin (records who).length) ≤
          Fintype.card Player * (2 * horizon + 1) := by
        simp only [Fintype.card_sigma, Fintype.card_fin]
        calc
          _ ≤ ∑ _who : Player, (2 * horizon + 1) :=
            Finset.sum_le_sum (fun who _ => counts who)
          _ = _ := by simp
      have bigger := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ one_le_B total)
        (ENNReal.toReal_nonneg : 0 ≤
          (((baseN).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
            ⟨some current, trace⟩).toReal)
      have stoppedEq : (fun history : (baseE).History => match history.state with
          | none => False
          | some control => control.execution.application.current.excluded ≠ ∅ ∨
              control.execution.application.attempt ≠ current.execution.application.attempt ∨
              (baseN).infoOf focal history.trace = site.1) = stopped := by
        funext history
        rcases history with ⟨state, trace⟩
        cases state with
        | none => rfl
        | some control => simp only [stopped, attemptEq]
      dsimp only at bounded
      erw [stoppedEq] at bounded
      exact bounded.trans (add_le_add bigger le_rfl)
    · have noMass : (baseN).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩
          history.1 = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro member
        exact isPrefix ((baseN).runBehavioralUntil_support_prefix certificate noisy stopped
          ⟨some entry, entryTrace⟩ history.1 member)
      refine ⟨fun _ => [], 0, le_rfl, ?_, ?_, ?_⟩
      · intro who record member
        cases member
      · intro nonzero
        exact (nonzero rfl).elim
      · rw [noMass, ENNReal.toReal_zero]
        simp only [zero_mul, add_zero]
        positivity
  choose records chance nonnegativeChance bindings provenance bounded using each
  refine ⟨records, chance, nonnegativeChance, bindings, provenance, ?_⟩
  intro error
  constructor
  · calc
      _ ≤ ∑ history ∈ rows, (
          B ^ (Fintype.card Player * (2 * horizon + 1)) *
            (((baseN).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
              history.1).toReal + error history) :=
        Finset.sum_le_sum (fun history _ => bounded history)
      _ = _ := by rw [Finset.sum_add_distrib, Finset.mul_sum]
  · intro history
    exact bounded history

end Vegas
