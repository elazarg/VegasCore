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
/-- Every zero-RAW member path survives with the original raw-mixture
retention factor, including after arbitrary correlated full entry memories.
The SAME focal intervention is used in both actual stopped profiles. -/
theorem phase_timing_continuation_stopped_lower
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (sources : Player → setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix entryTrace finalTrace)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : entry.execution.application.phases = phase :: remaining)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (clear : final.execution.application.current.excluded = ∅)
    (ready : final.execution.application.current.native.config.cut.Ready event)
    (certificate : (E).WellFoundedHistories) (site : (N).InformationSite focal)
    (atSite : (N).infoOf focal finalTrace = site.1) :
    let zero := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded parts who) focal intervention
    let noisy := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) noise nonnegative bounded slotWeight
          slotNonnegative slotBounded parts who) focal intervention
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ final.execution.application.attempt ∨
          (N).infoOf focal history.trace = site.1
    (1 - noise) ^ (Fintype.card Player * (2 * horizon + 1)) *
        (((N).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
          ⟨some final, finalTrace⟩).toReal ≤
      (((N).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
        ⟨some final, finalTrace⟩).toReal := by
  classical
  subst initial
  intro zero noisy stopped
  have choices (who : Player) (input : (baseN).InfoState who)
      (choice : (baseN).Choice who input) :
      (1 - noise) * ((zero who input) choice).toReal ≤ ((noisy who input) choice).toReal := by
    by_cases same : who = focal
    · subst who
      simp only [zero, noisy, Function.update_self]
      exact mul_le_of_le_one_left ENNReal.toReal_nonneg (by linarith)
    · simp only [zero, noisy, Function.update_of_ne same]
      exact phaseTimingPlanProfile_noise_lower setup mode runtime leaks bounds baseInitial horizon
        scheduler bound fallback wellFormed (sources who) noise nonnegative bounded slotWeight
          slotNonnegative slotBounded parts who input choice
  have lower := (baseN).runBehavioralFrom_domination_of_supported_choices zero noisy (1 - noise)
    (sub_nonneg.mpr bounded) ⟨some entry, entryTrace⟩
      (fun _ history _ who choice => choices who ((baseN).infoOf who history.trace) choice)
        (finalTrace.length - entryTrace.length) ⟨some final, finalTrace⟩
  have depth := (app).trace_bound baseInitial horizon scheduler
    ((menu).toRawTrace baseInitial horizon scheduler finalTrace)
  rw [ReactiveApplication.ResponseMenu.toRawTrace_length] at depth
  have fuel : finalTrace.length - entryTrace.length ≤ 2 * horizon + 1 := by omega
  have powers := pow_le_pow_of_le_one (sub_nonneg.mpr bounded) (by linarith : 1 - noise ≤ 1)
    (Nat.mul_le_mul_left (Fintype.card Player) fuel)
  have retained := (mul_le_mul_of_nonneg_right powers (ENNReal.toReal_nonneg : 0 ≤
    (((baseN).runBehavioralFrom zero (finalTrace.length - entryTrace.length)
      ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal)).trans lower
  have initialized : baseInitial =
      (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan) := by
    simp only [PMF.map_comp, Function.comp_def]
  have untilAtom (profile : ∀ who, (baseN).BehavioralPolicy who) :
      (baseN).runBehavioralUntil certificate profile stopped ⟨some entry, entryTrace⟩
          ⟨some final, finalTrace⟩ =
        (baseN).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
          ⟨some entry, entryTrace⟩ ⟨some final, finalTrace⟩ := by
    convert! (phase_current_attempt_until_atom runtime leaks bounds baseInitial horizon
      scheduler plan
      (setup.initialLaw.map encodeInputs) initialized certificate entry final entryTrace finalTrace
        isPrefix phase remaining installed event inside clear ready focal site atSite profile)
      using 1
    apply congrArg (fun stopping : (baseE).History → Prop =>
      (baseN).runBehavioralUntil certificate profile stopping ⟨some entry, entryTrace⟩
        ⟨some final, finalTrace⟩)
    funext history
    rcases history with ⟨state, trace⟩
    cases state <;> rfl
  rw [untilAtom zero, untilAtom noisy]
  exact retained

include initialLaw in
/-- Summing actual native information rows retains the same zero-RAW law
with one uniform finite-horizon factor. No positive input-mass floor or fresh
entry/source prior is required. -/
theorem phase_timing_continuation_fiber_lower
    (fallback : ∀ who, (N).Policy who) (wellFormed : setup.WellFormed)
    (sources : Player → setup.commitRecoveryModel.BehavioralAssessment)
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (parts : Player → (p : Pool) → Parts p)
    (focal : Player) (intervention : (N).BehavioralPolicy focal)
    (entry original : (app).Control)
    (entryTrace : (E).Trace (some entry)) (originalTrace : (E).Trace (some original))
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : entry.execution.application.phases = phase :: remaining)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩)
    (active : original.actor = some focal)
    (certificate : (E).WellFoundedHistories) (site : (N).InformationSite focal)
    (atSite : (N).infoOf focal originalTrace = site.1)
    (rows : Finset ((N).InformationHistory focal site.1)) :
    let zero := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) 0 (by norm_num) (by norm_num) slotWeight
          slotNonnegative slotBounded parts who) focal intervention
    let noisy := Function.update (fun who =>
      phaseTimingPlanProfile setup mode runtime leaks bounds initial horizon scheduler bound
        fallback wellFormed (sources who) noise nonnegative bounded slotWeight
          slotNonnegative slotBounded parts who) focal intervention
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ original.execution.application.attempt ∨
          (N).infoOf focal history.trace = site.1
    (1 - noise) ^ (Fintype.card Player * (2 * horizon + 1)) *
        (∑ history ∈ rows,
          (((N).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
            history.1).toReal) ≤
      ∑ history ∈ rows,
        (((N).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
          history.1).toReal := by
  classical
  subst initial
  intro zero noisy stopped
  have genuine := phase_binding_fiber_genuine setup mode runtime leaks bounds plan horizon scheduler
    focal site original originalTrace atSite active event clear request
  have each (history : (baseN).InformationHistory focal site.1) :
      (1 - noise) ^ (Fintype.card Player * (2 * horizon + 1)) *
          (((baseN).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩)
            history.1).toReal ≤
        (((baseN).runBehavioralUntil certificate noisy stopped ⟨some entry, entryTrace⟩)
          history.1).toReal := by
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
      have lower := phase_timing_continuation_stopped_lower setup mode runtime leaks bounds plan
        _ rfl horizon scheduler bound fallback wellFormed sources noise nonnegative bounded
          slotWeight
          slotNonnegative slotBounded parts focal intervention entry current entryTrace trace
            isPrefix phase remaining installed event inside currentClear currentRequest.2.2.1
              certificate site same
      dsimp only at lower
      convert! lower using 1 <;> congr 3
      all_goals
        congr 1
        funext history
        rcases history with ⟨state, historyTrace⟩
        cases state with
        | none => rfl
        | some control => simp only [stopped, attemptEq]
    · have noMass : (baseN).runBehavioralUntil certificate zero stopped ⟨some entry, entryTrace⟩
          history.1 = 0 := by
        apply (PMF.apply_eq_zero_iff _ _).mpr
        intro member
        exact isPrefix ((baseN).runBehavioralUntil_support_prefix certificate zero stopped
          ⟨some entry, entryTrace⟩ history.1 member)
      rw [noMass, ENNReal.toReal_zero, mul_zero]
      exact ENNReal.toReal_nonneg
  rw [Finset.mul_sum]
  exact Finset.sum_le_sum (fun history _ => each history)

end Vegas
