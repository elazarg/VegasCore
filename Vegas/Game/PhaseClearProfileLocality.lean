/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhasePublicCompletion
import Vegas.Pending.PhaseClearTraceProgress
import Vegas.Game.PhaseOpponentRawBindingMass
import GameTheory.Analysis.Protocol.SequentialOneShot

/-! # Exact recipe locality along actual histories without public exclusions -/

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

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

private theorem queriedInfos_prefix (player : Player) (info : (N).InfoState player) :
    ∀ {state} (trace : (E).Trace state), info ∈ (N).queriedInfos player trace →
      ∃ (before : (E).State) (prior : (E).Trace before),
        TracePrefix prior trace ∧ (N).infoOf player prior = info := by
  intro state trace
  induction trace with
  | start =>
      intro member
      simp only [InformationModel.queriedInfos, List.mem_singleton] at member
      exact ⟨_, .start, .refl, member.symm⟩
  | extend prior joint legal moved ih =>
      intro member
      simp only [InformationModel.queriedInfos, List.mem_cons] at member
      rcases member with current | earlier
      · exact ⟨_, _, .refl, current.symm⟩
      · obtain ⟨before, earlierTrace, retained, same⟩ := ih earlier
        exact ⟨before, earlierTrace, .extend retained joint legal moved, same⟩

/-- Equality at nonexcluded played sites supplies every queried policy law
along an actual clear history. All earlier exclusions are ruled out by the
real monotone runtime, including inactive and zero-probability legal prefixes. -/
theorem phase_clear_profile_queries
    (first second : ∀ player, (N).BehavioralPolicy player)
    (agree : ∀ player (site : (N).InformationSite player),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 →
        first player site.1 = second player site.1)
    (final : (phaseApplication runtime leaks).Control) (finalTrace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅) :
    ∀ player info, info ∈ (N).queriedInfos player finalTrace →
      first player info = second player info := by
  intro player info member
  obtain ⟨state, prior, retained, observed⟩ := queriedInfos_prefix setup mode runtime leaks bounds
    plan
    horizon scheduler player info finalTrace member
  rw [← observed]
  cases state with
  | none =>
      exact (N).behavioral_eq_of_not_active (first player) (second player) prior
        (by simp [ReactiveApplication.ResponseMenu.protocol, ReactiveApplication.actor])
  | some before =>
      by_cases acting : before.actor = some player
      · have beforeClear := (phase_clear_nativeProgress_of_prefix runtime leaks
          (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler before final
            prior finalTrace retained clear).1
        have running : ¬(E).terminal (some before) := by
          change ¬(before.remaining = 0 ∧ before.actor = none)
          rintro ⟨_, impossible⟩
          rw [acting] at impossible
          cases impossible
        obtain ⟨site, siteInfo⟩ := (N).exists_informationSite_of_active player
          ⟨some before, prior⟩ running acting
        rw [← siteInfo]
        apply agree player site
        rintro ⟨past, view, same, excluded⟩
        rw [siteInfo] at same
        have physical : (N).infoOf player prior =
            some (before.execution.recall player,
              before.execution.observe (phaseApplication runtime leaks) player) := by
          change
            ((PhaseCount.onePacketMenu runtime leaks bounds).signals initial horizon
              scheduler).infoOf
              player prior = _
          rw [ReactiveApplication.ResponseMenu.info]
          simp only [ReactiveApplication.observe, acting, ↓reduceIte]
        have inputEq := Option.some.inj (physical.symm.trans same)
        have exclusions := congrArg (fun input => input.2.application.2.excluded) inputEq
        change before.execution.application.current.excluded = view.application.2.excluded
          at exclusions
        exact excluded (exclusions.symm.trans beforeClear)
      · exact (N).behavioral_eq_of_not_active (first player) (second player) prior acting

/-- Actual full reach is local to the clear prefixes, using the existing
queried-information congruence for the SAME behavioral execution runner. -/
theorem phase_clear_historyReach_eq
    (first second : ∀ player, (N).BehavioralPolicy player)
    (agree : ∀ player (site : (N).InformationSite player),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 →
        first player site.1 = second player site.1)
    (final : (phaseApplication runtime leaks).Control) (finalTrace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅) :
    (N).historyReachWeight first ⟨some final, finalTrace⟩ =
      (N).historyReachWeight second ⟨some final, finalTrace⟩ := by
  exact (N).runBehavioral_apply_congr_of_queriedInfos first second finalTrace.length
    ⟨some final, finalTrace⟩
    (phase_clear_profile_queries setup mode runtime leaks bounds plan horizon scheduler first second
      agree final finalTrace clear)

/-- Every recorded own law is an actual earlier queried law. No equality at
arbitrary free inputs is needed. -/
theorem phase_clear_ownPlay_policy_eq
    (first second : ∀ player, (N).BehavioralPolicy player)
    (agree : ∀ player (site : (N).InformationSite player),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 →
        first player site.1 = second player site.1)
    (final : (phaseApplication runtime leaks).Control) (finalTrace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅) (player : Player)
    (record : (N).InfoState player × (E).Action player)
    (member : record ∈ (N).ownPlay player finalTrace) :
    first player record.1 = second player record.1 := by
  obtain ⟨prior, joint, legal, next, moved, fuel, observed, _chosen, reached⟩ :=
    (N).ownPlay_prefix player finalTrace member
  have prefixInfo := (N).queriedInfos_mono_reachesWithin player
    (.step joint legal moved reached) ((N).infoOf_mem_queriedInfos player prior)
  rw [observed] at prefixInfo
  exact phase_clear_profile_queries setup mode runtime leaks bounds plan horizon scheduler first
    second agree final finalTrace clear player record.1 prefixInfo

/-- The actual counterfactual factor also transfers. Positivity follows from
the second profile's genuine full support, not a prescribed likelihood ratio. -/
theorem phase_clear_counterfactualReach_eq
    (first second : ∀ player, (N).BehavioralPolicy player)
    (agree : ∀ player (site : (N).InformationSite player),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 →
        first player site.1 = second player site.1)
    (mixed : ∀ player (site : (N).InformationSite player) choice,
      choice ∈ (second player site.1).support)
    (final : (phaseApplication runtime leaks).Control) (finalTrace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅) (player : Player) :
    (N).counterfactualReachProbability first player finalTrace =
      (N).counterfactualReachProbability second player finalTrace := by
  have ownEq : (N).playerReachProbability first player finalTrace =
      (N).playerReachProbability second player finalTrace := by
    rw [(N).playerReachProbability_eq_ownPlayReachProbability,
      (N).playerReachProbability_eq_ownPlayReachProbability]
    exact (N).ownPlayReachProbability_congr _
      (phase_clear_ownPlay_policy_eq setup mode runtime leaks bounds plan horizon scheduler first
        second agree final finalTrace clear player)
  have full := congrArg ENNReal.toReal (phase_clear_historyReach_eq setup mode runtime leaks bounds
    plan horizon scheduler first second agree final finalTrace clear)
  rw [(N).historyReachProbability_eq_player_mul_counterfactual first player finalTrace,
    (N).historyReachProbability_eq_player_mul_counterfactual second player finalTrace,
    ownEq] at full
  exact mul_left_cancel₀ ((N).playerReachProbability_pos second mixed player finalTrace).ne' full

/-- Each selected raw-send component transfers exactly to the actual common
profile, since both side products and the real counterfactual factor are local. -/
theorem phase_clear_raw_positionWeight_eq
    (first second : ∀ player, (N).BehavioralPolicy player)
    (agree : ∀ player (site : (N).InformationSite player),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 →
        first player site.1 = second player site.1)
    (mixed : ∀ player (site : (N).InformationSite player) choice,
      choice ∈ (second player site.1).support)
    (final : (phaseApplication runtime leaks).Control) (finalTrace : (E).Trace (some final))
    (clear : final.execution.application.current.excluded = ∅)
    (noise : ℝ) (player : Player) (index : Nat) :
    phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
        player first ⟨some final, finalTrace⟩ index =
      phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
        player second ⟨some final, finalTrace⟩ index := by
  have past := phase_clear_ownPlay_policy_eq setup mode runtime leaks bounds plan horizon scheduler
    first second agree final finalTrace clear player
  have beforeEq : (N).ownPlayReachProbability (first player)
      (((N).ownPlay player finalTrace).take index) =
      (N).ownPlayReachProbability (second player) (((N).ownPlay player finalTrace).take index) := by
    apply (N).ownPlayReachProbability_congr
    intro record member
    exact past record (List.mem_of_mem_take member)
  have afterEq : (N).ownPlayReachProbability (first player)
      (((N).ownPlay player finalTrace).drop index).tail =
      (N).ownPlayReachProbability (second player)
        (((N).ownPlay player finalTrace).drop index).tail := by
    apply (N).ownPlayReachProbability_congr
    intro record member
    exact past record (List.mem_of_mem_drop (List.mem_of_mem_tail member))
  have otherEq := phase_clear_counterfactualReach_eq setup mode runtime leaks bounds plan horizon
    scheduler first second agree mixed final finalTrace clear player
  unfold phaseRawBindingPositionWeight
  split_ifs
  · dsimp only [phaseMarkedHistoryWeight, phaseRawMixtureOwnPlayWeight]
    rw [beforeEq, afterEq, otherEq]
  · rfl

end Vegas
