/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseClearProfileLocality
import Vegas.Game.PhaseOpponentRawBindingLimit

/-! # Opponent raw-send elimination for the actual clear-pinned common profiles -/

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

variable [nature : (phaseApplication runtime leaks).FiniteNature
  (setup.initialLaw.map (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))) scheduler]

/-- The whole actual information fiber has identical reach and selected raw
components under the common completion and its clear recipe. Profiles may
differ arbitrarily after a public exclusion. -/
theorem phase_clear_fiber_raw_share_eq
    (first second : ∀ player, (N).BehavioralPolicy player)
    (agree : ∀ player (site : (N).InformationSite player),
      ¬PhasePublicExclusion setup mode runtime leaks site.1 →
        first player site.1 = second player site.1)
    (mixed : ∀ player (site : (N).InformationSite player) choice,
      choice ∈ (second player site.1).support)
    (noise : ℝ) (focal : Player) (site : (N).InformationSite focal)
    (original : (phaseApplication runtime leaks).Control)
    (originalTrace : (E).Trace (some original))
    (atSite : (N).infoOf focal originalTrace = site.1) (active : original.actor = some focal)
    (event : (serviceGraph setup mode).EventId)
    (clear : original.execution.application.current.excluded = ∅)
    (request : original.execution.application.SeedRequest focal
      ⟨original.execution.application.attempt, event⟩) :
    (N).informationMass first focal site = (N).informationMass second focal site ∧
      phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler noise
        focal
          first site =
        phaseOpponentRawBindingShare setup mode runtime leaks bounds plan horizon scheduler noise
          focal second site := by
  have genuine := phase_binding_fiber_genuine setup mode runtime leaks bounds plan horizon scheduler
    focal site original originalTrace atSite active event clear request
  have each (history : (N).InformationHistory focal site.1) :
      (N).historyReachWeight first history.1 = (N).historyReachWeight second history.1 ∧
      ∀ owner index, phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon
          scheduler noise owner first history.1 index =
        phaseRawBindingPositionWeight setup mode runtime leaks bounds plan horizon scheduler noise
          owner second history.1 index := by
    obtain ⟨control, atControl, _acting, controlClear, _request⟩ := genuine history
    rcases history with ⟨⟨state, trace⟩, _info⟩
    change state = some control at atControl
    cases atControl
    exact ⟨phase_clear_historyReach_eq setup mode runtime leaks bounds initial horizon scheduler
      first second agree control trace controlClear, fun owner index =>
        phase_clear_raw_positionWeight_eq setup mode runtime leaks bounds plan horizon scheduler
          first
          second agree mixed control trace controlClear noise owner index⟩
  have massEq : (N).informationMass first focal site = (N).informationMass second focal site := by
    unfold InformationModel.informationMass
    apply tsum_congr
    intro history
    exact (each history).1
  refine ⟨massEq, ?_⟩
  unfold phaseOpponentRawBindingShare
  rw [massEq]
  congr 1
  unfold phaseOpponentRawBindingMass
  apply Finset.sum_congr rfl
  intro owner _member
  apply Finset.sum_congr rfl
  intro index _inside
  apply Finset.sum_congr rfl
  intro history _member
  exact (each history).2 owner index

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

variable [setup.FiniteInitialLaw]

include maximal in
/-- The SAME chosen native noise works for every actual common profile
sequence pinned to its clear recipe, as supplied by PhaseAssessmentCompletion.
Actual normalized opponent RAW sends vanish without global profile equality,
source posterior assumptions or a rare-source-failure claim. -/
theorem exists_phase_common_raw_binding_share_vanishes
    (capacity : horizon ≤ bounds.candidateCount) (covered : bounds.CoversOutputValues)
    (slotWeight : ℕ → ℝ) (slotPositive : ∀ n, 0 < slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1) :
    ∃ (noise : ℕ → ℝ) (noisePositive : ∀ n, 0 < noise n)
      (noiseSmall : ∀ n, noise n < 1 / 2),
      Filter.Tendsto noise Filter.atTop (nhds 0) ∧
      ∀ profiles : ℕ → ∀ player, (N).BehavioralPolicy player,
        (∀ n player (site : (N).InformationSite player),
          ¬PhasePublicExclusion setup mode runtime leaks site.1 →
            profiles n player site.1 =
              phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
                wellFormed (approximation.sequence n) (noise n) (noisePositive n).le
                  (by linarith [noiseSmall n]) (slotWeight n) (slotPositive n).le
                    (slotBounded n) player site.1) →
        ∀ (focal : Player) (site : (N).InformationSite focal)
          (original : (phaseApplication runtime leaks).Control)
          (originalTrace : (E).Trace (some original)),
          (N).infoOf focal originalTrace = site.1 → original.actor = some focal →
          ∀ (event : (serviceGraph setup mode).EventId) (payload : L.Ty),
          (serviceGraph setup mode).outputLayout event = .binding focal payload →
          original.execution.application.current.excluded = ∅ →
          original.execution.application.SeedRequest focal
            ⟨original.execution.application.attempt, event⟩ →
          Filter.Tendsto (fun n => phaseOpponentRawBindingShare setup mode runtime leaks bounds plan
            horizon scheduler (noise n) focal (profiles n) site) Filter.atTop (nhds 0) := by
  obtain ⟨_floor, noise, _floorPositive, noisePositive, noiseSmall, _floored, noiseVanishes,
    recipeVanishes⟩ := exists_phase_opponent_raw_binding_share_vanishes setup mode runtime leaks
      bounds
      plan horizon scheduler finite wellFormed target approximation maximal capacity covered
        slotWeight slotPositive slotBounded
  refine ⟨noise, noisePositive, noiseSmall, noiseVanishes, ?_⟩
  intro profiles agree focal site original originalTrace atSite active event payload output clear
    request
  have recipeLimit := recipeVanishes focal site original originalTrace atSite active event payload
    output clear request
  apply Filter.Tendsto.congr _ recipeLimit
  intro n
  symm
  apply (phase_clear_fiber_raw_share_eq setup mode runtime leaks bounds plan horizon scheduler
    (profiles n) _ (agree n) _ (noise n) focal site original originalTrace atSite active event clear
      request).2
  intro player decision choice
  exact phaseSourcePerturbedStrategy_fullSupport setup mode runtime leaks bounds initial horizon
    scheduler wellFormed (approximation.sequence n) (noise n) (noisePositive n)
      (by linarith [noiseSmall n]) (slotWeight n) (slotPositive n).le (slotBounded n)
        player decision.1 choice

end Vegas
