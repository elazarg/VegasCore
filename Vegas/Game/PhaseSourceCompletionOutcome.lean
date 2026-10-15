/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceCompletionLaw
import Vegas.Game.PhaseAssessmentCompletion

/-! # Consistent physical completion with the original canonical history law -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (sourceConvergence : BehavioralAssessmentConvergesPointwise sourceSequence sourceLimit)

local notation "app" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler
local notation "canonical" => phaseSourceStrategy setup mode runtime leaks bounds wellFormed
  sourceLimit (start) horizon scheduler
local notation "players" => phaseSourcePolicy setup mode runtime leaks bounds wellFormed sourceLimit

include maximal sourceConvergence

open Classical in
/-- One actual completion supplies a common fully mixed Bayes sequence, its
consistent limit, rational whole continuations after exclusion, and the entire
original canonical terminal history law. Clear-site rationality remains separate. -/
theorem exists_phase_source_completion_with_history_law
    [Finite (E).History]
    (noise : ℕ → ℝ) (positive : ∀ n, 0 < noise n) (small : ∀ n, noise n < 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (safe : ∀ (current : (app).Control) (_trace : (E).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (excludedPayoff : Player → ℝ) :
    let certificate := ((menu).bounded (start) horizon scheduler).wellFoundedHistories
    let payoff := fun who (final : (E).History) =>
      phaseExclusionBase setup mode runtime leaks utility excludedPayoff final.state who
    ∃ (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
      (index : ℕ → ℕ),
      (∀ n who (site : (N).InformationSite who),
        ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
          (sequence n).strategy who site.1 =
            phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon scheduler
              wellFormed (sourceSequence n) (noise n) (positive n).le (small n).le
                (slotWeight n) (slotNonnegative n) (slotBounded n) who site.1) ∧
      (∀ n, (sequence n).IsFullyMixed) ∧
      (∀ n, BehavioralAssessment.IsBayesConsistent (N) (sequence n)
        ((menu).decisionRecall (start) horizon scheduler).decisionInformationAntichain) ∧
      StrictMono index ∧
      BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit ∧
      limit.IsSequentiallyConsistent
        ((menu).decisionRecall (start) horizon scheduler).decisionInformationAntichain ∧
      (∀ who (site : (N).InformationSite who),
        PhasePublicExclusion setup mode runtime leaks site.1 →
          ∀ alternative : (N).BehavioralPolicy who,
            (limit.continuationContext certificate site (payoff who)).value alternative ≤
              (limit.continuationContext certificate site (payoff who)).value
                (limit.strategy who)) ∧
      (N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory =
        (N).runBehavioralTerminalFrom certificate canonical (E).initHistory := by
  intro certificate payoff
  let _ := Fintype.ofFinite (E).History
  obtain ⟨_residual, sequence, limit, index, _assembled, recipe, mixed, bayes, increasing,
      converges, consistent, optimal⟩ :=
    exists_phase_source_assessment_completion setup mode runtime leaks bounds (start) horizon
      scheduler wellFormed sourceSequence noise positive small vanishes slotWeight slotNonnegative
        slotBounded utility excludedPayoff
  refine ⟨sequence, limit, index, recipe, mixed, bayes, increasing, converges, consistent,
    optimal, ?_⟩
  exact phaseSourceAssessment_terminal_run_eq_canonical setup mode runtime leaks bounds wellFormed
    plan maximal horizon scheduler sourceSequence sourceLimit sourceConvergence noise
      (fun n => (positive n).le) (fun n => (small n).le) vanishes slotWeight slotNonnegative
        slotBounded slotVanishes sequence limit index increasing converges recipe safe certificate

end Vegas
