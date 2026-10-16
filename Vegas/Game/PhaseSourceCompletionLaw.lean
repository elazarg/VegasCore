/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceDispatchLimit
import Vegas.Game.PhaseCompiledBehavioralLaw
import Vegas.Game.PhasePublicCompletion

/-! # Original execution laws at the same completed source assessment limit -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability Filter

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

include sourceConvergence maximal

private theorem common_strategy_at_clear_callback
    (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
    (recipe : ∀ n who (site : (N).InformationSite who),
      (∃ (current : (app).Control) (_trace : (E).Trace (some current)),
        current.actor = some who ∧
        site.1 = some (current.execution.recall who, current.execution.observe app who) ∧
        ∀ owner, (players owner).Consistent (current.execution.recall owner)) →
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
        (sequence n).strategy who site.1 =
          phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon scheduler
            wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
              (slotWeight n) (slotNonnegative n) (slotBounded n) who site.1)
    (current : (app).Control)
    (trace : (E).Trace (some current)) (who : Player) (acting : current.actor = some who)
    (clear : current.execution.application.current.excluded = ∅)
    (faithful : ∀ owner, (players owner).Consistent (current.execution.recall owner)) :
    let input := some (current.execution.recall who, current.execution.observe app who)
    limit.strategy who input = canonical who input := by
  intro input
  apply phaseSourceAssessment_strategy_of_clear_history setup mode runtime leaks bounds wellFormed
    plan horizon scheduler sourceSequence sourceLimit sourceConvergence maximal current trace who
      acting clear noise nonnegative bounded vanishes slotWeight slotNonnegative slotBounded
        slotVanishes sequence limit index increasing converges
  intro n
  obtain ⟨site, observed⟩ := (N).exists_informationSite_of_active who ⟨some current, trace⟩ (by
    change ¬ (current.remaining = 0 ∧ current.actor = none)
    simp only [acting, Option.some_ne_none, and_false, not_false_eq_true]) acting
  have atSite : site.1 = input := observed.trans (by
    change ((menu).signals (start) horizon scheduler).infoOf who trace = input
    rw [ReactiveApplication.ResponseMenu.info]
    change (if current.actor = some who then input else none) = input
    rw [ite_eq_left acting])
  have unflagged : ¬ PhasePublicExclusion setup mode runtime leaks site.1 := by
    rw [atSite]
    rintro ⟨past, view, same, excluded⟩
    have flags := congrArg (fun pair : List (app).PlayerEntry × (app).PlayerView =>
      pair.2.application.2.excluded) (Option.some.inj same)
    change current.execution.application.current.excluded = view.application.2.excluded at flags
    exact excluded (flags.symm.trans clear)
  have pinned := recipe n who site ⟨current, trace, acting, atSite, faithful⟩ unflagged
  rw [atSite] at pinned
  exact pinned

/-- The common completed assessment has the entire original canonical history
law at every finite fuel. Equality is proved only along actual supported
canonical play; the assessment can complete every other input freely. -/
theorem phaseSourceAssessment_run_eq_canonical
    (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
    (recipe : ∀ n who (site : (N).InformationSite who),
      (∃ (current : (app).Control) (_trace : (E).Trace (some current)),
        current.actor = some who ∧
        site.1 = some (current.execution.recall who, current.execution.observe app who) ∧
        ∀ owner, (players owner).Consistent (current.execution.recall owner)) →
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
        (sequence n).strategy who site.1 =
          phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon scheduler
            wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
              (slotWeight n) (slotNonnegative n) (slotBounded n) who site.1)
    (safe : ∀ (current : (app).Control) (_trace : (E).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (fuel : Nat) :
    (N).runBehavioralFrom limit.strategy fuel (E).initHistory =
      (N).runBehavioralFrom canonical fuel (E).initHistory := by
  symm
  apply (N).runBehavioralFrom_congr_on_support
  intro elapsed _historyBound history supported _running who
  by_cases active : (E).active history.state who
  · have currentExists : ∃ current : (app).Control, history.state = some current := by
      cases stateEq : history.state with
      | none =>
          change (app).actor history.state = some who at active
          rw [stateEq] at active
          cases active
      | some current => exact ⟨current, rfl⟩
    obtain ⟨current, atCurrent⟩ := currentExists
    have acting : current.actor = some who := by
      change (app).actor history.state = some who at active
      simpa only [atCurrent, ReactiveApplication.actor, Option.bind_some] using active
    have covered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed
      sourceLimit
    have evaluated := (menu).run_restrict_control_steps (start) horizon scheduler players
      ((menu).admissible_of_covered (start) horizon scheduler players covered) elapsed
        (E).initHistory
    change ((N).runBehavioralFrom canonical elapsed (E).initHistory).map History.state =
      (fun law => law.bind ((app).controlStep (start) horizon scheduler players))^[elapsed]
        (PMF.pure none) at evaluated
    have stateSupported : history.state ∈ ((fun law => law.bind
        ((app).controlStep (start) horizon scheduler players))^[elapsed]
          (PMF.pure none)).support := by
      rw [← evaluated]
      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨history, supported, rfl⟩
    have physicalSupported : history.state ∈ ((fun law => law.bind
        ((app).controlStep
          ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
            scheduler players))^[elapsed] (PMF.pure none)).support := by
      simpa only [PMF.map_comp, Function.comp_def] using stateSupported
    obtain ⟨_physicalTrace, faithful⟩ := PhaseNativeProjection.supported_control_play runtime
      leaks plan bounds (setup.initialLaw.map encodeInputs) horizon scheduler players covered
        elapsed history.state physicalSupported
    have trace : (E).Trace (some current) := atCurrent ▸ history.trace
    have clear := safe current trace (faithful current atCurrent)
    have same := common_strategy_at_clear_callback setup mode runtime leaks bounds wellFormed
      plan maximal horizon scheduler sourceSequence sourceLimit sourceConvergence noise
        nonnegative bounded vanishes slotWeight slotNonnegative slotBounded slotVanishes
          sequence limit index increasing converges recipe current trace who acting clear
            (faithful current atCurrent)
    have observed : (N).infoOf who history.trace =
        some (current.execution.recall who, current.execution.observe app who) := by
      change ((menu).signals (start) horizon scheduler).infoOf who history.trace = _
      rw [ReactiveApplication.ResponseMenu.info]
      change (app).observe who history.state = _
      rw [atCurrent]
      simp only [ReactiveApplication.observe, acting, ↓reduceIte]
    rw [observed]
    exact same.symm
  · exact (N).behavioral_eq_of_not_active (canonical who) (limit.strategy who) history.trace active

/-- Completing inputs outside canonical supported play preserves the full terminal
history law, retaining the original initial draw and all runtime observations. -/
theorem phaseSourceAssessment_terminal_run_eq_canonical
    (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
    (recipe : ∀ n who (site : (N).InformationSite who),
      (∃ (current : (app).Control) (_trace : (E).Trace (some current)),
        current.actor = some who ∧
        site.1 = some (current.execution.recall who, current.execution.observe app who) ∧
        ∀ owner, (players owner).Consistent (current.execution.recall owner)) →
      ¬ PhasePublicExclusion setup mode runtime leaks site.1 →
        (sequence n).strategy who site.1 =
          phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon scheduler
            wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
              (slotWeight n) (slotNonnegative n) (slotBounded n) who site.1)
    (safe : ∀ (current : (app).Control) (_trace : (E).Trace (some current)),
      (∀ who, (players who).Consistent (current.execution.recall who)) →
        current.execution.application.current.excluded = ∅)
    (certificate : (E).WellFoundedHistories) :
    (N).runBehavioralTerminalFrom certificate limit.strategy (E).initHistory =
      (N).runBehavioralTerminalFrom certificate canonical (E).initHistory := by
  rw [(N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
    ((menu).bounded (start) horizon scheduler),
    (N).runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate
      ((menu).bounded (start) horizon scheduler)]
  exact phaseSourceAssessment_run_eq_canonical setup mode runtime leaks bounds wellFormed plan
    maximal horizon scheduler sourceSequence sourceLimit sourceConvergence noise nonnegative
      bounded vanishes slotWeight slotNonnegative slotBounded slotVanishes sequence limit index
        increasing converges recipe safe _

end Vegas
