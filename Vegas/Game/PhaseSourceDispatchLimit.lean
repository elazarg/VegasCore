/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceStrategyLimit
import Vegas.Pending.PhaseBindingIdleMenu

/-! # Complete canonical strategies at actual clear assessment-limit callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler

private theorem sourceStrategy_eq_of_no_request (remaining : Nat) (who : Player)
    (execution : (app).Execution)
    (trace : ((menu).protocol (start) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (absent : ∀ coordinate, ¬ execution.application.SeedRequest who coordinate)
    (first second : setup.commitRecoveryModel.BehavioralAssessment) :
    let input := some (execution.recall who, execution.observe app who)
    phaseSourceStrategy setup mode runtime leaks bounds wellFormed first (start) horizon scheduler
        who input =
      phaseSourceStrategy setup mode runtime leaks bounds wellFormed second (start) horizon
        scheduler who input := by
  intro input
  have physical : ((menu).protocol
      ((setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩) := by
    rw [PMF.map_comp]
    exact trace
  have singleton := PhaseCount.onePacketActions_eq_singleton_of_no_request runtime leaks bounds
    plan (setup.initialLaw.map encodeInputs) horizon scheduler remaining who execution physical
      absent
  have silent (assessment : setup.commitRecoveryModel.BehavioralAssessment) :
      phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (execution.recall who) (execution.observe app who) = PMF.pure ⟨none⟩ := by
    apply pmf_eq_pure_of_support_subset_singleton
    intro action supported
    have offered := phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed
      assessment who _ _ action supported
    rw [singleton] at offered
    exact Finset.mem_singleton.mp offered
  apply pmf_map_injective Subtype.val_injective
  rw [phaseSourceStrategy_map_val, phaseSourceStrategy_map_val, silent first, silent second]

variable (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (sourceConvergence : BehavioralAssessmentConvergesPointwise sourceSequence sourceLimit)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include sourceConvergence maximal

/-- Every actual clear actor callback has a convergent entire canonical
finite-menu law, including callbacks with no current request. -/
theorem phaseSourceStrategy_converges_of_clear_history
    (control : (app).Control)
    (trace : ((menu).protocol (start) horizon scheduler).Trace (some control))
    (who : Player) (acting : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    PMFConvergesPointwise
      (fun n => phaseSourceStrategy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        (start) horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input) := by
  intro input
  classical
  by_cases requested : ∃ coordinate, control.execution.application.SeedRequest who coordinate
  · obtain ⟨⟨attempt, event⟩, request⟩ := requested
    have same : attempt = control.execution.application.attempt := request.1
    subst attempt
    have raw := (menu).toRawTrace (start) horizon scheduler trace
    cases node : nodeView (serviceGraph setup mode) event with
    | bind owner payload outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        exact phaseSourceStrategy_binding_converges_of_history setup mode runtime leaks bounds
          wellFormed sourceSequence sourceLimit sourceConvergence plan maximal horizon scheduler
            control raw who event payload outputEq request clear
    | resolve owner payload binding checks outputEq codeEq =>
        have ownerEq : owner = who := Option.some.inj
          (((EventCode.actor_cast outputEq _).symm.trans
            (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
        subst owner
        have same (n : Nat) := phaseSourceStrategy_opening_independent_of_history setup mode
          runtime leaks bounds wellFormed plan horizon scheduler control raw who event payload
            binding checks outputEq codeEq request (sourceSequence n) sourceLimit
        simpa only [input, same] using pmfConvergesPointwise_const
          (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
            (start) horizon scheduler who input)
    | sample payload law outputEq codeEq =>
        have noOwner : (serviceGraph setup mode).actor? event = none :=
          (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
        have owned := request.2.2.2.1
        rw [noOwner] at owned
        cases owned
  · rcases control with ⟨remaining, actor, execution⟩
    cases acting
    have same (n : Nat) := sourceStrategy_eq_of_no_request setup mode runtime leaks bounds
      wellFormed plan horizon scheduler remaining who execution trace
        (fun coordinate present => requested ⟨coordinate, present⟩) (sourceSequence n) sourceLimit
    simpa only [input, same] using pmfConvergesPointwise_const
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input)

/-- The same common native assessment limit has the complete canonical
strategy at every actual clear callback, irrespective of its dispatcher branch. -/
theorem phaseSourceAssessment_strategy_of_clear_history
    (control : (app).Control)
    (trace : ((menu).protocol (start) horizon scheduler).Trace (some control))
    (who : Player) (acting : control.actor = some who)
    (clear : control.execution.application.current.excluded = ∅)
    (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0))
    (sequence : ℕ → (N).BehavioralAssessment) (limit : (N).BehavioralAssessment)
    (index : ℕ → ℕ) (increasing : StrictMono index)
    (converges : BehavioralAssessmentConvergesPointwise (fun n => sequence (index n)) limit)
    (recipe : ∀ n, (sequence n).strategy who
      (some (control.execution.recall who, control.execution.observe app who)) =
        phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon scheduler
          wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
            (slotWeight n) (slotNonnegative n) (slotBounded n) who
              (some (control.execution.recall who, control.execution.observe app who))) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    limit.strategy who input = phaseSourceStrategy setup mode runtime leaks bounds wellFormed
      sourceLimit (start) horizon scheduler who input := by
  intro input
  have canonical := phaseSourceStrategy_converges_of_clear_history setup mode runtime leaks
    bounds wellFormed plan horizon scheduler sourceSequence sourceLimit sourceConvergence maximal
      control trace who acting clear
  have perturbed := phaseSourcePerturbedStrategy_converges setup mode runtime leaks bounds
    wellFormed sourceSequence sourceLimit plan horizon scheduler who input canonical noise
      nonnegative bounded vanishes slotWeight slotNonnegative slotBounded slotVanishes
  obtain ⟨site, atSite⟩ := (N).exists_informationSite_of_active who ⟨some control, trace⟩ (by
    change ¬ (control.remaining = 0 ∧ control.actor = none)
    simp only [acting, Option.some_ne_none, and_false, not_false_eq_true]) acting
  have siteEq : site.1 = input := atSite.trans (by
    change ((menu).signals (start) horizon scheduler).infoOf who trace = input
    rw [ReactiveApplication.ResponseMenu.info]
    change (if control.actor = some who then input else none) = input
    rw [ite_eq_left acting])
  have native := converges.strategy who site
  rw [siteEq] at native
  have transported : PMFConvergesPointwise
      (fun n => (sequence (index n)).strategy who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input) := by
    simpa only [input, recipe] using perturbed.subseq increasing
  exact native.unique transported

end Vegas
