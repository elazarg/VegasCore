/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceResponseLimit

/-! # Full physical source strategies at a common native assessment limit -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (wellFormed : setup.WellFormed)
  (sourceSequence : ℕ → setup.commitRecoveryModel.BehavioralAssessment)
  (sourceLimit : setup.commitRecoveryModel.BehavioralAssessment)
  (sourceConvergence : BehavioralAssessmentConvergesPointwise sourceSequence sourceLimit)

include sourceConvergence

private theorem bindingPolicy_converges (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (played : setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event view))) :
    PMFConvergesPointwise
      (fun n => phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed
        (sourceSequence n) who event payload binding past view)
      (phaseRecoveryBindingPolicy setup mode runtime leaks bounds wellFormed sourceLimit
        who event payload binding past view) := by
  classical
  cases fresh : reactiveFreshSlot view.application.1 with
  | none =>
      simp only [phaseRecoveryBindingPolicy, fresh]
      exact pmfConvergesPointwise_const _
  | some serial =>
      by_cases covered : ∀ move, phaseRecoveryBindingResponse setup mode runtime leaks who event
          payload binding serial move ∈ PhaseCount.onePacketActions runtime leaks bounds who
            past view
      · simp only [phaseRecoveryBindingPolicy, fresh, ite_eq_left covered]
        exact (sourceConvergence.strategy who ⟨_, played⟩).map
          (fun choice => phaseRecoveryBindingResponse setup mode runtime leaks who event payload
            binding serial choice.1)
      · simp only [phaseRecoveryBindingPolicy, fresh, ite_eq_right covered]
        exact pmfConvergesPointwise_const _

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler

include maximal in
/-- At every actual clear ready binding, the complete physical response law
converges, including its exact fresh handle and preparation. No intended-view
witness, capacity or unsent premise is needed for this statement. -/
theorem phaseSourcePolicy_binding_converges_of_history
    (control : (app).Control) (trace : ((app).protocol (start) horizon scheduler).Trace
      (some control)) (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (clear : control.execution.application.current.excluded = ∅) :
    PMFConvergesPointwise
      (fun n => phaseSourcePolicy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        who (control.execution.recall who) (control.execution.observe app who))
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed sourceLimit who
        (control.execution.recall who) (control.execution.observe app who)) := by
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler trace who event payload binding request.2.2.1 clear wellFormed
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physical : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    physical
  have branch (assessment : setup.commitRecoveryModel.BehavioralAssessment) :=
    phaseSourcePolicy_binding setup mode runtime leaks bounds wellFormed assessment
      control.execution valid who event payload binding request
  simp only [branch]
  exact bindingPolicy_converges setup mode runtime leaks bounds wellFormed sourceSequence
    sourceLimit sourceConvergence who event payload binding _ _ played

include maximal in
/-- The same convergence retains the entire authentic finite-menu choice. -/
theorem phaseSourceStrategy_binding_converges_of_history
    (control : (app).Control) (trace : ((app).protocol (start) horizon scheduler).Trace
      (some control)) (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (clear : control.execution.application.current.excluded = ∅) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    PMFConvergesPointwise
      (fun n => phaseSourceStrategy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        (start) horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input) := by
  intro input
  have physical := (phaseSourcePolicy_binding_converges_of_history setup mode runtime leaks
    bounds wellFormed sourceSequence sourceLimit sourceConvergence plan maximal horizon scheduler
      control trace who event payload binding request clear).map some
  have mapped : PMFConvergesPointwise
      (fun n => (phaseSourceStrategy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        (start) horizon scheduler who input).map Subtype.val)
      ((phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input).map Subtype.val) := by
    simpa only [input, phaseSourceStrategy_map_val] using physical
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro choice
  simpa only [pmf_map_apply_of_injective _ Subtype.val_injective] using mapped.toReal choice.1

omit sourceConvergence in
/-- Vanishing raw and slot weights preserve convergence of the entire canonical
finite choice law. The intermediate slot laws may vary arbitrarily. -/
theorem phaseSourcePerturbedStrategy_converges
    (who : Player) (input : (app).Info)
    (canonical : PMFConvergesPointwise
      (fun n => phaseSourceStrategy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        (start) horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input))
    (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
    (vanishes : Tendsto noise atTop (nhds 0))
    (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
    (slotBounded : ∀ n, slotWeight n ≤ 1)
    (slotVanishes : Tendsto slotWeight atTop (nhds 0)) :
    PMFConvergesPointwise
      (fun n => phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon
        scheduler wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
          (slotWeight n) (slotNonnegative n) (slotBounded n) who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input) := by
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro choice
  have rawTerm := vanishes.mul_const
    (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy (start) horizon scheduler
      who input) choice).toReal
  have slotTerm : Tendsto (fun n => slotWeight n *
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        (start) horizon scheduler who input) choice).toReal) atTop (nhds 0) := by
    apply squeeze_zero
      (fun n => mul_nonneg (slotNonnegative n) ENNReal.toReal_nonneg)
      (fun n => (mul_le_mul_of_nonneg_left (pmf_toReal_apply_le_one _ _)
        (slotNonnegative n)).trans_eq (mul_one _)) slotVanishes
  have mainTerm := ((tendsto_const_nhds (x := (1 : ℝ))).sub slotVanishes).mul
    (canonical.toReal choice)
  have total := rawTerm.add (((tendsto_const_nhds (x := (1 : ℝ))).sub vanishes).mul
    (slotTerm.add mainTerm))
  simpa only [zero_mul, sub_zero, one_mul, zero_add, phaseSourcePerturbedStrategy,
    mix_apply_toReal] using total

include maximal in
/-- The common consistent native limit plays the exact canonical physical
strategy at every actual clear binding, when both native noise tiers vanish.
This retains the full response rather than only its declared source outcome. -/
theorem phaseSourceAssessment_binding_strategy_of_history
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol (start) horizon
      scheduler).Trace (some control)) (who : Player) (acting : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
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
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace (start) horizon scheduler
    trace
  have canonical := phaseSourceStrategy_binding_converges_of_history setup mode runtime leaks
    bounds wellFormed sourceSequence sourceLimit sourceConvergence plan maximal horizon scheduler
      control raw who event payload binding request clear
  have perturbed := phaseSourcePerturbedStrategy_converges setup mode runtime leaks bounds
    wellFormed sourceSequence sourceLimit plan horizon scheduler who input canonical noise
      nonnegative bounded vanishes slotWeight slotNonnegative slotBounded slotVanishes
  obtain ⟨site, atSite⟩ := (N).exists_informationSite_of_active who
    ⟨some control, trace⟩ (by
      change ¬ (control.remaining = 0 ∧ control.actor = none)
      simp only [acting, Option.some_ne_none, and_false, not_false_eq_true]) (by
      change control.actor = some who
      exact acting)
  have siteEq : site.1 = input := atSite.trans (by
    change ((PhaseCount.onePacketMenu runtime leaks bounds).signals (start) horizon
      scheduler).infoOf who trace = input
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

omit sourceConvergence in
/-- Actual opening responses are identical for every auxiliary assessment.
The dispatcher reads the authentic native binding and always attempts TRUE. -/
theorem phaseSourceStrategy_opening_independent_of_history
    (control : (app).Control) (trace : ((app).protocol (start) horizon scheduler).Trace
      (some control)) (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (first second : setup.commitRecoveryModel.BehavioralAssessment) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    phaseSourceStrategy setup mode runtime leaks bounds wellFormed first (start) horizon
        scheduler who input =
      phaseSourceStrategy setup mode runtime leaks bounds wellFormed second (start) horizon
        scheduler who input := by
  intro input
  let inputs : PMF (serviceGraph setup mode).Inputs := setup.initialLaw.map encodeInputs
  have physical : ((app).protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
      scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  obtain ⟨draw, valid⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
    physical
  apply pmf_map_injective Subtype.val_injective
  rw [phaseSourceStrategy_map_val, phaseSourceStrategy_map_val]
  rw [phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed first control.execution
    valid who event payload binding checks outputEq codeEq request,
    phaseSourcePolicy_opening setup mode runtime leaks bounds wellFormed second control.execution
      valid who event payload binding checks outputEq codeEq request]

omit sourceConvergence in
/-- With both native noise tiers vanishing, the same common assessment limit
retains the canonical full physical opening strategy, at every genuine opening
input. No source-belief or successful-binding premise is needed. -/
theorem phaseSourceAssessment_opening_strategy_of_history
    (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol (start) horizon
      scheduler).Trace (some control)) (who : Player) (acting : control.actor = some who)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
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
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace (start) horizon scheduler
    trace
  have same (n : ℕ) := phaseSourceStrategy_opening_independent_of_history setup mode runtime leaks
    bounds wellFormed plan horizon scheduler control raw who event payload binding checks outputEq
      codeEq request (sourceSequence n) sourceLimit
  have canonical : PMFConvergesPointwise
      (fun n => phaseSourceStrategy setup mode runtime leaks bounds wellFormed (sourceSequence n)
        (start) horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input) := by
    simpa only [input, same] using pmfConvergesPointwise_const
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed sourceLimit
        (start) horizon scheduler who input)
  have perturbed := phaseSourcePerturbedStrategy_converges setup mode runtime leaks bounds
    wellFormed sourceSequence sourceLimit plan horizon scheduler who input canonical noise
      nonnegative bounded vanishes slotWeight slotNonnegative slotBounded slotVanishes
  obtain ⟨site, atSite⟩ := (N).exists_informationSite_of_active who
    ⟨some control, trace⟩ (by
      change ¬ (control.remaining = 0 ∧ control.actor = none)
      simp only [acting, Option.some_ne_none, and_false, not_false_eq_true]) (by
      change control.actor = some who
      exact acting)
  have siteEq : site.1 = input := atSite.trans (by
    change ((PhaseCount.onePacketMenu runtime leaks bounds).signals (start) horizon
      scheduler).infoOf who trace = input
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
