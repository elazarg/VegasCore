/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceResponseLaw
import Vegas.Game.PhaseSourceSlotInformation
import Vegas.Game.PhaseAssessmentCompletion

/-! # Source response laws at a common native assessment limit -/

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
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
  (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
  (control : (phaseApplication runtime leaks).Control)
  (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
  (acting : control.actor = some who)
  (request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, event⟩)
  (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
    PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
  (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (clear : control.execution.application.current.excluded = ∅)
  (noise : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ noise n) (bounded : ∀ n, noise n ≤ 1)
  (vanishes : Tendsto noise atTop (nhds 0))
  (slotWeight : ℕ → ℝ) (slotNonnegative : ∀ n, 0 ≤ slotWeight n)
  (slotBounded : ∀ n, slotWeight n ≤ 1)

local notation "app" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler

include sourceConvergence maximal capacity trace acting request unsent values clear vanishes

/-- At every actual clear binding site, the joint declared-result/omission law
converges to its original auxiliary source law. Slot weights need not vanish:
both source tiers have the same semantic law before physical inclusion. -/
theorem phaseSourcePerturbedStrategy_result_converges_of_history :
    let input := some (control.execution.recall who, control.execution.observe app who)
    let outcome := fun choice : (N).Choice who input =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (choice.1.getD ⟨none⟩)
    PMFConvergesPointwise
      (fun n => (phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon
        scheduler wellFormed (sourceSequence n) (noise n) (nonnegative n) (bounded n)
          (slotWeight n) (slotNonnegative n) (slotBounded n) who input).map outcome)
      ((sourceLimit.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe app who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) := by
  intro input outcome
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace (start) horizon scheduler
    trace
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler raw who event payload binding request.2.2.1 clear wellFormed
  have source := (sourceConvergence.strategy who ⟨_, played⟩).map
    (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1)
  let inputs := setup.initialLaw.map encodeInputs
  have physical : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have exactLaw (n : Nat) := phaseSourcePerturbedStrategy_result_law_of_history setup mode runtime
    leaks bounds wellFormed (sourceSequence n) who event payload binding
      (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity control
        physical acting request unsent values (start) (noise n) (nonnegative n) (bounded n)
          (slotWeight n) (slotNonnegative n) (slotBounded n)
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro result
  have first := vanishes.mul_const
    ((((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy (start) horizon scheduler
      who input).map outcome) result).toReal
  have rest := ((tendsto_const_nhds (x := (1 : ℝ))).sub vanishes).mul (source.toReal result)
  have total := first.add rest
  simp only [zero_mul, sub_zero, one_mul, zero_add] at total
  convert total using 1
  funext n
  rw [exactLaw n, mix_apply_toReal]

/-- Every common native subsequential limit retaining this recipe has the exact
source joint response law at the same actual clear site. This identifies a
local response law, not a conditional native/source history distribution. -/
theorem phaseSourceAssessment_binding_limit_of_history
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
    let outcome := fun choice : (N).Choice who input =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (choice.1.getD ⟨none⟩)
    (limit.strategy who input).map outcome =
      ((sourceLimit.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe app who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) := by
  intro input outcome
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
  have intended := phaseSourcePerturbedStrategy_result_converges_of_history setup mode runtime
    leaks bounds wellFormed sourceSequence sourceLimit sourceConvergence plan maximal horizon
      scheduler capacity who event payload binding control trace acting request unsent values clear
        noise nonnegative bounded vanishes slotWeight slotNonnegative slotBounded
  have transported : PMFConvergesPointwise
      (fun n => ((sequence (index n)).strategy who input).map outcome)
      ((sourceLimit.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe app who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)) := by
    simpa only [input, recipe] using intended.subseq increasing
  exact (native.map outcome).unique transported

end Vegas
