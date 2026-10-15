/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryContinuingProbability
import Vegas.Game.PhaseSourceResponseLaw
import Vegas.Game.PhaseBindingCounterpart

/-! # Uniform silence bounds at actual clear native binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (wellFormed : setup.WellFormed)
  (reference target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    reference target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
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

local notation "app" => phaseApplication runtime leaks
local notation "start" => setup.initialLaw.map fun draw =>
  PhaseRuntimeState.initial plan (encodeInputs draw)
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) (start) horizon scheduler

include maximal capacity binding trace acting request unsent values clear

/-- Every actual clear unsent binding callback has this uniform silence bound.
The source and raw tremble rates remain separate; the fresh-slot weight does
not alter the bound. This is a future response law, not a bound on past omissions
conditioned on a native information set. -/
theorem phaseSourcePerturbedStrategy_silence_probability_of_history
    (n : ℕ) (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    let silent := fun choice : (N).Choice who input =>
      (choice.1.getD ⟨none⟩).transmission.isNone
    (((phaseSourcePerturbedStrategy setup mode runtime leaks bounds (start) horizon scheduler
      wellFormed (approximation.sequence n) noise nonnegative bounded slotWeight
        slotNonnegative slotBounded who input).map silent) true).toReal ≤
          noise + (1 - noise) * approximation.epsilon n := by
  intro input silent
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace (start) horizon scheduler
    trace
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler raw who event payload binding request.2.2.1 clear wellFormed
  let inputs := setup.initialLaw.map encodeInputs
  have physical : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have exactLaw := phaseSourcePerturbedStrategy_result_law_of_history setup mode runtime
    leaks bounds wellFormed (approximation.sequence n) who event payload binding
      (PhaseCount.onePacketMenu runtime leaks bounds) plan inputs horizon scheduler capacity control
        physical acting request unsent values (start) noise nonnegative bounded
          slotWeight slotNonnegative slotBounded
  have responseSnd (response : (app).Action) :
      (phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        response).2 = response.transmission.isNone := by
    cases missing : response.transmission.isNone <;>
      simp only [phaseBindingResponseOutcome, missing, Bool.false_eq_true, ↓reduceIte]
  have sourceSnd (choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe app who)))) :
      (phaseRecoveryBindingData setup mode event who payload binding choice.1).2 =
        choice.1.elim false (·.missing) := by
    unfold phaseRecoveryBindingData
    split
    · next missing => exact missing.symm
    · next notMissing => exact (Bool.eq_false_iff.mpr notMissing).symm
  have silenceLaw := congrArg (fun law => law.map Prod.snd) exactLaw
  simp only [mix_map, PMF.map_comp, Function.comp_def, responseSnd, sourceSnd] at silenceLaw
  change (PMF.map silent _ true).toReal ≤ _
  rw [silenceLaw, mix_apply_toReal]
  have sourceBound := setup.commitRecovery_approximation_missing_probability wellFormed
    reference target approximation n who ⟨_, played⟩
  exact add_le_add
    ((mul_le_mul_of_nonneg_left (pmf_toReal_apply_le_one _ _) nonnegative).trans_eq
      (mul_one noise))
    (mul_le_mul_of_nonneg_left sourceBound (sub_nonneg.mpr bounded))

end Vegas
