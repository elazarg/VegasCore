/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourcePosition
import Vegas.Game.CommitRecoveryOmissionPosition
import Vegas.Game.PhaseSourceResponseLaw
import Vegas.Game.PhaseBindingCounterpart

/-! # Identical native waiting factors at the same source binding address -/

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

omit [Fintype Player] in
/-- The physical source decoder names the original static source rank. -/
theorem phaseSourceView?_position (execution : (phaseApplication runtime leaks).Execution)
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view) :
    ProtocolView.position who setup.program view = event.val := by
  rw [phaseSourceView?_observed] at decoded
  exact decodeEventView?_position setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event _ _ view decoded

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- At a genuine unsent callback, both source response recipes preserve the
entire source omission law. Sampling a fresh slot cannot create silence. -/
theorem phaseSourceMixture_silence_law_of_history
    (wellFormed : setup.WellFormed) (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (app).Control) (trace : (E).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (acting : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    let silent := fun choice : (N).Choice who input =>
      (choice.1.getD ⟨none⟩).transmission.isNone
    (mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who input)).map silent =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe app who)))).map
            (fun choice => CommitRecoveryMove.missed choice.1) := by
  intro input silent
  let inputs := setup.initialLaw.map encodeInputs
  have physical : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have exactLaw := phaseSourcePerturbedStrategy_result_law_of_history setup mode runtime leaks
    bounds wellFormed assessment who event payload binding (PhaseCount.onePacketMenu runtime
      leaks bounds) plan inputs horizon scheduler capacity control physical acting request unsent
        values initial 0 (by norm_num) (by norm_num) slotWeight slotNonnegative slotBounded
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
        CommitRecoveryMove.missed choice.1 := by
    unfold phaseRecoveryBindingData
    split
    · next missing => exact missing.symm
    · next notMissing => exact (Bool.eq_false_iff.mpr notMissing).symm
  have projected := congrArg (fun law => law.map Prod.snd) exactLaw
  simp only [mix_zero, PMF.map_comp, Function.comp_def, responseSnd, sourceSnd] at projected
  simpa only [phaseSourcePerturbedStrategy, mix_zero] using projected

omit [Fintype Player] in
private theorem raw_silence_atom (law : PMF (app).Action) :
    (law.map (fun response => response.transmission.isNone)) true = law ⟨none⟩ := by
  classical
  have preimage (response : (app).Action) :
      true = response.transmission.isNone ↔ response = ⟨none⟩ := by
    rcases response with ⟨transmission⟩
    cases transmission <;> simp
  simp only [PMF.map_apply, preimage, tsum_ite_eq]

theorem phaseSourceMixture_silence_atom (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment) (who : Player)
    (control : (app).Control)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (choice : (N).Choice who (some (control.execution.recall who,
      control.execution.observe app who))) (selected : choice.1 = some ⟨none⟩) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    let law := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who input)
    law choice = (law.map (fun option => (option.1.getD ⟨none⟩).transmission.isNone)) true := by
  intro input law
  let physical := mix slotWeight slotNonnegative slotBounded
    (phaseSourceSlotPolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who) (control.execution.observe app who))
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who) (control.execution.observe app who))
  have projection : law.map Subtype.val = physical.map some := by
    dsimp only [law, physical]
    rw [mix_map, phaseSourceSlotStrategy_map_val, phaseSourceStrategy_map_val, ← mix_map]
  have boolean : (law.map (fun option => (option.1.getD ⟨none⟩).transmission.isNone)) =
      physical.map (fun response => response.transmission.isNone) := by
    change PMF.map ((fun response : Option (app).Action =>
      (response.getD ⟨none⟩).transmission.isNone) ∘ Subtype.val) law = _
    rw [← PMF.map_comp, projection, PMF.map_comp]
    rfl
  rw [boolean, raw_silence_atom]
  rw [← pmf_map_apply_of_injective law Subtype.val_injective choice]
  rw [projection, selected]
  exact pmf_map_apply_of_injective physical (Option.some_injective _) ⟨none⟩

variable (finite : setup.program.FiniteBindingTypes) (wellFormed : setup.WellFormed)
  (target : setup.commitRecoveryModel.BehavioralAssessment)
  (approximation : (setup.commitRecoveryRestriction wellFormed).RestrictedExtensionApproximation
    (setup.commitRecoveryReference finite) target setup.commitRecoveryModel_decisionAntichain
    setup.commitRecoveryContinuingChoice)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)

include maximal

/-- Two genuine clear unsent binding callbacks naming the same original event
have identical source and slot-mixture silence laws at every approximation.
Their hidden values, full own words and fresh-slot sets may differ. Only the
raw-noise recipe remains outside this exact timing identity. -/
theorem phaseSourceMixture_silence_eq_of_history (n : Nat)
    (capacity : horizon ≤ bounds.candidateCount)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (first second : (app).Control)
    (firstTrace : (E).Trace (some first)) (secondTrace : (E).Trace (some second))
    (firstActor : first.actor = some who) (secondActor : second.actor = some who)
    (firstRequest : first.execution.application.SeedRequest who
      ⟨first.execution.application.attempt, event⟩)
    (secondRequest : second.execution.application.SeedRequest who
      ⟨second.execution.application.attempt, event⟩)
    (firstUnsent : ∀ message ∈ (app).outputs (first.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨first.execution.application.attempt, event⟩)
    (secondUnsent : ∀ message ∈ (app).outputs (second.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨second.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (firstClear : first.execution.application.current.excluded = ∅)
    (secondClear : second.execution.application.current.excluded = ∅) :
    (phaseSourceView? setup mode runtime leaks who event (first.execution.observe app who)).map
        (ProtocolView.position who setup.program) = some event.val ∧
      (phaseSourceView? setup mode runtime leaks who event (second.execution.observe app who)).map
        (ProtocolView.position who setup.program) = some event.val ∧
      ∀ (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1),
        let firstInput := some (first.execution.recall who, first.execution.observe app who)
        let secondInput := some (second.execution.recall who, second.execution.observe app who)
        let firstSilent := fun choice : (N).Choice who firstInput =>
          (choice.1.getD ⟨none⟩).transmission.isNone
        let secondSilent := fun choice : (N).Choice who secondInput =>
          (choice.1.getD ⟨none⟩).transmission.isNone
        let firstLaw := mix slotWeight slotNonnegative slotBounded
          (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed
            (approximation.sequence n) initial horizon scheduler who firstInput)
          (phaseSourceStrategy setup mode runtime leaks bounds wellFormed
            (approximation.sequence n) initial horizon scheduler who firstInput)
        let secondLaw := mix slotWeight slotNonnegative slotBounded
          (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed
            (approximation.sequence n) initial horizon scheduler who secondInput)
          (phaseSourceStrategy setup mode runtime leaks bounds wellFormed
            (approximation.sequence n) initial horizon scheduler who secondInput)
        firstLaw.map firstSilent = secondLaw.map secondSilent ∧
        ∀ (firstChoice : (N).Choice who firstInput) (secondChoice : (N).Choice who secondInput),
          firstChoice.1 = some ⟨none⟩ → secondChoice.1 = some ⟨none⟩ →
            firstLaw firstChoice = secondLaw secondChoice := by
  have firstRaw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler firstTrace
  have secondRaw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial horizon
    scheduler secondTrace
  obtain ⟨firstSource, _firstSourceTrace, _firstExcluded, _firstGeneration, _firstActor,
      firstView⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler firstRaw
      who event payload binding firstRequest.2.2.1 firstClear
  obtain ⟨secondSource, _secondSourceTrace, _secondExcluded, _secondGeneration, _secondActor,
      secondView⟩ := phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon
        scheduler secondRaw who event payload binding secondRequest.2.2.1 secondClear
  have firstPosition := phaseSourceView?_position setup mode runtime leaks first.execution who
    event _ firstView
  have secondPosition := phaseSourceView?_position setup mode runtime leaks second.execution who
    event _ secondView
  have firstPlayed := phase_ready_binding_information setup mode runtime leaks plan maximal
    horizon scheduler firstRaw who event payload binding firstRequest.2.2.1 firstClear wellFormed
  have secondPlayed := phase_ready_binding_information setup mode runtime leaks plan maximal
    horizon scheduler secondRaw who event payload binding secondRequest.2.2.1 secondClear wellFormed
  rw [firstView] at firstPlayed
  rw [secondView] at secondPlayed
  have missing := setup.commitRecovery_approximation_missing_eq_of_position finite wellFormed
    target approximation n who _ _ (firstPosition.trans secondPosition.symm) firstPlayed
      secondPlayed
  refine ⟨?_, ?_, ?_⟩
  · rw [firstView, Option.map_some, firstPosition]
  · rw [secondView, Option.map_some, secondPosition]
  · intro slotWeight slotNonnegative slotBounded firstInput secondInput firstSilent secondSilent
      firstLaw secondLaw
    have laws : firstLaw.map firstSilent = secondLaw.map secondSilent := by
      rw [phaseSourceMixture_silence_law_of_history setup mode runtime leaks bounds plan horizon
        scheduler wellFormed (approximation.sequence n) capacity first firstTrace who event payload
          binding firstActor firstRequest firstUnsent values slotWeight slotNonnegative slotBounded,
        phaseSourceMixture_silence_law_of_history setup mode runtime leaks bounds plan horizon
          scheduler wellFormed (approximation.sequence n) capacity second secondTrace who event
            payload binding secondActor secondRequest secondUnsent values slotWeight
              slotNonnegative slotBounded]
      rw [firstView, secondView]
      exact missing
    refine ⟨laws, ?_⟩
    intro firstChoice secondChoice firstSelected secondSelected
    exact (phaseSourceMixture_silence_atom setup mode runtime leaks bounds plan horizon scheduler
      wellFormed (approximation.sequence n) who first slotWeight slotNonnegative slotBounded
        firstChoice firstSelected).trans ((congrArg (fun law : PMF Bool => law true) laws).trans
          (phaseSourceMixture_silence_atom setup mode runtime leaks bounds plan horizon scheduler
            wellFormed (approximation.sequence n) who second slotWeight slotNonnegative slotBounded
              secondChoice secondSelected).symm)

end Vegas
