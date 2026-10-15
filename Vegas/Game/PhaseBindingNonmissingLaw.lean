/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourceResponseLaw
import Vegas.Game.CommitRecoveryNonmissingLaw
import GameTheory.Math.Probability.ConditionalObservation

/-! # Conditional nonmissing binding laws at genuine native callbacks -/

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
/-- Reading the physical binding data preserves the separate omission flag. -/
theorem phaseRecoveryBindingData_missing (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (move : Option (CommitRecoveryMove Player L)) :
    (phaseRecoveryBindingData setup mode event who payload binding move).2 =
      CommitRecoveryMove.missed move := by
  unfold phaseRecoveryBindingData
  split
  · next missing => exact missing.symm
  · next notMissing => exact (Bool.eq_false_iff.mpr notMissing).symm

omit [Fintype Player] in
/-- Conditioning the declared data on receipt uses the original conditioned AUX
choice law. The accepted failure result remains among the nonmissing outcomes. -/
theorem phaseRecoveryBindingData_nonmissing
    (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (view : setup.ProtocolView who) :
    let info := setup.commitRecoveryClearInformation wellFormed who view
    let data := fun choice : setup.commitRecoveryModel.Choice who info =>
      phaseRecoveryBindingData setup mode event who payload binding choice.1
    fiberPosterior ((profile who info).map data) Prod.snd false =
      (setup.commitRecoveryNonmissingProfile profile who info).map data := by
  intro info data
  have same : (Prod.snd ∘ data) =
      (fun choice => CommitRecoveryMove.missed choice.1) := by
    funext choice
    exact phaseRecoveryBindingData_missing setup mode who event payload binding choice.1
  by_cases present : false ∈ ((profile who info).map
      (fun choice => CommitRecoveryMove.missed choice.1)).support
  · have moved := map_fiberPosterior_readout (profile who info) data Prod.snd false
      (same.symm ▸ present)
    rw [same] at moved
    exact moved.symm
  · have absent : false ∉ (((profile who info).map data).map Prod.snd).support := by
      simpa only [PMF.map_comp, same] using present
    rw [fiberPosterior_of_not_mem_support _ _ absent]
    unfold Setup.commitRecoveryNonmissingProfile
    rw [fiberPosterior_of_not_mem_support _ _ present]

variable (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
  (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount) (control : (phaseApplication runtime leaks).Control)
  (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
    (some control)) (acting : control.actor = some who)
  (request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, event⟩)
  (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
    PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
  (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
  (initial : PMF (phaseApplication runtime leaks).State)

local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

include capacity trace acting request unsent values

/-- The actual canonical and fresh-slot mixture, conditional on transmitting,
is exactly the nonmissing AUX binding kernel at its genuine decoded input.
Raw uniform noise is kept outside this conditional reference law. -/
theorem phaseSourceMixture_nonmissing_result_of_history
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let input := some (control.execution.recall who,
      control.execution.observe (phaseApplication runtime leaks) who)
    let outcome := fun choice : (N).Choice who input =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (choice.1.getD ⟨none⟩)
    let law := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who input)
    let info := setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who))
    fiberPosterior (law.map outcome) Prod.snd false =
      (setup.commitRecoveryNonmissingProfile assessment.strategy who info).map
        (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1) := by
  intro input outcome law info
  have actual := phaseSourcePerturbedStrategy_result_law_of_history setup mode runtime leaks
    bounds wellFormed assessment who event payload binding menu plan inputs horizon scheduler
    capacity control trace acting request unsent values initial 0 (by norm_num) (by norm_num)
    slotWeight slotNonnegative slotBounded
  simp only [phaseSourcePerturbedStrategy, mix_zero] at actual
  change fiberPosterior (law.map outcome) Prod.snd false = _
  rw [actual]
  exact phaseRecoveryBindingData_nonmissing setup mode wellFormed assessment.strategy who event
    payload binding _

end Vegas
