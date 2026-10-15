/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingNonmissingLaw
import Vegas.Game.PhaseRecoveryBindingChoice

/-! # Actual binding response atoms against the nonmissing AUX reference -/

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
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "initial" => setup.initialLaw.map
  (fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "N" => ReactiveApplication.ResponseMenu.information menu initial horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu initial horizon scheduler

include maximal in
/-- At every genuine clear unsent binding, the complete canonical/slot sending
atom factors into the positive source nonomission mass and the original AUX
conditional typed-result atom. Guard-invalid and accepted failed results remain
in this reference; no native-history/source-history weight identity is asserted. -/
theorem phaseSourceMixture_nonmissing_reference_of_history
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (capacity : horizon ≤ bounds.candidateCount)
    (control : (phaseApplication runtime leaks).Control) (trace : (E).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (acting : control.actor = some who)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (clear : control.execution.application.current.excluded = ∅)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, event⟩)
    (values : ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let input := some (control.execution.recall who,
      control.execution.observe (phaseApplication runtime leaks) who)
    let info := setup.commitRecoveryClearInformation wellFormed who
      (phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who))
    let data := fun choice : setup.commitRecoveryModel.Choice who info =>
      phaseRecoveryBindingData setup mode event who payload binding choice.1
    let outcome := fun choice : (N).Choice who input =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (choice.1.getD ⟨none⟩)
    let reference := mix slotWeight slotNonnegative slotBounded
      (phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who input)
      (phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who input)
    0 < setup.commitRecoveryNonmissingMass assessment.strategy who info ∧
      ((reference.map outcome).map Prod.snd) false =
        setup.commitRecoveryNonmissingMass assessment.strategy who info ∧
      ∀ result : PublicationResult (L.Val payload),
        (reference.map outcome) (result, false) =
          setup.commitRecoveryNonmissingMass assessment.strategy who info *
            ((setup.commitRecoveryNonmissingProfile assessment.strategy who info).map data)
              (result, false) := by
  intro input info data outcome reference
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have supported := phaseRecoveryBindingChoice_supported_of_history setup mode runtime leaks
    wellFormed assessment mixed plan maximal horizon scheduler raw who event payload binding
    request clear .failure
  change (.failure, false) ∈ ((assessment.strategy who info).map data).support at supported
  have present : false ∈ (((assessment.strategy who info).map data).map Prod.snd).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨(.failure, false), supported, rfl⟩
  have dataSnd : Prod.snd ∘ data =
      (fun choice => CommitRecoveryMove.missed choice.1) := by
    funext choice
    exact phaseRecoveryBindingData_missing setup mode who event payload binding choice.1
  have sourceMass : (((assessment.strategy who info).map data).map Prod.snd) false =
      setup.commitRecoveryNonmissingMass assessment.strategy who info := by
    rw [PMF.map_comp, dataSnd]
    rfl
  let inputs := setup.initialLaw.map encodeInputs
  have physical : ((menu).protocol (inputs.map (PhaseRuntimeState.initial plan))
      horizon scheduler).Trace (some control) := by
    dsimp only [inputs]
    rw [PMF.map_comp]
    exact trace
  have actual := phaseSourcePerturbedStrategy_result_law_of_history setup mode runtime leaks
    bounds wellFormed assessment who event payload binding menu plan inputs horizon scheduler
    capacity control physical acting request unsent values initial 0 (by norm_num) (by norm_num)
    slotWeight slotNonnegative slotBounded
  simp only [phaseSourcePerturbedStrategy, mix_zero] at actual
  change reference.map outcome = (assessment.strategy who info).map data at actual
  refine ⟨?_, ?_, ?_⟩
  · rw [← sourceMass]
    exact bot_lt_iff_ne_bot.mpr ((PMF.mem_support_iff _ _).mp present)
  · rw [actual]
    exact sourceMass
  · intro result
    rw [actual]
    have factor := fiberPosterior_disintegrate ((assessment.strategy who info).map data)
      Prod.snd false present (result, false)
    rw [sourceMass, phaseRecoveryBindingData_nonmissing setup mode wellFormed assessment.strategy
      who event payload binding _] at factor
    simpa only [Set.indicator_of_mem (show (result, false) ∈
      {pair : PublicationResult (L.Val payload) × Bool | pair.2 = false} from rfl)]
      using factor.symm

end Vegas
