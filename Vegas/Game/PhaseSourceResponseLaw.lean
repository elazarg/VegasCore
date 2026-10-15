/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseSourcePerturbation
import Vegas.Game.PhaseSourcePolicyLaw
import Vegas.Game.PhaseSourceSlotPolicyLaw

/-! # Exact typed response laws under independent native perturbations -/

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

local notation "app" => phaseApplication runtime leaks

omit [Fintype Player] in
private theorem recoveryBindingResponse_outcome (execution : (app).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (move : Option (CommitRecoveryMove Player L)) :
    let response := phaseRecoveryBindingResponse setup mode runtime leaks who event payload
      binding serial move
    let fixed := ((execution.respond app who response).application.current.native.bindingResult
      (who, .prepared serial) payload, response.transmission.isNone)
    phaseBindingResponseOutcome setup mode runtime leaks execution who payload response =
      if fixed.2 then (.failure, true) else fixed := by
  dsimp only
  cases missing : (phaseRecoveryBindingData setup mode event who payload binding move).2 with
  | false =>
      simp only [phaseRecoveryBindingResponse, missing, Bool.false_eq_true, ↓reduceIte]
      rfl
  | true =>
      simp only [phaseRecoveryBindingResponse, missing, ↓reduceIte]
      rfl

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

include capacity trace acting request unsent values

/-- Read the declared result from the slot actually named by each response.
The canonical dispatcher and the slot tier therefore share one outcome map. -/
theorem phaseSourcePolicy_result_law_of_history :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who) (control.execution.observe app who)).map
      (phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload) =
      (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe app who)))).map
        (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1) := by
  obtain ⟨view, serial, decoded, _bounded, law, result⟩ :=
    phaseSourcePolicy_binding_of_history setup mode runtime leaks bounds wellFormed assessment
      who event payload binding menu plan inputs horizon scheduler capacity control trace acting
        request unsent values
  let tidy := fun data : PublicationResult (L.Val payload) × Bool =>
    if data.2 then (.failure, true) else data
  have common :
      (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who) (control.execution.observe app who)).map
          (phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload) =
      ((phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
        (control.execution.recall who) (control.execution.observe app who)).map
          (fun response => ((control.execution.respond app who response).application.current.native
            |>.bindingResult (who, .prepared serial) payload, response.transmission.isNone))).map
              tidy := by
    rw [PMF.map_comp, law, PMF.map_comp, PMF.map_comp]
    apply congrArg (fun f =>
      (assessment.strategy who
        (setup.commitRecoveryClearInformation wellFormed who (some view))).map f)
    funext choice
    exact recoveryBindingResponse_outcome setup mode runtime leaks control.execution who event
      payload binding serial choice.1
  rw [common, result, PMF.map_comp, decoded]
  apply congrArg (fun f =>
    (assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who (some view))).map f)
  funext choice
  dsimp only [Function.comp_def, tidy]
  unfold phaseRecoveryBindingData
  split <;> rfl

variable (initial : PMF (phaseApplication runtime leaks).State)

local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

/-- At an actual unsent binding, both source tiers have exactly the same joint
typed-result/omission law. Only raw noise contaminates that law. -/
theorem phaseSourcePerturbedStrategy_result_law_of_history
    (noise : ℝ) (nonnegative : 0 ≤ noise) (bounded : noise ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1) :
    let input := some (control.execution.recall who, control.execution.observe app who)
    let outcome := fun choice : (N).Choice who input =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (choice.1.getD ⟨none⟩)
    ((phaseSourcePerturbedStrategy setup mode runtime leaks bounds initial horizon scheduler
      wellFormed assessment noise nonnegative bounded slotWeight slotNonnegative slotBounded who
        input).map outcome) =
      mix noise nonnegative bounded
        (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy initial horizon scheduler
          who input).map outcome)
        ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event
            (control.execution.observe app who)))).map
              (fun choice => phaseRecoveryBindingData setup mode event who payload binding
                choice.1)) := by
  intro input outcome
  have main := phaseSourcePolicy_result_law_of_history setup mode runtime leaks bounds wellFormed
    assessment who event payload binding menu plan inputs horizon scheduler capacity control
      trace acting request unsent values
  have slots := (phaseSourceSlotPolicy_binding_of_history setup mode runtime leaks bounds
    wellFormed assessment who event payload binding menu plan inputs horizon scheduler capacity
      control trace acting request unsent values).2
  let source := (assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
    (phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe app who)))).map
        (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1)
  have canonical : ((phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment
      initial horizon scheduler who) input).map outcome = source := by
    change PMF.map ((fun response : Option (app).Action =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (response.getD ⟨none⟩)) ∘ Subtype.val)
      ((phaseSourceStrategy setup mode runtime leaks bounds wellFormed assessment initial horizon
        scheduler who) input) = source
    rw [← PMF.map_comp, phaseSourceStrategy_map_val, PMF.map_comp]
    exact main
  have slotted : ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment
      initial horizon scheduler who) input).map outcome = source := by
    change PMF.map ((fun response : Option (app).Action =>
      phaseBindingResponseOutcome setup mode runtime leaks control.execution who payload
        (response.getD ⟨none⟩)) ∘ Subtype.val)
      ((phaseSourceSlotStrategy setup mode runtime leaks bounds wellFormed assessment initial
        horizon scheduler who) input) = source
    rw [← PMF.map_comp, phaseSourceSlotStrategy_map_val, PMF.map_comp]
    exact slots
  unfold phaseSourcePerturbedStrategy
  rw [mix_map, mix_map, canonical, slotted, mix_self]

end Vegas
