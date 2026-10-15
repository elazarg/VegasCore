/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingNonmissingLaw
import Vegas.Game.CommitRecoveryNonmissingSource

/-! # The chronological source policy behind actual nonmissing binding kernels -/

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
/-- Decoding the conditional typed result gives the existing structural source
policy. Its later occurrences of an owner use the updated source history. -/
theorem phaseRecoveryBindingData_source_reference
    (wellFormed : setup.WellFormed)
    (profile : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view)
    (acting : (serviceGraph setup mode).actor? event = some who) :
    PMF.map (fun data : PublicationResult (L.Val payload) × Bool =>
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm) data.1))
      ((setup.commitRecoveryNonmissingProfile profile who
        (setup.commitRecoveryClearInformation wellFormed who (some view))).map
          (fun choice => phaseRecoveryBindingData setup mode event who payload binding choice.1)) =
      (setup.commitRecoveryNonmissingSourceProfile wellFormed profile who).protocolAction
        setup.program view := by
  rw [PMF.map_comp, setup.commitRecovery_nonmissingSource_raw]
  apply congrArg (fun read => (setup.commitRecoveryNonmissingProfile profile who
    (setup.commitRecoveryClearInformation wellFormed who (some view))).map read)
  funext choice
  obtain ⟨move, action, raw, decodedAction, data⟩ := phaseRecoveryBindingData_faithful setup mode
    runtime leaks wellFormed execution who event payload binding view decoded acting choice
  dsimp only [Function.comp_def]
  rw [data]
  change decodeEventAction setup.program event
    (cast (congrArg EventField.Action binding.symm)
      (cast (congrArg EventField.Action binding) action)) = _
  rw [cast_cast, cast_eq, decodedAction, raw]
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
  (initial : PMF (phaseApplication runtime leaks).State)

local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

include capacity trace acting request unsent values

/-- The actual unsent callback's nonmissing reference is precisely the raw
choice kernel of the owning chronological source profile. No intended-view
witness or native/source belief identity is required to identify this kernel. -/
theorem phaseSourceMixture_source_reference_of_history
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
    let source := setup.commitRecoveryNonmissingSourceProfile wellFormed assessment.strategy
    ∃ view : SourceProgram.ProtocolView who setup.program,
      phaseSourceView? setup mode runtime leaks who event
        (control.execution.observe (phaseApplication runtime leaks) who) = some view ∧
      (fiberPosterior (law.map outcome) Prod.snd false).map
          (fun data => decodeEventAction setup.program event
            (cast (congrArg EventField.Action binding.symm) data.1)) =
        (source who).protocolAction setup.program view := by
  intro input outcome law source
  obtain ⟨view, decoded⟩ := phaseSourceView?_succeeds setup mode runtime leaks control.execution
    who event request.2.2.1 request.2.2.2.1 (by
      have kind : setup.eventGraph.outputLayout event = .binding who payload := binding
      change ¬(setup.eventGraph.outputLayout event).IsPublication
      rw [kind]
      exact not_false)
  refine ⟨view, decoded, ?_⟩
  have actual := phaseSourceMixture_nonmissing_result_of_history setup mode runtime leaks bounds
    wellFormed assessment who event payload binding menu plan inputs horizon scheduler capacity
    control trace acting request unsent values initial slotWeight slotNonnegative slotBounded
  change fiberPosterior (law.map outcome) Prod.snd false = _ at actual
  rw [actual, decoded]
  exact phaseRecoveryBindingData_source_reference setup mode runtime leaks wellFormed
    assessment.strategy control.execution who event payload binding view decoded request.2.2.2.1

end Vegas
