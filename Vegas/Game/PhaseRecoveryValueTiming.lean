/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryValuePlan
import Vegas.Game.PhaseBindingCounterpart
import Vegas.Game.PhaseSourceTimingPolicy

/-! # Immutable original source values at actual physical binding callbacks -/

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

/-- At an actual initialized clear binding callback, the original global
source-policy draw followed by the original omission draw gives exactly the
physical joint result/omission/response law, for every fixed timing option.
This is an original-prior identity, before physical own-recall conditioning. -/
theorem phaseRecoveryTimingTaggedLaw_value_plan_of_history
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (ready : control.execution.application.current.native.config.cut.Ready event)
    (clear : control.execution.application.current.excluded = ∅)
    (finite : setup.program.FiniteBindingTypes) [setup.FiniteInitialLaw]
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed) (option : LateOption bounds.candidateCount) :
    (setup.commitRecoveryValuePlan finite wellFormed assessment.strategy who).bind
        (fun member =>
          (setup.commitRecoveryValuePolicy wellFormed assessment.strategy who member
            (setup.commitRecoveryClearInformation wellFormed who
              (phaseSourceView? setup mode runtime leaks who event
                (control.execution.observe (phaseApplication runtime leaks) who)))).map
                  (fun choice =>
                    let data := phaseRecoveryBindingData setup mode event who payload binding
                      choice.1
                    (data, phaseBindingTimingResponse setup mode runtime leaks bounds who event
                      payload option (control.execution.recall who)
                      (control.execution.observe (phaseApplication runtime leaks) who) data))) =
      phaseRecoveryTimingTaggedLaw setup mode runtime leaks bounds wellFormed assessment who
        event payload binding option (control.execution.recall who)
          (control.execution.observe (phaseApplication runtime leaks) who) := by
  obtain ⟨source, sourceTrace, sourceClear, _generation, actor, same⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding ready clear
  let history : setup.commitRecoveryProtocol.History := ⟨some source, sourceTrace⟩
  have running : ¬ setup.commitRecoveryProtocol.terminal history.state := by
    change ¬ ProtocolState.terminal setup.program source.point
    intro stopped
    have impossible := ProtocolState.terminal_actor_none who setup.program source.point stopped
    rw [ProtocolState.actor_observe_eq, actor] at impossible
    cases impossible
  have law := setup.commitRecoveryValuePlan_clear_law finite wellFormed assessment mixed history
    sourceClear running who
  change phaseSourceView? setup mode runtime leaks who event
      (control.execution.observe (phaseApplication runtime leaks) who) =
    setup.commitRecoveryPrivate who history.state at same
  rw [← same] at law
  let encode := fun choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who))) =>
    let data := phaseRecoveryBindingData setup mode event who payload binding choice.1
    (data, phaseBindingTimingResponse setup mode runtime leaks bounds who event payload option
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who) data)
  have moved := congrArg (PMF.map encode) law
  simpa only [PMF.map_bind, phaseRecoveryTimingTaggedLaw] using moved

end Vegas
