/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryReadyCommitInformation

/-! # Played auxiliary information at physical commitment callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An actual ready commitment has a genuine clear source trace realizing its
whole decoded view, including effective own actions. -/
theorem RecoverySourceCheckpoint.ready_binding_sourceView
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (frontier : execution.application.Frontier) (stored : execution.application.StoredCheckpoint)
    (retained : execution.application.HistoryCheckpoint)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : execution.application.current.native.config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (clear : execution.application.entry.excluded = ∅)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs) :
    ∃ (source : CommitRecoveryState setup.program)
      (_trace : setup.commitRecoveryProtocol.Trace (some source)),
      source.excluded = ∅ ∧ source.generation = execution.application.generation ∧
      ProtocolState.actor setup.program source.point = some who ∧
      phaseSourceView? setup mode runtime leaks who event
        (execution.observe (phaseApplication runtime leaks) who) =
          some (ProtocolState.observe who setup.program source.point) := by
  obtain ⟨source, trace, excluded, generation, actor, decoded⟩ := checkpoint.ready_binding_trace
    frontier stored retained phase remaining installed kind event inside ready who payload binding
    clear valid reachable
  exact ⟨source, trace, excluded, generation, actor,
    (phaseSourceView?_observed setup mode runtime leaks execution who event).trans decoded⟩

/-- An actual intended current-view witness identifies the complete played
auxiliary source information used by the physical binding component. -/
theorem RecoverySourceCheckpoint.ready_binding_information
    {setup : Setup (Player := Player) (L := L)} {mode : ExecutionMode}
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution)
    (checkpoint : RecoverySourceCheckpoint setup mode execution.application)
    (frontier : execution.application.Frontier) (stored : execution.application.StoredCheckpoint)
    (retained : execution.application.HistoryCheckpoint)
    (phase : RuntimePhase (serviceGraph setup mode))
    (remaining : List (RuntimePhase (serviceGraph setup mode)))
    (installed : execution.application.phases = phase :: remaining)
    (kind : phase.kind = .commitment)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (ready : execution.application.current.native.config.cut.Ready event)
    (who : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (clear : execution.application.entry.excluded = ∅)
    (valid : execution.application.current.native.BindingInvariant) {inputs}
    (reachable : execution.application.current.native.config.Reachable inputs)
    (wellFormed : setup.WellFormed) (original : setup.intendedProtocol.History)
    (same : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) =
        setup.intendedModel.infoOf who original.trace) :
    setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (execution.observe (phaseApplication runtime leaks) who))) := by
  obtain ⟨source, trace, excluded, _generation, actor, decoded⟩ :=
    checkpoint.ready_binding_sourceView runtime leaks execution frontier stored retained phase
      remaining installed kind event inside ready who payload binding clear valid reachable
  rw [same]
  exact commitRecovery_isDecisionInfo_of_clear_view setup wellFormed who source trace excluded
    actor original (decoded.symm.trans same)

end Vegas
