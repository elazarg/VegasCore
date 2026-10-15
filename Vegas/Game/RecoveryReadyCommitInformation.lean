/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryReadyCommitWitness
import Vegas.Game.PhaseEventSourceView
import Vegas.Game.CommitRecoveryClearInformation

/-! # Complete played source information at clear ready binding callbacks -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The physical decoder reads the surviving effective source action history. -/
theorem phaseSourceView?_observed
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) :
    phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) =
    decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (outputEmbedding setup.program).ref who event
      ((serviceGraph setup mode).playerStore who execution.application.current.native.config.store)
      (decodeHistory setup.program (execution.application.current.native.config.history.map
        (setup.eventGraph.fromModeCompletion mode)) who) := by
  unfold phaseSourceView?
  rw [dite_eq_left (show
    (execution.observe (phaseApplication runtime leaks) who).application.1.who = who from rfl)]
  change decodeEventView? setup.program _ _ who event _
      (decodeCompletions setup.program
        (((serviceGraph setup mode).ownCompletions who
          execution.application.current.native.config.history).map
            (setup.eventGraph.fromModeCompletion mode))) = _
  congr 1
  simp only [decodeHistory, ownCompletions, List.filter_map]
  rfl

/-- A clear source trace at an owned turn is a genuine auxiliary decision site. -/
theorem commitRecovery_isDecisionInfo_of_actor
    (setup : Setup (Player := Player) (L := L))
    (source : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some source)) (who : Player)
    (clear : source.excluded = ∅)
    (actor : ProtocolState.actor setup.program source.point = some who) :
    setup.commitRecoveryModel.IsDecisionInfo who (setup.commitRecoveryModel.infoOf who trace) := by
  have active : source.Active who := ⟨actor, by rw [clear]; exact Finset.notMem_empty _⟩
  have nonterminal : ¬ setup.commitRecoveryProtocol.terminal (some source) := by
    intro terminal
    have impossible := ProtocolState.terminal_actor_none who setup.program source.point terminal
    rw [ProtocolState.actor_observe_eq, actor] at impossible
    cases impossible
  obtain ⟨joint, legal⟩ := source.progress
  have localLegal := legal who
  cases chosen : joint who with
  | none =>
      rw [chosen] at localLegal
      exact (localLegal active).elim
  | some move =>
      rw [chosen] at localLegal
      refine ⟨⟨⟨some source, trace⟩, rfl⟩, nonterminal, move, ?_⟩
      exact (setup.commitRecoveryModel.menu_adequate who trace (some move)).mpr localLegal

/-- When an actual ready callback has an intended current-view witness, its
complete copied information is played in the auxiliary source game. An
unrealizable intended-view fallback is never treated as a source site. -/
theorem commitRecovery_isDecisionInfo_of_clear_view
    (setup : Setup (Player := Player) (L := L)) (wellFormed : setup.WellFormed)
    (who : Player) (source : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some source))
    (clear : source.excluded = ∅)
    (actor : ProtocolState.actor setup.program source.point = some who)
    (original : setup.intendedProtocol.History)
    (same : some (ProtocolState.observe who setup.program source.point) =
      setup.intendedModel.infoOf who original.trace) :
    setup.commitRecoveryModel.IsDecisionInfo who
      (setup.commitRecoveryInformation wellFormed who
        (setup.intendedModel.infoOf who original.trace)) := by
  have information := setup.commitRecoveryInformation_of_clear wellFormed who trace clear
    original same
  rw [← information]
  exact commitRecovery_isDecisionInfo_of_actor setup source trace who clear actor

end Vegas
