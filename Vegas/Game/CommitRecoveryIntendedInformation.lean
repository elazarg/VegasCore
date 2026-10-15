/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.IntendedNoDebt
import Vegas.Game.SourceIntendedTrace
import Vegas.Game.CommitRecoveryClearDecoder

/-! # Actual intended source information from clear semantic checkpoints -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- A clear initialized recovery trace whose complete source point is intended
has an initialized intended trace at the exact same point and own words. -/
theorem commitRecovery_intendedTrace (wellFormed : setup.WellFormed)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (clear : current.excluded = ∅)
    (intended : ProtocolState.Intended setup.program current.point) :
    Nonempty (setup.intendedProtocol.Trace (some current.point)) := by
  apply setup.intendedTrace_of_not_owes wellFormed
    (CommitmentInterface.forfeiture setup.program) (setup.commitRecoveryClearTrace trace clear)
  intro who
  exact ProtocolState.Intended.not_owesFailure who setup.program current.point intended

/-- An actual owned checkpoint supplies a played intended decision site and
its complete original information history. Semantic intendedness is explicit;
an empty exclusion record alone is insufficient. -/
theorem commitRecovery_intendedInformation (wellFormed : setup.WellFormed)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (clear : current.excluded = ∅)
    (intended : ProtocolState.Intended setup.program current.point)
    (who : Player) (actor : ProtocolState.actor setup.program current.point = some who) :
    ∃ site : setup.intendedModel.InformationSite who,
      ∃ original : setup.intendedModel.InformationHistory who site.1,
        original.1.state = some current.point ∧
        site.1 = some (ProtocolState.observe who setup.program current.point) ∧
        setup.commitRecoveryClearInformation wellFormed who site.1 =
          setup.commitRecoveryInformation wellFormed who site.1 := by
  obtain ⟨original⟩ := setup.commitRecovery_intendedTrace wellFormed current trace clear intended
  have active : setup.intendedProtocol.active (some current.point) who := by
    change ProtocolView.actor who setup.program
      (ProtocolState.observe who setup.program current.point) = some who
    exact (ProtocolState.actor_observe_eq _ _ _).trans actor
  have nonterminal : ¬ setup.intendedProtocol.terminal (some current.point) := by
    intro terminal
    have impossible := ProtocolState.terminal_actor_none who setup.program current.point terminal
    rw [ProtocolState.actor_observe_eq, actor] at impossible
    cases impossible
  obtain ⟨joint, legal⟩ := setup.intendedProtocol.progress (some current.point) nonterminal
  have chosen := legal who
  have decision : setup.intendedModel.IsDecisionInfo who
      (setup.intendedModel.infoOf who original) := by
    cases choice : joint who with
    | none =>
        rw [choice] at chosen
        exact (chosen active).elim
    | some action =>
        rw [choice] at chosen
        exact ⟨⟨⟨some current.point, original⟩, rfl⟩, nonterminal, action,
          (setup.intendedModel.menu_adequate who original (some action)).mpr chosen⟩
  refine ⟨⟨setup.intendedModel.infoOf who original, decision⟩,
    ⟨⟨some current.point, original⟩, rfl⟩, rfl, setup.intended_info who original, ?_⟩
  exact setup.commitRecoveryClearInformation_intended wellFormed who
    ⟨some current.point, original⟩

end Vegas.SourceProgram.Setup
