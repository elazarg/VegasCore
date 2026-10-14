/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCounterpartGuard

/-! # Failed bindings remain hidden at a forced decision

A binding read by a ready or completed reveal agrees with the corresponding
binding of an intended witness. That witness holds a value. Consequently an
unusable hidden binding cannot have reached such a reveal, which is the
visibility guard needed for directed repair of its private preparation.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  {p q : ProtocolState setup.program}

open Classical in
/-- A failed binding cannot be read by a ready or completed reveal at a native
decision whose source view has an intended witness. -/
theorem failedBinding_not_ready_or_completed (wellFormed : setup.WellFormed)
    {second : setup.intendedProtocol.History} (secondState : second.state = some q)
    (who : Player)
    (sameView : ProtocolState.observe who setup.program p =
      ProtocolState.observe who setup.program q)
    {control : (application setup leaks).Control}
    (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some control))
    (decodedP : decodedPoint setup control.execution.application.config = some p)
    (staticQ : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) q)
    (readyOwn : ∀ event, control.execution.application.config.cut.Ready event →
      ∀ owner payload binding checks outputEq codeEq,
        nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
          owner = who)
    {event : (graph setup).EventId} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks}
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq)
    (failed : ProtocolState.cell? setup.program p (fieldCell setup binding.field).1
      (.commitment owner payload) = some .failure) :
    ¬ (control.execution.application.config.cut.Ready event ∨
      event ∈ control.execution.application.config.cut.completed) := by
  intro active
  have agree := bindingCellsAgree_of_decoded wellFormed secondState who sameView trace decodedP
    staticQ readyOwn active view
  obtain ⟨value, impossible⟩ := ProtocolState.cell?_commitment_success
    (intended_of_history wellFormed second.trace q secondState) (agree.symm.trans failed)
  cases impossible

/-- The public record of a forced information set holds at every history in
that set, including histories whose hidden bindings are irregular. -/
theorem publicRecord_of_forced_information {who : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {past : List (application setup leaks).PlayerEntry}
    {view : (application setup leaks).PlayerView} (decision : site.1 = some (past, view))
    (forced : forcedAgent (bounds.onePacketMenu (runtime setup) leaks) (initialLaw setup) horizon
      scheduler who site.1)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    {control : (application setup leaks).Control} (current : history.1.state = some control) :
    PublicRecord setup who control := by
  obtain ⟨witness, witnessInfo, witnessForced⟩ := forced
  obtain ⟨found, foundState, viewEq⟩ := state_of_decision history decision
  rw [current, Option.some.injEq] at foundState
  subst found
  obtain ⟨witnessControl, witnessStateEq, witnessViewEq⟩ :=
    state_of_decision (site := site) ⟨witness, witnessInfo⟩ decision
  obtain ⟨⟨state, trace⟩, info⟩ := history
  change state = some control at current
  subst current
  obtain ⟨witnessState, witnessTrace⟩ := witness
  change witnessState = some witnessControl at witnessStateEq
  subst witnessStateEq
  have record := publicRecord_of_forced who witnessTrace witnessControl rfl witnessForced
  have sameView := viewEq.trans witnessViewEq.symm
  have samePublic : control.execution.application.publicView =
      witnessControl.execution.application.publicView := congrArg
    (fun observed : (application setup leaks).PlayerView => observed.application.publicView)
    sameView
  have sameAccepted : control.execution.application.accepted =
      witnessControl.execution.application.accepted := congrArg PublicView.accepted samePublic
  have sameOrder : control.execution.application.config.history.map EventGraph.Completion.event =
      witnessControl.execution.application.config.history.map EventGraph.Completion.event :=
    congrArg (fun publicView : PublicView (graph setup) =>
      publicView.observation.completionOrder) samePublic
  have sameSource := (sourceViewOf_eq_decodedPoint who trace).symm.trans
    ((congrArg (sourceViewOf setup leaks who) sameView).trans
      (sourceViewOf_eq_decodedPoint who witnessTrace))
  refine ⟨fun event owner payload layout other completed => ?_,
    fun player other point decoded failed => ?_⟩
  · rw [sameAccepted]
    apply record.1 event owner payload layout other
    apply (witnessControl.execution.application.config.history_exact event).mp
    rw [← sameOrder]
    exact (control.execution.application.config.history_exact event).mpr completed
  · obtain ⟨rank, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
      (bounds.onePacketMenu (runtime setup) leaks) horizon scheduler witnessTrace
      witnessControl rfl
    have witnessDecoded := decodedPoint_eq residual
    rw [decoded, witnessDecoded] at sameSource
    have observed := Option.some.inj sameSource
    exact record.2 player other _ witnessDecoded
      ((ProtocolState.revealFailed_iff_of_observe_eq player who setup.program _ _
        observed).mp failed)

end Vegas
