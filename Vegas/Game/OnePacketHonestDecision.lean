/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketHonestLaw
import Vegas.Game.CompiledPolicyView
import Vegas.Game.OnePacketPrescribedSupport
import Vegas.Game.OnePacketCanonicalPermits

/-! # As-if-honest decisions are compiled decisions of the effective opening

At an owner's turn, at an execution whose configuration decodes at its
completed prefix to a point of the intended game carrying the program's
registry and publication status, the as-if-honest native response is the
canonical source decision of the intended effective opening
(`Vegas.honestResponse_eq_openingCanonical`): the compiled decision reads the
source view the projection reads (`Vegas.compilePolicyTable_eq_protocolAction`),
and there the effective opening plays the intended law.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **As-if-honest play is the effective opening's compiled decision.** At an
owner's turn at an execution decoding to an intended point that carries the
program's registry and publication status, the as-if-honest native response of
an intended assessment, for any recall, is the canonical source decision of the
intended effective opening of its strategy. -/
theorem honestResponse_eq_openingCanonical
    (assessment : setup.intendedModel.BehavioralAssessment)
    (execution : (application setup leaks).Execution) (rank : Nat)
    (ordered : execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (staticPoint : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)
      point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (who : Player) (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event) :
    honestResponse setup leaks assessment who (execution.recall who)
        (execution.observe (application setup leaks) who) =
      sourceServiceCanonicalPolicy setup leaks
        (setup.intendedOpeningProfile assessment.strategy) who (execution.recall who)
        (execution.observe (application setup leaks) who) := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have atRank := (ready_iff_rank setup _ rank ordered event).mp ready
  let opening := setup.intendedOpeningProfile assessment.strategy
  have canonical := sourceServiceCanonicalPolicy_at_event setup leaks opening who execution
    event turn owned
  rw [show sourceServiceCanonicalPolicy setup leaks opening = serviceCanonicalPolicy setup
    .sequential (rankDeadline setup .sequential) leaks opening from rfl, canonical]
  have turnView : (execution.observe (application setup leaks) who).application.publicView.ownTurn?
      who = some event := turn
  unfold honestResponse
  rw [turnView]
  dsimp only
  rw [asIfHonestProfile_observe setup leaks assessment who execution rank ordered point decoded]
  have ownerEq : eventOwner? setup.program event = some who :=
    (eventOwner?_eq_actor setup.program event).trans owned
  have viewDecoded : decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      event.val ((graph setup).playerStore who execution.application.config.store)
      (decodeCompletions setup.program
        (((graph setup).ownCompletions who execution.application.config.history).map
          (setup.eventGraph.fromModeCompletion .sequential))) =
      some (ProtocolState.observe who setup.program point) := by
    rw [atRank]
    refine (decodeViewPrefix?_playerStore (graph := graph setup) who rank setup.program _ _ _
      _).trans ?_
    refine (congrArg (fun own => decodeViewPrefix? who setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
      rank execution.application.config.store (decodeCompletions setup.program own))
      (ownCompletions_fromModeCompletion setup (mode := .sequential) who
        execution.application.config.history)).trans ?_
    exact decodeViewPrefix?_eq_observe who rank setup.program _ [] _ _ _ _ point decoded
  have compiled := compilePolicyTable_eq_protocolAction who setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    (opening who) event _ _ _ ownerEq viewDecoded
  have disclosing : Disclosing setup.program (setup.decodeBehavioralProfile
      (CommitmentInterface.values setup.program) (setup.intendedSourceProfile assessment.strategy)
      who) :=
    BehavioralPolicy.disclosing_fromProtocol setup.program _ _
      (fun view => setup.intendedSourceProfile_notRefusal assessment.strategy who (some view))
  have actionLaw : (opening who).protocolAction setup.program
      (ProtocolState.observe who setup.program point) =
      (assessment.strategy who (setup.protocolObserve who (some point))).map Subtype.val := by
    change ((setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.intendedSourceProfile assessment.strategy) who).effectiveOpening setup.program []
        (Revelations.initial setup.context)).protocolAction setup.program _ = _
    rw [BehavioralPolicy.protocolAction_effectiveOpening setup.program _ _ _ disclosing point
      staticPoint intendedPoint]
    refine (BehavioralPolicy.protocolAction_fromProtocol setup.program _ _ _).trans ?_
    change ((assessment.strategy who (some (ProtocolState.observe who setup.program point))).map
      _).map Subtype.val = _
    rw [PMF.map_comp]
    rfl
  rw [actionLaw] at compiled
  have expand : (compileEventProfile setup.program opening who event owned
      (setup.eventGraph.fromModeObservation .sequential who
        ((graph setup).playerObserve who execution.application.config))).map
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event) =
      ((compilePolicyTable setup.program
        (ContextRefs.initial setup.context (outputLayout setup.program))
        (outputRef setup.program) who (opening who) event
        ((graph setup).playerStore who execution.application.config.store)
        (decodeCompletions setup.program
          (((graph setup).ownCompletions who execution.application.config.history).map
            (setup.eventGraph.fromModeCompletion .sequential)))).map some).map
        (fun chosen => chosen.elim ⟨none⟩ ((runtime setup).canonicalServiceDecision leaks who
          (execution.recall who) (execution.observe (application setup leaks) who) event)) := by
    rw [PMF.map_comp]
    rfl
  change _ = (compileEventProfile setup.program opening who event owned
      (setup.eventGraph.fromModeObservation .sequential who
        ((graph setup).playerObserve who execution.application.config))).map
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event)
  rw [expand, compiled]
  simp only [PMF.map_comp]
  congr 1
  funext chosen
  simp only [Function.comp_apply]
  cases (chosen.1).bind (encodeEventAction? setup.program event) <;> rfl

end Vegas
