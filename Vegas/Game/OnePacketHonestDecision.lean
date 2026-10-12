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

section Recorded

/-- An earlier turn of `who` at `event` in its recall. -/
def SeenTurn (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry) : Prop :=
  ∃ entry ∈ past, entry.beforeView.application.publicView.ownTurn? who = some event

/-- After an earlier turn at an event, the first-turn clients are silent at
every later turn at it. -/
theorem openingClients_later_silent (bound : (graph setup).EventId → Nat) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (seen : SeenTurn who event past) :
    openingClients setup leaks bound turns intended who past view = PMF.pure ⟨none⟩ := by
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  rw [openingClients, firstTurnPolicy_eq_family owned turn]
  unfold serviceTurnFamily
  rw [(application setup leaks).turnScheduledPolicy_unselected _ _ _ _ past view]
  · rfl
  · intro slot selected counted
    cases selected
    change (if view.application.publicView.ownTurn? who = some event then
      some (past.countP fun entry =>
        decide (entry.beforeView.application.publicView.ownTurn? who = some event))
      else none) = some 0 at counted
    rw [ite_eq_left turn ..] at counted
    rw [Option.some.injEq, List.countP_eq_zero] at counted
    obtain ⟨entry, member, earlier⟩ := seen
    exact counted entry member (decide_eq_true earlier)

/-- The first-turn clients never submit for an event after an earlier turn at it
at which they did not. -/
theorem openingClients_keeps_unrecorded (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player)
    (event : (graph setup).EventId) :
    ∀ (more : Nat) (execution : (application setup leaks).Execution),
      (runtime setup).eventRecorded leaks (execution.recall who) event = false →
      SeenTurn who event (execution.recall who) →
      ∀ final ∈ ((application setup leaks).runRounds scheduler
          (openingClients setup leaks bound turns intended) more execution).support,
        (runtime setup).eventRecorded leaks (final.recall who) event = false ∧
          SeenTurn who event (final.recall who) := by
  let app := application setup leaks
  intro more
  induction more with
  | zero =>
      intro execution unrecorded seen final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨unrecorded, seen⟩
  | succ more ih =>
      intro execution unrecorded seen final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      refine ih middle ?_ ?_ final rest
      all_goals
        obtain ⟨command, _, between, stepped, cases⟩ := round_cases setup leaks moved
        have recallEq := app.environmentStep_recall execution between command stepped
      · rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, chosen, rfl⟩
        · rw [recallEq]
          exact unrecorded
        · by_cases same : responder = who
          · subst responder
            obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks between who response
            rw [recalled]
            apply Bool.eq_false_of_not_eq_true
            intro recorded
            obtain ⟨entry, member, submitted⟩ :=
              ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
            rcases List.mem_append.mp member with old | new
            · have before := ((runtime setup).eventRecorded_iff leaks _ event).mpr
                ⟨entry, old, submitted⟩
              rw [recallEq, unrecorded] at before
              cases before
            · cases List.mem_singleton.mp new
              have turn := sourceServiceTurnPolicy_submitsAtTurn setup leaks bound turns
                (firstTurnTiming setup turns .sequential) (setup.intendedOpeningProfile intended)
                who _ _ response chosen event submitted
              have earlier : SeenTurn who event (between.recall who) := by
                rw [recallEq]
                exact seen
              rw [openingClients_later_silent bound turns intended who _ _ event turn earlier,
                PMF.mem_support_pure_iff] at chosen
              subst chosen
              cases submitted
          · rw [app.respond_recall_other between responder who (Ne.symm same) response, recallEq]
            exact unrecorded
      · obtain ⟨entry, member, earlier⟩ := seen
        refine ⟨entry, ?_, earlier⟩
        rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
        · rw [recallEq]
          exact member
        · have grown := app.respond_recall_mono between responder who response
          rw [recallEq] at grown
          exact grown member

end Recorded

end Vegas
