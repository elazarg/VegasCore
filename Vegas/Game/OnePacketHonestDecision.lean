/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketHonestLaw
import Vegas.Game.CompiledPolicyView
import Vegas.Game.OnePacketPrescribedSupport
import Vegas.Game.OnePacketCanonicalPermits
import Vegas.Game.OnePacketPendingPool
import Vegas.Game.SourceServiceFirstTurnRisk
import Interaction.ReactiveTrafficIdentity

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

/-- **Earlier turns are answered.** For a well-formed setup, under the
asynchronous contract with timely delays, at every execution the first-turn
clients of the intended effective opening reach within the horizon, an owner
that had a turn at its event has submitted for it. -/
theorem openingClients_recorded_of_seen [Finite Player] (wellFormed : setup.WellFormed)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) {count : Nat}
    (within : count ≤ horizon) {execution : (application setup leaks).Execution}
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (openingClients setup leaks bound turns intended) count).support)
    (who : Player) (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (seen : SeenTurn who event (execution.recall who)) :
    (runtime setup).eventRecorded leaks (execution.recall who) event = true := by
  let app := application setup leaks
  let players := openingClients setup leaks bound turns intended
  apply Bool.eq_true_of_not_eq_false
  intro unrecorded
  cases node : nodeView (graph setup) event with
  | sample payload law outputEq codeEq =>
      have none := nodeView_sample_actor outputEq codeEq
      rw [owned] at none
      cases none
  | bind actor payload outputEq codeEq =>
      obtain ⟨entry, member, turn⟩ := seen
      have recorded := (sourceServiceFirstTurn_recallFacts contract timely players who turns
        (setup.intendedOpeningProfile intended) rfl count within execution supported).1 entry
        member event actor payload turn outputEq
      rw [unrecorded] at recorded
      cases recorded
  | resolve actor payload binding checks outputEq codeEq =>
      obtain ⟨final, finalMem⟩ :=
        (app.runRounds scheduler players (horizon - count) execution).support_nonempty
      have kept := (openingClients_keeps_unrecorded scheduler bound turns intended who event
        (horizon - count) execution unrecorded seen final finalMem).1
      have atHorizon := mem_roundsFrom_of_runRounds (app := app) supported finalMem
      rw [show count + (horizon - count) = horizon by omega] at atHorizon
      obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
        horizon le_rfl final atHorizon
      rw [Nat.sub_self] at trace
      have terminalCut := contract.completes ⟨0, none, final⟩ trace ⟨rfl, rfl⟩
      have completed : event ∈ final.application.config.cut.completed := by
        change final.application.config.cut.completed = Finset.univ at terminalCut
        rw [terminalCut]
        exact Finset.mem_univ _
      obtain ⟨rank, ⟨residual⟩, intendedHolds⟩ := openingClients_intended (profile :=
        setup.intendedOpeningProfile intended) wellFormed contract timely turns intended horizon
        le_rfl final atHorizon
      obtain ⟨recordRank, ⟨recordResidual⟩, record⟩ :=
        publicationRecord_history (setup.intendedOpeningProfile intended) horizon scheduler trace
      rcases record with failed | accepted
      · have sameRank := isPrefix_unique recordResidual.checkpoint.ordered
          residual.checkpoint.ordered
        subst sameRank
        obtain ⟨other, revealFailed⟩ := failed _ residual.decode
        exact ProtocolState.not_excluded_of_intended other setup.program _
          (intendedHolds _ residual.decode)
          (ProtocolState.RevealFailed.excluded setup.program _ revealFailed)
      · obtain ⟨message, present, _, named, sender⟩ := accepted event completed payload outputEq
        have senderEq : message.sender = who := Option.some.inj (sender.symm.trans owned)
        have input := app.ledger_subset_inputs_history (initialLaw setup) horizon scheduler
          ⟨0, none, final⟩ trace present
        have output : message ∈ app.outputs (final.recall who) := by
          rw [← app.history_inputRecall (initialLaw setup) horizon scheduler trace who]
          exact List.mem_filter.mpr ⟨input, by simp [senderEq]⟩
        exact output_event trace who event kept message output named

end Recorded

section Repeated

/-- Every transmitting recall entry emitted the packet of its submission. -/
def TransmissionsEmitted (execution : (application setup leaks).Execution) : Prop :=
  ∀ who, ∀ entry ∈ execution.recall who, ∀ material, entry.action.transmission = some material →
    ∃ message, entry.emitted = some message ∧ message.payload.call = material.call.packet

/-- Transmissions are emitted at every history, under arbitrary responses and
scheduler choices. -/
theorem transmissionsEmitted_serviceInvariant (scheduler : (application setup leaks).Scheduler) :
    (application setup leaks).ServiceInvariant scheduler (TransmissionsEmitted (leaks := leaks))
    where
  respond execution responder action valid := by
    intro who entry member material transmits
    rw [(runtime setup).respond_recall leaks execution responder who action] at member
    split at member
    · rename_i same
      subst same
      rcases List.mem_append.mp member with old | new
      · exact valid who entry old material transmits
      · cases List.mem_singleton.mp new
        change action.transmission = some material at transmits
        refine ⟨_, by rw [transmits]; rfl, rfl⟩
    · exact valid who entry member material transmits
  environment execution next command valid _ moved := by
    intro who entry member
    rw [(application setup leaks).environmentStep_recall execution next command moved] at member
    exact valid who entry member

/-- **A repeated packet is not a one-packet response.** At every history, under
arbitrary responses and scheduler choices, a canonical decision of `who` at its
turn `event` that transmits, after its recall has submitted for `event`, is not
in the one-packet menu. -/
theorem canonical_not_onePacket_of_recorded [Fintype Player] (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {control : (application setup leaks).Control}
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control))
    (who : Player) (event : (graph setup).EventId)
    (recorded : (runtime setup).eventRecorded leaks (control.execution.recall who) event = true)
    (action : (graph setup).Action event)
    (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
      (control.execution.observe (application setup leaks) who) event action).transmission =
        some material) :
    (runtime setup).canonicalServiceDecision leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) event action ∉
      bounds.onePacketActions (runtime setup) leaks who (control.execution.recall who)
        (control.execution.observe (application setup leaks) who) := by
  let app := application setup leaks
  intro member
  obtain ⟨_, sent⟩ := (bounds.mem_onePacketActions (runtime setup) leaks who _ _ _).mp member
  rcases sent with silent | ⟨chosen, transmits, permitted⟩
  · rw [silent] at submits
    cases submits
  · rw [submits] at transmits
    have same := Option.some.inj transmits
    subst same
    have named : material.call.packet.event? (graph setup) = some event := by
      rcases (runtime setup).canonicalServiceDecision_cases leaks who
          (control.execution.recall who) (control.execution.observe app who) event action with
        silent | submitted
      · rw [silent] at submits
        cases submits
      · unfold EventGraphRuntime.submittedEvent? at submitted
        rw [submits] at submitted
        exact submitted
    have recalled := (runtime setup).countRecall_history leaks trace
    rw [(runtime setup).localEnvelope_eq_of_recall leaks control.execution recalled.1
      recalled.2.1 who material, countPermits_eq_true_iff] at permitted
    obtain ⟨entry, entryMember, submitted⟩ :=
      ((runtime setup).eventRecorded_iff leaks _ event).mp recorded
    obtain ⟨entryMaterial, entryTransmits⟩ : ∃ entryMaterial,
        entry.action.transmission = some entryMaterial := by
      unfold EventGraphRuntime.submittedEvent? at submitted
      cases transmission : entry.action.transmission with
      | none => rw [transmission] at submitted; cases submitted
      | some entryMaterial => exact ⟨entryMaterial, rfl⟩
    have entryNamed : entryMaterial.call.packet.event? (graph setup) = some event := by
      unfold EventGraphRuntime.submittedEvent? at submitted
      rw [entryTransmits] at submitted
      exact submitted
    obtain ⟨message, emitted, call⟩ :=
      ((transmissionsEmitted_serviceInvariant scheduler).history (initialLaw setup) horizon
        (fun _ _ _ entry member => (List.not_mem_nil member).elim) trace) who entry entryMember
        entryMaterial entryTransmits
    have output : message ∈ app.outputs (control.execution.recall who) :=
      List.mem_filterMap.mpr ⟨entry, entryMember, emitted⟩
    have earlier := earlierOwnPacket_of_output trace who
      (app.packet (app.submit control.execution.application who material) who
        (control.execution.network.known who) material) message output
    have distinct := permitted.2.2 message earlier
    apply distinct
    change message.payload.call.event? (graph setup) =
      material.call.packet.event? (graph setup)
    rw [call, entryNamed, named]

end Repeated

end Vegas
