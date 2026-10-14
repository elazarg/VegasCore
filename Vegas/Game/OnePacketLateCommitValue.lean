/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateReveal
import Vegas.Game.OnePacketCommitmentCompletion
import Vegas.Game.OnePacketLateCommitments

/-! # The completion value of a late commitment

After a commitment of the owner's binding to an openable value, every stop of
play until the event completes is at the point the committed value's source
choice reaches, or has failed the event. So at a late delivery, committing a
value whose source choice reaches an intended point has, from every history
whose decoded point the intended game reaches, completion value exactly one less
its failure probability times the value of committing that choice
(`Vegas.lateCommit_historyNear`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- **The completion value of a late commitment.** Under a scheduler completing
play, at a late delivery of the binding `event` of `who`, let a choice commit,
at the player's turn, the event to a prepared slot whose meaning after the
response is the value `value`, and let the source choice of that value reach
only intended points from the decoded point. From every history of the site
whose configuration is a prefix of the site's rank decoding to a point the
intended game reaches, the completion value of the choice is exactly one less
its failure probability times the value of committing that source choice. -/
theorem lateCommit_historyNear [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).History]
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (assessment : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralAssessment) (profile : BehavioralProfile setup.program) {who : Player}
    (site : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationSite who)
    {key : LateKey setup leaks}
    {event : (graph setup).EventId} (decided : decidedEvent key = some event)
    (pending : pendingEvent setup leaks who site.1 = some event)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).Choice who site.1) (response : (application setup leaks).Action)
    (selected : choice.1 = some response)
    (history : (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (member : response ∈ bounds.onePacketActions (runtime setup) leaks who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (material : (application setup leaks).Submission)
    (sends : response.transmission = some material) {serial : Nat}
    (packet : material.call.packet = .commitment event (who, .prepared serial))
    (turn : execution.application.publicView.ownTurn? who = some event)
    (ordered : execution.application.config.cut.IsPrefix (siteRank site.1))
    {payload : L.Ty} (outputEq : (graph setup).outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload)
    {value : L.Val payload}
    (after : material.call.candidateAfter who
      (execution.observe (application setup leaks) who).application.candidates
      (.prepared serial) = .openable ⟨payload, value⟩)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup (siteRank site.1) execution.application.config =
      some point)
    (reachedPoint : IntendedReached setup point)
    (targetIntended : ∀ target ∈ (ProtocolState.step setup.program point
      (fun _ => sourceOfValue setup event outputEq value)).support,
      ProtocolState.Intended setup.program target)
    {bound : ℝ} (readoutBounded : ∀ readout,
      |exclusionReadoutUtility setup parameter utility excludedPayoff readout who| ≤ bound) :
    historyStopValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
        assessment profile site (PMF.pure choice) history.1 =
      (1 - siteHistoryFailure setup leaks bounds horizon scheduler assessment site
          (PMF.pure choice) history) *
        decodedCommitValue setup leaks bounds horizon scheduler parameter utility excludedPayoff
          profile who (siteRank site.1) (sourceOfValue setup event outputEq value) history.1 := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
  have horizonBound := menu.bounded (initialLaw setup) horizon scheduler
  let certificate := horizonBound.wellFoundedHistories
  let installed := Profile.update (sig := model.behavioralSignature)
    assessment.strategy who ((assessment.strategy who).withLaw site.1 (PMF.pure choice))
  have freshIff : ∀ control, siteFresh who site.1 control ↔
      ¬ StoreEventFailed control.execution.application.config.store event := by
    intro control
    simp only [siteFresh, pending]
  have ready : execution.application.config.cut.Ready event :=
    (execution.application.publicView_eventReady event).mp
      (PublicView.ownTurn?_spec _ who event turn).1
  have traceHere : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.1.trace
  -- The committed action and the point it reaches.
  let committed : (graph setup).Action event :=
    cast (congrArg EventGraph.EventField.Action outputEq.symm) (PublicationResult.success value)
  have successful : (cast (congrArg EventGraph.EventField.Action outputEq) committed :
      PublicationResult (L.Val payload)) = .success value := by
    simp only [committed, cast_cast, cast_eq]
  have owned : (graph setup).actor? event = some who := nodeView_bind_actor outputEq codeEq
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => decodeEventAction setup.program event committed) (acts who)
  have intended := targetIntended target (by
    change target ∈ (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event committed)).support
    rw [stepEq]
    exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨found, ⟨residualFound⟩⟩ := protocol_sourceResidual (failureProfile setup.program)
    menu horizon scheduler traceHere _ rfl
  have foundEq : found = siteRank site.1 :=
    isPrefix_unique residualFound.checkpoint.ordered ordered
  have residual := foundEq ▸ residualFound
  -- The owner's first step performs the commitment.
  have notStopped : ¬ LateStopped setup leaks bounds horizon scheduler (siteRank site.1)
      history.1 := by
    rintro ⟨control, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self _ (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.1.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have infoEq : model.infoOf who history.1.trace = site.1 := history.2
  have stepStates := menu.run_one_response (initialLaw setup) horizon scheduler installed
    history.1 who remaining execution current
  have responseLaw : (installed who (some (execution.recall who,
      execution.observe (application setup leaks) who))).map
        (fun choice => choice.1.getD ⟨none⟩) = PMF.pure response := by
    rw [← atSite]
    simp only [installed, Profile.update_same, BehavioralPolicy.withLaw_self, PMF.pure_map,
      selected, Option.getD_some]
  rw [decodeProfile_eq_map, responseLaw, PMF.pure_map] at stepStates
  have stops : ∀ stop ∈ (model.runBehavioralUntil certificate installed
      (LateStopped setup leaks bounds horizon scheduler (siteRank site.1)) history.1).support,
      ∃ final, stop.state = some final ∧
        (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
            (siteFresh who site.1) stop = some target ∨
          (completionPoint setup leaks bounds horizon scheduler (siteRank site.1)
              (siteFresh who site.1) stop = none ∧
            StoreEventFailed final.execution.application.config.store event)) := by
    intro stop stopMember
    rw [model.runBehavioralUntil_of_running certificate installed notStopped running,
      PMF.mem_support_bind_iff] at stopMember
    obtain ⟨next, nextMember, reached⟩ := stopMember
    have nextState : next.state = some ⟨remaining, none,
        execution.respond (application setup leaks) who response⟩ := by
      have inStates : next.state ∈ ((model.runBehavioralFrom installed 1 history.1).map
          History.state).support := (PMF.mem_support_map_iff _ _ _).mpr ⟨next, nextMember, rfl⟩
      rw [stepStates, PMF.mem_support_pure_iff] at inStates
      exact inStates
    have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond (application setup leaks) who response⟩) :=
      nextState ▸ next.trace
    obtain ⟨acceptance, lookup⟩ := acceptanceInvariant_respond_commitment traceHere event turn
      outputEq response member material sends packet after afterTrace
    obtain ⟨_, records, emitted, _, _, stable, _⟩ := acceptance
    have invariant : OpenableCommitmentInvariant setup leaks bounds horizon scheduler who
        (respondEntry setup leaks execution who response)
        (sentEnvelope setup leaks execution who material) event (who, .prepared serial) outputEq
        value execution.application.config ready committed next.state := by
      rw [nextState]
      refine ⟨⟨afterTrace⟩, records, emitted, rfl, packet, lookup, stable, fun done => ?_⟩
      exact ((ready.1 (by
        rw [← ((runtime setup).reactive_respond_application leaks execution who response).1]
        exact done))).elim
    obtain ⟨final, finalState, stepped⟩ := openableCommitment_stop bounds horizon scheduler
      completes certificate installed codeEq successful ordered next invariant stop reached
    refine ⟨final, finalState, ?_⟩
    rcases stepped with inStep | ⟨failing, failed, inStep⟩
    · have pointEq := completionPoint_of_mem_step (fresh := siteFresh who site.1) residual
        decoded ready stepEq finalState inStep
      by_cases freshHere : siteFresh who site.1 final
      · left
        rw [pointEq, ite_eq_left ⟨intended, freshHere⟩ ..]
      · right
        exact ⟨by rw [pointEq, ite_eq_right (fun good => freshHere good.2) ..],
          not_not.mp ((not_congr (freshIff final)).mp freshHere)⟩
    · right
      have output := step_binding_output (outputEq := outputEq) (codeEq := codeEq) inStep
      have failedHere : StoreEventFailed final.execution.application.config.store event :=
        ⟨_, by rw [EventGraph.Config.store_output, output],
          (isFailure_cast_binding_iff outputEq _).mpr failed⟩
      exact ⟨completionPoint_eq_none_of_not_fresh finalState fun freshHere =>
        (freshIff final).mp freshHere failedHere, failedHere⟩
  rw [historyStopValue_eq_of_stops parameter utility excludedPayoff completes assessment site
    decided pending (PMF.pure choice) history current ordered ready profile stops
    readoutBounded]
  congr 1
  unfold decodedCommitValue
  rw [current]
  dsimp only
  rw [decoded]
  dsimp only
  rw [ite_eq_left reachedPoint ..]
  change sourcePointValue setup parameter utility excludedPayoff profile who target =
    expect (ProtocolState.step setup.program point
      (fun _ => decodeEventAction setup.program event committed))
      (sourcePointValue setup parameter utility excludedPayoff profile who)
  rw [stepEq, expect_pure]

end Vegas
