/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketPrescribedCompletion
import Vegas.Game.ServiceRevealDecode

/-! # The completion point after disclosing at the first activation

**The stop after an accepted packet.** Let who have sent a packet for the event
of rank rank from a configuration at which it is ready, with the acceptance
invariant holding and the packet settling once the event completes. Under play
of any profile until the event completes, under a scheduler completing play,
every stop completes the event from the sending configuration, and the event's
output is a success (`Vegas.accepted_stop_config`).

**A successful resolution discloses.** A resolve event completed with a
successful output was completed by the disclosing action
(`Vegas.disclose_of_outputSucceeded`).

**Disclosing at the first activation.** Under the asynchronous contract and the
timeliness margin, at a first activation for a resolve event whose configuration
decodes to a point of the intended game, the canonical decision disclosing, when
it transmits, has, under play of any other policies until the event completes,
the completion-point law of the source step of the disclosure, with success one
and no error (`Vegas.firstActivation_disclose_completionPointLaw`). Installing
the slot-trembled prescribed component there gives the step of the intended
effective opening with error six times the scale
(`Vegas.firstActivation_prescribed_disclose_completionPointLaw`).
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

variable (setup leaks bounds horizon scheduler) in
/-- After a recorded send of message for event from sent: the acceptance
invariant, and, once the event has completed, the configuration is one step of
the event from sent. -/
private def AcceptedInvariant (who : Player) (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event sent
          (some control) ∧
        (event ∈ control.execution.application.config.cut.completed →
          ∃ action, control.execution.application.config ∈
            (sent.step event ready action).support)

/-- The invariant passes along every transition from a state where the event
of rank rank has not completed. -/
private theorem acceptedInvariant_transition {who : Player}
    {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {ready : sent.cut.Ready event} {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) (before after : (application setup leaks).ProtocolState)
    (going : ∀ control, before = some control →
      ¬ control.execution.application.config.cut.IsPrefix (rank + 1))
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : AcceptedInvariant setup leaks bounds horizon scheduler who entry message event sent
      ready before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    AcceptedInvariant setup leaks bounds horizon scheduler who entry message event sent ready
      after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨invariant, completion⟩ := holds
      have afterInvariant := acceptanceInvariant_transition bounds horizon scheduler who entry
        message event sent (some control) after joint legal invariant reached
      cases after with
      | none => exact afterInvariant.elim
      | some next =>
          refine ⟨afterInvariant, fun completedNext => ?_⟩
          have pending : event ∉ control.execution.application.config.cut.completed := by
            intro done
            obtain ⟨action, member⟩ := completion done
            apply going control rfl
            have rankEq := (ready_iff_rank setup sent rank ordered event).mp ready
            rw [sent.step_cut event ready action _ member]
            exact ordered.complete_at event ready rankEq
          have atSent := invariant.2.2.2.2.2.1 pending
          rcases transition_configStep (initialLaw setup) horizon scheduler control next joint
              reached with same | ⟨other, otherReady, action, member⟩
          · rw [same] at completedNext
            exact (pending completedNext).elim
          · revert otherReady member
            rw [atSent]
            intro otherReady member
            rw [atSent] at pending
            rw [sent.step_cut other otherReady action _ member, EventOrder.Cut.mem_complete]
              at completedNext
            rcases completedNext with rfl | earlier
            · exact ⟨action, member⟩
            · exact (pending earlier).elim

/-- A recorded accepted call retains its sent configuration while pending,
and every completed stopped endpoint performs its successful compiled event
step. Settlement is required only on this actual stopped law. -/
theorem accepted_until_config
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (extraStop : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History → Prop)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent)
    (settles : ∀ stopped ∈ (((bounds.onePacketMenu (runtime setup) leaks).information
        (initialLaw setup) horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          extraStop history) start).support,
      ∀ final, stopped.state = some final → RecordsEntry setup leaks who entry (some final) →
        event ∈ final.execution.application.config.cut.completed →
          (message.id, true) ∈ final.execution.receipts) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
          extraStop history) start).support,
      ∃ final, stop.state = some final ∧
        (event ∉ final.execution.application.config.cut.completed →
          final.execution.application.config = sent) ∧
        (event ∈ final.execution.application.config.cut.completed →
          ∃ action, final.execution.application.config ∈ (sent.step event ready action).support ∧
            OutputSucceeded final.execution.application.config.store event) := by
  intro stop member
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have holds : AcceptedInvariant setup leaks bounds horizon scheduler who entry message event sent
      ready start.state := by
    rw [current]
    refine ⟨invariant, fun done => ?_⟩
    rw [atSent] at done
    exact (ready.1 done).elim
  have reachedInvariant := model.runBehavioralUntil_support_closed_of_going certificate players
    (fun history => LateStopped setup leaks bounds horizon scheduler rank history ∨
      extraStop history)
    (AcceptedInvariant setup leaks bounds horizon scheduler who entry message event sent ready)
    (fun history going _ joint legal target holds reached =>
      acceptedInvariant_transition ordered history.state target
        (fun control state prefixed => going (Or.inl ⟨control, state, prefixed⟩)) joint legal holds
        reached)
    start holds stop member
  cases state : stop.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some final =>
      rw [state] at reachedInvariant
      obtain ⟨finalInvariant, completion⟩ := reachedInvariant
      obtain ⟨⟨finalTrace⟩, records, _, _, _, stable, settled⟩ := finalInvariant
      refine ⟨final, rfl, stable, fun done => ?_⟩
      obtain ⟨action, stepMember⟩ := completion done
      exact ⟨action, stepMember, settled (settles stop member final state records done)⟩

/-- **The stop after an accepted packet.** Let who have sent message, recorded
by entry, from the configuration sent at which the event of rank rank is ready.
Suppose the acceptance invariant holds at a history at sent, and the packet has
an accepting receipt at every later history recording it at which the event has
completed. Then, under a scheduler completing play, every stop of play of any
profile until the event completes completes the event from sent, and the
event's output is a success. -/
theorem accepted_stop_config
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank)
    (settles : ∀ control, ((bounds.onePacketMenu (runtime setup) leaks).protocol
        (initialLaw setup) horizon scheduler).Trace (some control) →
      RecordsEntry setup leaks who entry (some control) →
      event ∈ control.execution.application.config.cut.completed →
        (message.id, true) ∈ control.execution.receipts)
    (start : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History) {control : (application setup leaks).Control}
    (current : start.state = some control)
    (invariant : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent (some control))
    (atSent : control.execution.application.config = sent) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start).support,
      ∃ final action, stop.state = some final ∧
        final.execution.application.config ∈ (sent.step event ready action).support ∧
        OutputSucceeded final.execution.application.config.store event := by
  intro stopped supported
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have partialLaw := accepted_until_config certificate players (fun _ => False) ready ordered
    start current invariant atSent
    (fun final _ control equal records done =>
      settles control (equal ▸ final.trace) records done)
  obtain ⟨final, state, stable, completed⟩ := partialLaw stopped
    (by simpa only [or_false] using supported)
  have ends := model.mem_support_runBehavioralUntil certificate players
    (LateStopped setup leaks bounds horizon scheduler rank) start stopped supported
  have done : event ∈ final.execution.application.config.cut.completed := by
    by_contra pending
    rcases ends with ⟨other, otherState, prefixed⟩ | ended
    · rw [state] at otherState
      cases Option.some.inj otherState
      rw [stable pending] at prefixed
      exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
    · rw [state] at ended
      have rawTrace := state ▸ menu.toRawTrace (initialLaw setup) horizon scheduler stopped.trace
      have terminal := completes final rawTrace ended
      exact pending (by rw [terminal]; exact Finset.mem_univ _)
  obtain ⟨action, stepMember, succeeded⟩ := completed done
  exact ⟨final, action, state, stepMember, succeeded⟩

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A publication's failure read at its own type is a failure. -/
private theorem isFailure_cast_publication {kind : EventGraph.EventField Player L}
    {payload : L.Ty} (kindEq : kind = .publication payload) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm)
      (PublicationResult.failure : PublicationResult (L.Val payload))) := by
  subst kindEq
  rfl

omit [Fintype Player] in
/-- **A successful resolution discloses.** A resolve event completed from a
configuration with a successful output was completed by the disclosing
action. -/
theorem disclose_of_outputSucceeded {before after : (graph setup).Config}
    {event : (graph setup).EventId} {ready : before.cut.Ready event}
    {action : (graph setup).Action event} {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (member : after ∈ (before.step event ready action).support)
    (succeeded : OutputSucceeded after.store event) :
    (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) = true := by
  have reach : ConfigReaches setup before after :=
    Relation.ReflTransGen.single (Or.inr ⟨event, ready, action, member⟩)
  have completion : (⟨event, action⟩ : (graph setup).Completion) ∈ after.history := by
    rw [before.step_history event ready action after member]
    exact List.mem_append_right _ (List.mem_singleton.mpr rfl)
  have output := reach.resolve_output (outputEq := outputEq) (codeEq := codeEq) completion ready.1
  cases disclose : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) with
  | true => rfl
  | false =>
      exfalso
      rw [disclose] at output
      obtain ⟨stored, storedEq, notFailed⟩ := succeeded
      rw [EventGraph.Config.store_output, output] at storedEq
      unfold EventGraph.EventCode.resolveOutput? at storedEq
      simp only [Bool.false_eq_true, ↓reduceIte, ite_self] at storedEq
      obtain ⟨result, resultEq, rfl⟩ := Option.map_eq_some_iff.mp storedEq
      have failure : result = .failure := by
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
          Option.some.injEq] at resultEq
        obtain ⟨_, _, _, _, chosen⟩ := resultEq
        exact chosen.symm
      subst failure
      exact notFailed (isFailure_cast_publication outputEq)

/-- **Disclosing at the first activation.** Under the asynchronous contract
and the timeliness margin, let who be at its first activation for the resolve
event, at a history whose configuration is a prefix of rank events decoding to
a point of the intended game. Let the canonical decision of action transmit,
and let the source action action decodes to be intended at the decoded point.
Then, with that decision committed at the history's information state and any
other policies, until the event completes, the completion-point law is the
source step of that source action at the decoded point, with success one and no
error, for every property fresh of controls implied by the event not having
failed. -/
theorem firstActivation_disclose_completionPointLaw
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (profile : ∀ player, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    (info : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).InfoState
      who)
    (observed : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      info)
    (selected : choice.1 = some ((runtime setup).canonicalServiceDecision leaks who
      (execution.recall who) (execution.observe (application setup leaks) who) event action))
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {sourceAction : OwnAction Player L}
    (decodes : decodeEventAction setup.program event action = some sourceAction)
    (intendedAction : sourceAction ∈ ProtocolView.intendedAvailable who setup.program
      (ProtocolState.observe who setup.program point))
    {fresh : (application setup leaks).Control → Prop}
    (freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store event →
      fresh control) :
    CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).behavioralSignature) profile who ((profile who).commit info choice))
      rank fresh history 1 (ProtocolState.step setup.program point (fun _ => some sourceAction))
      0 := by
  classical
  subst observed
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have rankEq := (ready_iff_rank setup _ rank ordered event).mp ready
  -- An intended action discloses.
  have disclosing : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) =
      true := by
    cases disclose : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool) with
    | true => rfl
    | false =>
        exfalso
        have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
            false := by
          rw [← disclose]
          simp only [cast_cast, cast_eq]
        have failing : Failing (decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)) :=
          decodeEventAction_failing_publication setup.program event.val event.isLt outputEq
        rw [← actionEq, decodes] at failing
        exact ProtocolView.not_failing_of_intendedAvailable who setup.program _ sourceAction
          intendedAction failing
  -- The source step at the decoded point.
  obtain ⟨found, ⟨residual⟩⟩ := protocol_sourceResidual (failureProfile setup.program) menu
    horizon scheduler trace _ rfl
  have sameRank := isPrefix_unique residual.checkpoint.ordered ordered
  subst sameRank
  have pointDecoded : decodedPoint setup execution.application.config = some point :=
    (decodedPoint_eq_of_isPrefix ordered).trans decoded
  have acts : ∀ player, ProtocolView.actor player setup.program
      (ProtocolState.observe player setup.program point) = some who := fun player =>
    (decodedPoint_actor player ready pointDecoded).trans owned
  obtain ⟨target, stepEq⟩ := ProtocolState.step_eq_pure_of_actor who who setup.program point
    (fun _ => some sourceAction) (acts who)
  have targetIntended : ProtocolState.Intended setup.program target := by
    refine ProtocolState.intended_step_of_actors setup.program point _ target intendedPoint
      (fun player active => ?_) (by rw [stepEq]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
    cases (acts player).symm.trans active
    exact ⟨sourceAction, rfl, intendedAction⟩
  -- Every stop completes the event at the target point.
  have notStopped : ¬ LateStopped setup leaks bounds horizon scheduler found history := by
    rintro ⟨control, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self found (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have bindSuccess : ∀ owner payload' outputEq' codeEq',
      nodeView (graph setup) event = .bind owner payload' outputEq' codeEq' →
        ∃ value', (cast (congrArg EventGraph.EventField.Action outputEq') action :
          PublicationResult (L.Val payload')) = .success value' := by
    intro owner payload' outputEq' codeEq' node'
    rw [node] at node'
    cases node'
  have pointAt : ∀ stop ∈ (model.runBehavioralUntil certificate
      (Profile.update (sig := model.behavioralSignature) profile who
        ((profile who).commit (model.infoOf who history.trace) choice))
      (LateStopped setup leaks bounds horizon scheduler found) history).support,
      completionPoint setup leaks bounds horizon scheduler found fresh stop = some target := by
    intro stop member
    rw [model.runBehavioralUntil_of_running certificate _ notStopped running,
      PMF.mem_support_bind_iff] at member
    obtain ⟨next, stepped, reached⟩ := member
    have nextState : next.state = some ⟨remaining, none, execution.respond
        (application setup leaks) who ((runtime setup).canonicalServiceDecision leaks who
          (execution.recall who) (execution.observe (application setup leaks) who) event
          action)⟩ := by
      have committedStep := menu.run_commit_response (initialLaw setup) horizon scheduler profile
        history who remaining execution current choice _ selected
      have inLaw : next.state ∈ (PMF.pure (α := (application setup leaks).ProtocolState)
          (some ⟨remaining, none, execution.respond (application setup leaks) who
            ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
              (execution.observe (application setup leaks) who) event action)⟩)).support := by
        rw [← committedStep, PMF.support_map]
        exact ⟨next, by convert stepped, rfl⟩
      exact (PMF.mem_support_pure_iff _ _).mp inLaw
    have afterTrace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution.respond (application setup leaks) who
          ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event action)⟩) :=
      nextState ▸ next.trace
    have invariant := acceptanceInvariant_respond bounds horizon scheduler trace event turn
      action material submits bindSuccess afterTrace
    obtain ⟨final, completedAction, state, completedMember, succeeded⟩ :=
      accepted_stop_config contract.completes certificate _ ready ordered
      (fun control later records done =>
        (firstActivation_canonical_settles bounds contract timely trace event turn never action
          material submits later records).2 done)
      next nextState invariant
      ((runtime setup).reactive_respond_application leaks execution who _).1 stop reached
    have completedDiscloses := disclose_of_outputSucceeded (outputEq := outputEq) codeEq
      completedMember succeeded
    have sameAction : completedAction = action :=
      (cast_inj _).mp (completedDiscloses.trans disclosing.symm)
    rw [sameAction] at completedMember
    have stepMember := completedMember
    obtain ⟨before, after, beforeDecoded, afterDecoded, reachedPoint⟩ :=
      decodedPoint_step residual event ready action _ stepMember
    rw [pointDecoded] at beforeDecoded
    cases Option.some.inj beforeDecoded
    rw [decodes, stepEq, PMF.mem_support_pure_iff] at reachedPoint
    subst reachedPoint
    have prefixed : final.execution.application.config.cut.IsPrefix (found + 1) := by
      rw [execution.application.config.step_cut event ready action _ stepMember]
      exact ordered.complete_at event ready rankEq
    have prefixDecoded : sourceServicePrefix? setup (found + 1)
        final.execution.application.config = some after :=
      (decodedPoint_eq_of_isPrefix prefixed).symm.trans afterDecoded
    have good : ProtocolState.Intended setup.program after ∧ fresh final :=
      ⟨targetIntended, freshOf final (not_storeEventFailed_of_outputSucceeded succeeded)⟩
    unfold completionPoint
    rw [state]
    dsimp only
    rw [ite_eq_left prefixed .., prefixDecoded]
    dsimp only
    rw [ite_eq_left good ..]
  intro value bound _
  rw [expect_congr_on_support (g := fun _ => value target) fun stop member => by
      rw [pointAt stop member]
      rfl,
    expect_constant, stepEq, expect_pure, one_mul, sub_self, abs_zero, zero_mul]

/-- **The prescribed component at a disclosure first activation.** Under the
asynchronous contract, the timeliness margin and retention of covered canonical
packets, let who be at its first activation for the resolve event pending at a
history, whose configuration is a prefix of rank events decoding to a point of
the intended game, and let the canonical decision of every successful encoded
source action transmit there. Installing at the history's information state the
slot-trembled prescribed component of an intended assessment source, with any
other policies, until the event completes, the completion-point law is the step
of the intended effective opening of source at the decoded point, with success
one and error six times the scale, for every property fresh of controls implied
by the event not having failed. -/
theorem firstActivation_prescribed_disclose_completionPointLaw
    [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).InfoState who)]
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (retains : RetainsCoveredCanonical setup leaks bounds horizon scheduler bound)
    (source : setup.intendedModel.BehavioralAssessment) {scale : ℝ} (nonnegative : 0 ≤ scale)
    (le_one : scale ≤ 1)
    (profile : ∀ player, (onePacketModel setup leaks bounds (initialLaw setup) horizon
      scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph setup).EventId)
    (pending : pendingEvent setup leaks who (some (execution.recall who,
      execution.observe (application setup leaks) who)) = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding who payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    {outputEq : (graph setup).outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve who payload binding checks}
    (node : nodeView (graph setup) event = .resolve who payload binding checks outputEq codeEq)
    (transmits : CanonicalTransmitsAt setup leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event)
    {rank : Nat} (ordered : execution.application.config.cut.IsPrefix rank)
    {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank execution.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    {fresh : (application setup leaks).Control → Prop}
    (freshOf : ∀ control, ¬ StoreEventFailed control.execution.application.config.store event →
      fresh control)
    (info : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).InfoState
      who)
    (observed : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
      history.trace = info) :
    CompletionPointLaw setup leaks bounds horizon scheduler
      (Profile.update (sig := (onePacketModel setup leaks bounds (initialLaw setup) horizon
        scheduler).behavioralSignature) profile who ((profile who).withLaw info
          (slotPrescribedComponent setup leaks bounds (initialLaw setup) horizon scheduler source
            scale nonnegative le_one who info)))
      rank fresh history 1
      (ProtocolState.behavioralStateStep setup.program
        (setup.intendedOpeningProfile source.strategy) point)
      (6 * scale) := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  have infoEq : model.infoOf who history.trace =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
    change (menu.signals (initialLaw setup) horizon scheduler).infoOf who history.trace = _
    rw [menu.info, current]
    simp [ReactiveApplication.observe]
  have atSite := observed.symm.trans infoEq
  subst atSite
  obtain ⟨turn, readyView, _, unrecorded⟩ := pendingEvent_spec pending
  have turnExecution : execution.application.publicView.ownTurn? who = some event := turn
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have fits := firstActivation_inclusionFits contract timely
    (menu.toRawTrace (initialLaw setup) horizon scheduler trace) rfl event turnExecution never
  have ready := (execution.application.publicView_eventReady event).mp readyView
  rw [← asIfHonest_bind_step_eq_behavioralStateStep source who execution ordered decoded
    intendedPoint turnExecution (execution.recall who)]
  have notStopped : ¬ LateStopped setup leaks bounds horizon scheduler rank history := by
    rintro ⟨control, state, prefixed⟩
    rw [current] at state
    cases Option.some.inj state
    exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
  have running : ¬ (menu.protocol (initialLaw setup) horizon scheduler).terminal
      history.state := by
    rw [current]
    rintro ⟨_, impossible⟩
    cases impossible
  have active : (menu.protocol (initialLaw setup) horizon scheduler).active history.state who := by
    rw [current]
    rfl
  have actsOnce := (menu.decisionRecall (initialLaw setup) horizon scheduler).actsOnceWhereItMatters
  intro value valueBound valueBounded
  have boundNonneg : 0 ≤ valueBound := (abs_nonneg _).trans (valueBounded point)
  have pointBounded : ∀ stop, |(completionPoint setup leaks bounds horizon scheduler rank fresh
      stop).elim 0 value| ≤ valueBound := by
    intro stop
    cases completionPoint setup leaks bounds horizon scheduler rank fresh stop with
    | none => simpa using boundNonneg
    | some target => exact valueBounded target
  rw [model.runBehavioralUntil_update_withLaw_eq_bind certificate actsOnce profile who
      (profile who) _ _ _ history observed notStopped running active,
    expect_bind_tower_bounded _ _ _ pointBounded, one_mul]
  have stepBounded : |expect ((asIfHonestProfile setup leaks source who
      (some (execution.recall who, execution.observe (application setup leaks) who))).bind
        fun choice => ProtocolState.step setup.program point (fun _ => choice)) value| ≤
      valueBound := expect_abs_le_of_bounded boundNonneg valueBounded
  refine abs_expect_slotTrembledChoice_sub_le nonnegative le_one who _ _ _ _ _
    (fun choice => expect_abs_le_of_bounded boundNonneg pointBounded) stepBounded ?_
  -- The as-if-honest choices complete at the source step committing them.
  change expect ((honestResponse setup leaks source who (execution.recall who)
    (execution.observe (application setup leaks) who)).map (responseChoice setup leaks bounds
      (initialLaw setup) horizon scheduler who (some (execution.recall who,
        execution.observe (application setup leaks) who)))) _ = _
  unfold honestResponse
  rw [turn]
  dsimp only
  rw [PMF.map_comp, expect_map, expect_bind_tower_bounded _ _ _ valueBounded]
  refine expect_congr_on_support fun choice member => ?_
  have encodes := asIfHonestProfile_encodes source who execution rank ordered point decoded
    (execution.recall who) event turnExecution choice member
  rcases choice with _ | action
  · simp at encodes
  cases encoded : encodeEventAction? setup.program event action with
  | none => simp [encoded] at encodes
  | some graphAction =>
      have success := asIfHonestProfile_success source who execution rank ordered point decoded
        (execution.recall who) action member
      have sends := transmits action graphAction encoded success.1 success.2
      obtain ⟨material, submits⟩ := Option.ne_none_iff_exists'.mp sends
      have effective : EffectiveDecision event graphAction := by
        unfold EffectiveDecision
        rw [node]
        trivial
      have offered := canonical_mem_onePacket_of_pending bounds trace who event turnExecution
        unrecorded graphAction
        (retains trace who event graphAction turnExecution unrecorded fits effective sends)
      have selected : (responseChoice setup leaks bounds (initialLaw setup) horizon scheduler who
          (some (execution.recall who, execution.observe (application setup leaks) who))
          ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event graphAction)).1 =
          some ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event graphAction) := by
        unfold responseChoice
        simp only [offered, ↓reduceDIte]
      obtain ⟨intended, _, same⟩ := (mem_support_asIfHonestProfile_observe setup leaks source who
        execution rank ordered point decoded (execution.recall who) _).mp member
      have legal := intended.2
      change ProtocolView.intendedMenu who setup.program
        (ProtocolState.observe who setup.program point) intended.1 at legal
      rw [same] at legal
      have law := firstActivation_disclose_completionPointLaw contract timely profile history
        current event turnExecution never node graphAction material submits _ observed _
        selected
        ordered decoded intendedPoint
        (decodeEventAction_encodeEventAction?_eq_some setup.program event action graphAction
          encoded) legal.2 freshOf value valueBound valueBounded
      rw [zero_mul, one_mul] at law
      simp only [Function.comp_apply, Option.bind_some, encoded]
      exact sub_eq_zero.mp (abs_nonpos_iff.mp law)

end Vegas
