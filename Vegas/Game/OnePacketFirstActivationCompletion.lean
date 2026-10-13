/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketCompletionLaw
import Vegas.Game.OnePacketEventSuccess
import Vegas.Game.OnePacketDecodedActor
import Vegas.Game.OnePacketIntendedProjection
import Vegas.Pending.ReactiveBindingReceipts
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound

/-! # The completion point after committing at the first activation

**A step with an actor is deterministic.** At a source point where some player
acts, the source step is a point mass
(`Vegas.SourceProgram.ProtocolState.step_eq_pure_of_actor`).

**The stop after a commitment.** Let `who` have sent, from a configuration at
which the binding event of rank `rank` is ready, a packet committing to a handle
whose meaning is a successful value, with the acceptance invariant holding and
the packet settling once the event completes. Under play of any profile until
that event completes, under a scheduler completing play, every stop completes
the event from the sending configuration by the action binding that value, and
the event's output is a success (`Vegas.committed_stop_config`).

**Committing at the first activation.** Under the asynchronous contract and the
timeliness margin, at a first activation of `who` for a binding of rank `rank`
whose configuration decodes at `rank` to a point of the intended game, the
canonical decision committing an intended successful value has, under play of
any other policies until the event completes, the completion-point law of the
source step committing that value: success one and no error
(`Vegas.firstActivation_commit_completionPointLaw`).
-/

noncomputable section

namespace Vegas.SourceProgram.ProtocolState

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- **A step with an actor is deterministic.** At a source point where some
player acts, every joint choice steps to a single point. -/
theorem step_eq_pure_of_actor (who owner : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (state : ProtocolState program) → (joint : Player → Option (OwnAction Player L)) →
    ProtocolView.actor who program (observe who program state) = some owner →
    ∃ target, step program state joint = PMF.pure target
  | _, _, .ret _, _, _, acts => by
      simp [ProtocolView.actor] at acts
  | _, _, .sample _ _ _ next, state, joint, acts => by
      cases state with
      | inl config => simp [observe, ProtocolView.actor] at acts
      | inr rest =>
          obtain ⟨target, stepEq⟩ := step_eq_pure_of_actor who owner next rest joint acts
          exact ⟨Sum.inr target, by simp only [step, Sum.elim_inr, stepEq, PMF.pure_map]⟩
  | _, _, .commit _ _ _ _ next, state, joint, acts => by
      cases state with
      | inl config => exact ⟨_, rfl⟩
      | inr rest =>
          obtain ⟨target, stepEq⟩ := step_eq_pure_of_actor who owner next rest joint acts
          exact ⟨Sum.inr target, by simp only [step, Sum.elim_inr, stepEq, PMF.pure_map]⟩
  | _, _, .reveal _ _ _ _ _ _ next, state, joint, acts => by
      cases state with
      | inl config => exact ⟨_, rfl⟩
      | inr rest =>
          obtain ⟨target, stepEq⟩ := step_eq_pure_of_actor who owner next rest joint acts
          exact ⟨Sum.inr target, by simp only [step, Sum.elim_inr, stepEq, PMF.pure_map]⟩

end Vegas.SourceProgram.ProtocolState

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

omit [Fintype Player] in
/-- At a completed prefix, the decoded point is the readout at that prefix. -/
private theorem decodedPoint_eq_of_isPrefix {config : (graph setup).Config} {rank : Nat}
    (ordered : config.cut.IsPrefix rank) :
    decodedPoint setup config = sourceServicePrefix? setup rank config := by
  have exists_ordered : ∃ rank, config.cut.IsPrefix rank := ⟨rank, ordered⟩
  unfold decodedPoint
  rw [dite_eq_left_of_eq_true (eq_true exists_ordered), show exists_ordered.choose = rank from
    isPrefix_unique exists_ordered.choose_spec ordered]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- A binding output read at its own type is not a failure exactly when its
result is not a failure. -/
private theorem isFailure_cast {kind : EventGraph.EventField Player L} {owner : Player}
    {payload : L.Ty} (kindEq : kind = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    kind.IsFailure (cast (congrArg EventGraph.EventField.Value kindEq.symm) result) ↔
      result = .failure := by
  subst kindEq
  rfl

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
/-- Reading a stored binding output at its own type recovers its result. -/
private theorem get_cast {kind : EventGraph.EventField Player L} {owner : Player}
    {payload : L.Ty} (kindEq : kind = .binding owner payload)
    (result : PublicationResult (L.Val payload)) :
    cast (congrArg (fun field : EventGraph.EventField Player L => Option field.Value) kindEq)
      (some (cast (congrArg EventGraph.EventField.Value kindEq.symm) result)) = some result := by
  subst kindEq
  rfl

variable (setup leaks bounds horizon scheduler) in
/-- After a recorded commitment of `candidate` sent for `event` from `sent`:
the acceptance invariant, the meaning of `candidate` fixed at `raw`, and, once
the event has completed, the configuration is one step of the event from
`sent`. -/
private def CommitInvariant (who : Player) (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event)
    (candidate : Handle (graph setup)) (raw : Raw L) :
    (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event sent
          (some control) ∧
        control.execution.application.candidates.lookup candidate = .openable raw ∧
        (event ∈ control.execution.application.config.cut.completed →
          ∃ action, control.execution.application.config ∈
            (sent.step event ready action).support)

/-- The commitment invariant passes along every transition from a state where
the event of rank `rank` has not completed. -/
private theorem commitInvariant_transition {who : Player}
    {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} {ready : sent.cut.Ready event}
    {candidate : Handle (graph setup)} {raw : Raw L} {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) (before after : (application setup leaks).ProtocolState)
    (going : ∀ control, before = some control →
      ¬ control.execution.application.config.cut.IsPrefix (rank + 1))
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : CommitInvariant setup leaks bounds horizon scheduler who entry message event sent
      ready candidate raw before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    CommitInvariant setup leaks bounds horizon scheduler who entry message event sent ready
      candidate raw after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨invariant, fixed, completion⟩ := holds
      have afterInvariant := acceptanceInvariant_transition bounds horizon scheduler who entry
        message event sent (some control) after joint legal invariant reached
      cases after with
      | none => exact afterInvariant.elim
      | some next =>
          have kept := (keepsFixedCandidates_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          refine ⟨afterInvariant, ?_, fun completedNext => ?_⟩
          · rw [kept candidate (by rw [fixed]; exact fun impossible => by cases impossible), fixed]
          · have pending : event ∉ control.execution.application.config.cut.completed := by
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

/-- **The stop after a commitment.** Let `who` have sent `message`, recorded by
`entry`, from the configuration `sent` at which the binding `event` of rank
`rank` is ready, committing to `candidate` whose meaning is the successful
value `value` of the binding. Suppose the acceptance invariant holds at a
history at `sent`, and the packet has an accepting receipt at every later
history recording it at which the event has completed. Then, under a scheduler
completing play, every stop of play of any profile until the event completes
completes the event from `sent` by `action`, the action binding `value`, and
the event's output is a success. -/
theorem committed_stop_config
    (completes : CompletesPlay (runtime setup) leaks (initialLaw setup) horizon scheduler)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    {who : Player} {entry : (application setup leaks).PlayerEntry}
    {message : Message Player (WitnessedPacket (graph setup))} {event : (graph setup).EventId}
    {sent : (graph setup).Config} (ready : sent.cut.Ready event) {rank : Nat}
    (ordered : sent.cut.IsPrefix rank) {owner : Player} {payload : L.Ty}
    {outputEq : (graph setup).outputLayout event = .binding owner payload}
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    {candidate : Handle (graph setup)} (call : message.payload.call = .commitment event candidate)
    {value : L.Val payload} (action : (graph setup).Action event)
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
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
    (atSent : control.execution.application.config = sent)
    (fixed : control.execution.application.candidates.lookup candidate =
      .openable ⟨payload, value⟩) :
    ∀ stop ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralUntil certificate players
        (LateStopped setup leaks bounds horizon scheduler rank) start).support,
      ∃ final, stop.state = some final ∧
        final.execution.application.config ∈ (sent.step event ready action).support ∧
        OutputSucceeded final.execution.application.config.store event := by
  intro stop member
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  have holds : CommitInvariant setup leaks bounds horizon scheduler who entry message event sent
      ready candidate ⟨payload, value⟩ start.state := by
    rw [current]
    refine ⟨invariant, fixed, fun done => ?_⟩
    rw [atSent] at done
    exact (ready.1 done).elim
  have reachedInvariant := model.runBehavioralUntil_support_closed_of_going certificate players
    (LateStopped setup leaks bounds horizon scheduler rank)
    (CommitInvariant setup leaks bounds horizon scheduler who entry message event sent ready
      candidate ⟨payload, value⟩)
    (fun history going _ joint legal target holds reached =>
      commitInvariant_transition ordered history.state target
        (fun control state prefixed => going ⟨control, state, prefixed⟩) joint legal holds
        reached)
    start holds stop member
  have ends := model.mem_support_runBehavioralUntil certificate players _ start stop member
  cases state : stop.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some final =>
      rw [state] at reachedInvariant
      obtain ⟨finalInvariant, finalFixed, completion⟩ := reachedInvariant
      obtain ⟨⟨finalTrace⟩, records, emitted, _, _, stable, settled⟩ := finalInvariant
      have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some final) :=
        menu.toRawTrace (initialLaw setup) horizon scheduler finalTrace
      have done : event ∈ final.execution.application.config.cut.completed := by
        by_contra pending
        have same := stable pending
        rcases ends with ⟨other, otherState, prefixed⟩ | ended
        · rw [state] at otherState
          cases Option.some.inj otherState
          rw [same] at prefixed
          exact Nat.succ_ne_self rank (isPrefix_unique prefixed ordered)
        · rw [state] at ended
          have terminal := completes final rawTrace ended
          exact pending (by rw [terminal]; exact Finset.mem_univ _)
      obtain ⟨found, stepMember⟩ := completion done
      have receipt := settles final finalTrace records done
      have succeeded := settled receipt
      refine ⟨final, rfl, ?_, succeeded⟩
      -- The completion's action binds the committed value.
      have facts := legalFacts setup leaks horizon scheduler final rawTrace
      have initialized : initialLaw setup =
          (setup.initialLaw.map setup.eventInputs).map (State.initial (graph := graph setup)) := by
        simp only [initialLaw, serviceInitialLaw, PMF.map_comp, Function.comp_def]
      have bindingTrace := rawTrace
      rw [initialized] at bindingTrace
      have recorded := (runtime setup).bindingReceipts_history leaks
        (setup.initialLaw.map setup.eventInputs) horizon scheduler final bindingTrace
      obtain ⟨published, onLedger, identified, selected⟩ := recorded message.id receipt
      obtain ⟨earlier, later, split⟩ := records
      have output : message ∈ (application setup leaks).outputs
          (final.execution.recall who) := by
        rw [split]
        exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
      rw [← facts.inputs who] at output
      have input := (List.mem_filter.mp output).1
      have samePublished := (facts.unique.inputs message input).ledger published onLedger
        identified
      subst samePublished
      have acceptedEq := selected event candidate call
      have outputs := step_binding_output (outputEq := outputEq) (codeEq := codeEq) stepMember
      generalize resultEq : (cast (congrArg EventGraph.EventField.Action outputEq) found :
        PublicationResult (L.Val payload)) = result at outputs
      cases result with
      | failure =>
          exfalso
          obtain ⟨stored, storedEq, notFailed⟩ := succeeded
          rw [EventGraph.Config.store_output, outputs] at storedEq
          cases Option.some.inj storedEq
          exact notFailed ((isFailure_cast outputEq _).mpr rfl)
      | success read =>
          have reads : (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (graph setup).layout
              (.binding owner payload)).get? final.execution.application.config.store =
              some (.success read) := by
            change cast _ (final.execution.application.config.outputs event) = _
            rw [outputs]
            exact get_cast outputEq _
          obtain ⟨handle', acceptedHandle, _, meaning⟩ :=
            facts.binding.success_provenance _ read reads
          have handleEq : handle' = candidate :=
            Option.some.inj (acceptedHandle.symm.trans acceptedEq)
          subst handleEq
          rw [finalFixed] at meaning
          injection meaning with rawEq
          injection rawEq with _ valueEq
          subst valueEq
          have actionEq : found = action :=
            (cast_inj _).mp (resultEq.trans successful.symm)
          rw [← actionEq]
          exact stepMember

omit [Fintype Player] in
/-- The canonical decision committing a successful value at a binding of `who`
sends a commitment to a handle whose meaning, right after the response, is that
value. -/
private theorem canonical_commitment_sent {who : Player}
    {execution : (application setup leaks).Execution} {event : (graph setup).EventId}
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (action : (graph setup).Action event) {value : L.Val payload}
    (successful : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = .success value)
    (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material) :
    ∃ candidate, (sentEnvelope setup leaks execution who material).payload.call =
        .commitment event candidate ∧
      (execution.respond (application setup leaks) who
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event
            action)).application.candidates.lookup candidate = .openable ⟨payload, value⟩ := by
  have respondApplication : (execution.respond (application setup leaks) who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)).application =
      (application setup leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [submits]
  rw [respondApplication]
  obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
      action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
    ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
  simp only [cast_cast, cast_eq] at successful
  subst successful
  generalize hview : execution.observe (application setup leaks) who = view at submits
  cases selected : canonicalFreshSlot who view.application with
  | none =>
      simp only [EventGraphRuntime.canonicalServiceDecision,
        EventGraphRuntime.canonicalReactiveDecision, node, selected, Option.map_none,
        ReactiveApplication.SubmissionNormalization.action] at submits
      cases submits
  | some serial =>
      have fresh := canonicalFreshSlot_spec who _ serial selected
      rw [← hview] at fresh selected
      rw [← hview] at submits
      rw [(runtime setup).canonicalServiceDecision_binding leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event payload outputEq codeEq node
        serial selected (.success value)] at submits
      cases Option.some.inj submits
      have freshLookup : execution.application.candidates.lookup
          (who, .prepared serial) = .fresh := fresh
      refine ⟨(who, .prepared serial), rfl, ?_⟩
      change (submitStep (Submission.register
        ⟨.commitment event (who, .prepared serial), some ⟨payload, value⟩⟩
        execution.application who) who
        (.commitment event (who, .prepared serial))).candidates.lookup
          (who, .prepared serial) = _
      simp [submitStep, Submission.register, freshLookup,
        CommitmentCandidates.lookup_freeze_self, CommitmentCandidates.lookup_prepare_self]

/-- **Committing at the first activation.** Under the asynchronous contract and
the timeliness margin, let `who` be at its first activation for the binding
`event`, at a history whose configuration is a prefix of `rank` events decoding
to a point of the intended game. Let the canonical decision of `action`
transmit, and let the source action `action` decodes to be intended at the
decoded point. Then, with that decision committed
at the history's information state and any other policies, until the event
completes, the completion-point law is the source step of that source action at
the decoded point, with success one and no error, for every property `fresh`
of controls implied by the event not having failed. -/
theorem firstActivation_commit_completionPointLaw
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
    {payload : L.Ty} {outputEq : (graph setup).outputLayout event = .binding who payload}
    {codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind who payload}
    (node : nodeView (graph setup) event = .bind who payload outputEq codeEq)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    (choice : (onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).Choice who
      ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
        history.trace))
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
        scheduler).behavioralSignature) profile who ((profile who).commit
          ((onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler).infoOf who
            history.trace) choice))
      rank fresh history 1 (ProtocolState.step setup.program point (fun _ => some sourceAction))
      0 := by
  classical
  let menu := bounds.onePacketMenu (runtime setup) leaks
  let model := menu.information (initialLaw setup) horizon scheduler
  let certificate := (menu.bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
  have trace : (menu.protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp
    (PublicView.ownTurn?_spec _ who event turn).1
  have rankEq := (ready_iff_rank setup _ rank ordered event).mp ready
  -- An intended action binds a successful value.
  obtain ⟨value, successful⟩ : ∃ value : L.Val payload,
      (cast (congrArg EventGraph.EventField.Action outputEq) action :
        PublicationResult (L.Val payload)) = .success value := by
    generalize resultEq : (cast (congrArg EventGraph.EventField.Action outputEq) action :
      PublicationResult (L.Val payload)) = result
    cases result with
    | success value => exact ⟨value, rfl⟩
    | failure =>
        exfalso
        have actionEq : action = cast (congrArg EventGraph.EventField.Action outputEq.symm)
            (PublicationResult.failure : PublicationResult (L.Val payload)) := by
          rw [← resultEq]
          simp only [cast_cast, cast_eq]
        have failing : Failing (decodeEventAction setup.program event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm)
              (PublicationResult.failure : PublicationResult (L.Val payload)))) :=
          decodeEventAction_failing_binding setup.program event.val event.isLt outputEq
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
    exact ⟨value, successful⟩
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
    obtain ⟨candidate, call, fixed⟩ :=
      canonical_commitment_sent node action successful material submits
    have invariant := acceptanceInvariant_respond bounds horizon scheduler trace event turn
      action material submits bindSuccess afterTrace
    obtain ⟨final, state, stepMember, succeeded⟩ := committed_stop_config contract.completes
      certificate _ ready ordered (outputEq := outputEq) codeEq call action successful
      (fun control later records done =>
        (firstActivation_canonical_settles bounds contract timely trace event turn never action
          material submits later records).2 done)
      next nextState invariant
      ((runtime setup).reactive_respond_application leaks execution who _).1 fixed stop reached
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

end Vegas
