/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketFirstActivation
import Vegas.Game.OnePacketEventFailure

/-! # An accepted canonical packet completes its event successfully

A packet's acceptance is certified to succeed when its call commits to a handle
whose meaning is openable at the bound type, or opens a resolution whose
evaluation on a fixed configuration publishes a success
(`Vegas.AcceptanceWitness`). Fixed meanings stay fixed, so the witness
persists.

After `who` sends the canonical decision of a successful source action at its
turn, the following hold at every later history of the one-packet game, under
any responses and any scheduler (`Vegas.AcceptanceInvariant`): the response is
recorded, the witness holds, the configuration is the one the packet was sent
from while the event is unfinished (on the sequential graph nothing else can
complete), and once the packet has an accepting receipt the event's output is a
success. The invariant holds right after the send
(`Vegas.acceptanceInvariant_respond`) and persists under every transition
(`Vegas.acceptanceInvariant_transition`).

On the histories of the one-packet game, the event-level failed histories of a
player are those whose readout is an event-level failed readout
(`Vegas.EventFailedHistory`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

omit [DecidableEq Player] in
/-- A successful output is not a failure of the event in the store. -/
theorem not_storeEventFailed_of_outputSucceeded {graph : EventGraph Player L}
    {store : EventGraph.Store graph.layout} {event : graph.EventId}
    (succeeded : OutputSucceeded store event) : ¬ StoreEventFailed store event := by
  rintro ⟨value, stored, failed⟩
  obtain ⟨other, otherStored, notFailed⟩ := succeeded
  rw [stored] at otherStored
  cases Option.some.inj otherStored
  exact notFailed failed

variable (setup runtime) in
/-- **A certificate that acceptance succeeds.** The message commits to a
handle of the event whose meaning is openable at the bound type, or opens a
resolution of the event whose evaluation on the configuration `sent`
publishes a success. -/
def AcceptanceWitness (event : (graph setup).EventId)
    (message : Message Player (WitnessedPacket (graph setup))) (sent : (graph setup).Config)
    (state : EventGraphRuntime.State (graph setup)) : Prop :=
  (∃ candidate owner payload value, message.payload.call = .commitment event candidate ∧
    (graph setup).layout (.inr event) = .binding owner payload ∧
    state.candidates.lookup candidate = .openable ⟨payload, value⟩) ∨
  (∃ candidate raw owner payload binding checks outputEq codeEq value,
    message.payload.call = .opening event candidate raw ∧
    nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq ∧
    EventGraph.EventCode.resolveOutput? binding checks true sent.store = some (.success value))

/-- The witness persists while fixed meanings stay fixed. -/
theorem AcceptanceWitness.keep {event : (graph setup).EventId}
    {message : Message Player (WitnessedPacket (graph setup))} {sent : (graph setup).Config}
    {before after : EventGraphRuntime.State (graph setup)}
    (witness : AcceptanceWitness setup event message sent before)
    (kept : KeepsFixedCandidates before after) :
    AcceptanceWitness setup event message sent after := by
  rcases witness with ⟨candidate, owner, payload, value, call, layout, fixed⟩ | opening
  · refine Or.inl ⟨candidate, owner, payload, value, call, layout, ?_⟩
    rw [kept candidate (by rw [fixed]; exact fun impossible => by cases impossible), fixed]
  · exact Or.inr opening

/-- **A certified acceptance succeeds.** If the contract accepts the message at
a state with the sending configuration, the event's output is a success. -/
theorem AcceptanceWitness.output_success {event : (graph setup).EventId}
    {message : Message Player (WitnessedPacket (graph setup))} {sent : (graph setup).Config}
    {state next : EventGraphRuntime.State (graph setup)}
    (witness : AcceptanceWitness setup event message sent state)
    (sameConfig : state.config = sent) (valid : state.BindingInvariant)
    (accepted : handle runtime state ⟨message.id, message.payload.call⟩ = some next) :
    OutputSucceeded next.config.store event := by
  rcases witness with ⟨candidate, owner, payload, value, call, layout, fixed⟩ |
    ⟨candidate, raw, owner, payload, binding, checks, outputEq, codeEq, value, call, node,
      resolved⟩
  · rw [call] at accepted
    exact handle_commitment_output_success runtime state next message.id event
      candidate accepted valid owner payload layout value fixed
  · rw [call] at accepted
    rw [← sameConfig] at resolved
    exact handle_opening_output_success runtime state next message.id event candidate
      raw accepted owner payload binding checks outputEq codeEq node value resolved

section Invariant

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (horizon : Nat) (scheduler : (application setup runtime leaks).Scheduler)

variable (setup runtime leaks) in
/-- **The acceptance invariant** after a recorded send of `message` for
`event` from the configuration `sent`. -/
def AcceptanceInvariant (who : Player) (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) : (application setup runtime leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup runtime leaks who entry (some control) ∧
      entry.emitted = some message ∧
      sent.cut.Ready event ∧
      AcceptanceWitness setup event message sent control.execution.application ∧
      (event ∉ control.execution.application.config.cut.completed →
        control.execution.application.config = sent) ∧
      ((message.id, true) ∈ control.execution.receipts →
        OutputSucceeded control.execution.application.config.store event)

/-- **The acceptance invariant persists** under every transition of the
one-packet game. -/
theorem acceptanceInvariant_transition (who : Player)
    (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (before after : (application setup runtime leaks).ProtocolState)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry message
      event
      sent before)
    (reached : after ∈ (((bounds.onePacketMenu runtime leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    AcceptanceInvariant setup runtime leaks bounds horizon scheduler who entry message event sent
      after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sentReady, witness, stable, settled⟩ := holds
      have afterRecords := recordsEntry_transition (runtime := runtime) who entry (initialLaw
        setup) horizon scheduler
        _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu runtime leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step runtime leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have keptStore := (keepsStore_step runtime leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have configStep := transition_configStep (initialLaw setup) horizon
            scheduler control
            next joint reached
          refine ⟨⟨nextTrace⟩, afterRecords, emitted, sentReady, witness.keep kept, ?_, ?_⟩
          · intro unfinished
            rcases configStep with same | ⟨completedEvent, ready, action, member⟩
            · rw [same] at unfinished ⊢
              exact stable unfinished
            · have cutEq := control.execution.application.config.step_cut completedEvent ready
                action _ member
              have notBefore : event ∉ control.execution.application.config.cut.completed := by
                intro done
                apply unfinished
                rw [cutEq]
                exact Finset.mem_insert_of_mem done
              have beforeSent := stable notBefore
              rw [beforeSent] at ready
              have same := ready_unique (setup := setup) sent.cut ready sentReady
              subst same
              exact (unfinished (by rw [cutEq]; exact Finset.mem_insert_self _ _)).elim
          · intro receipt
            -- Which transition added the receipt, if any.
            rcases control with ⟨remaining, current, execution⟩
            have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
                scheduler).Trace (some ⟨remaining, current, execution⟩) :=
              (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
                scheduler trace
            have facts := legalFacts setup leaks horizon scheduler _ rawTrace
            cases current with
            | some responder =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                exact (settled receipt).mono keptStore
            | none =>
                cases remaining with
                | zero =>
                    cases (PMF.mem_support_pure_iff _ _).mp reached
                    exact settled receipt
                | succ remaining =>
                    obtain ⟨command, _, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨moved', supported, same⟩ := PMF.support_map .. ▸ moved
                    cases same
                    cases command with
                    | wait =>
                        simp only [ReactiveApplication.Execution.environmentStep,
                          PMF.pure_map] at supported
                        cases (PMF.mem_support_pure_iff _ _).mp supported
                        exact settled receipt
                    | activate activated =>
                        obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ chosen
                        exact settled receipt
                    | application command =>
                        obtain ⟨updated, chosen, rfl⟩ := PMF.support_map .. ▸ supported
                        obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ chosen
                        exact (settled receipt).mono keptStore
                    | «include» id =>
                        simp only [ReactiveApplication.Execution.environmentStep,
                          PMF.pure_map] at supported
                        cases (PMF.mem_support_pure_iff _ _).mp supported
                        change (message.id, true) ∈
                          (execution.includePending (application setup runtime leaks)
                            id).receipts at receipt
                        change OutputSucceeded
                          (execution.includePending (application setup runtime leaks)
                            id).application.config.store event
                        unfold ReactiveApplication.Execution.includePending
                          MessageNetwork.includePending at receipt ⊢
                        cases found : execution.network.lookup id with
                        | none =>
                            simp only [found] at receipt ⊢
                            exact settled receipt
                        | some envelope =>
                            simp only [found] at receipt ⊢
                            cases accepted : (application setup runtime leaks).handle
                                execution.application envelope with
                            | none =>
                                simp only [accepted, Option.getD_none] at receipt ⊢
                                rcases List.mem_append.mp receipt with old | new
                                · exact settled old
                                · simp at new
                            | some accepted' =>
                                simp only [accepted, Option.getD_some] at receipt ⊢
                                rcases List.mem_append.mp receipt with old | new
                                · exact (settled old).mono fun field value stored =>
                                    handle_store_of_some runtime _ _ _
                                      (reactiveHandle_call accepted) field value stored
                                · obtain ⟨idEq, -⟩ := Prod.mk.inj (List.mem_singleton.mp new)
                                  -- The included envelope is the message.
                                  obtain ⟨earlier, later, split⟩ := records
                                  change execution.recall who = _ at split
                                  have output : message ∈ (application setup runtime leaks).outputs
                                      (execution.recall who) := by
                                    rw [split]
                                    exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
                                  have inputRecall : execution.InputRecall
                                      (application setup runtime leaks) :=
                                    facts.inputs
                                  rw [← inputRecall who] at output
                                  have member := (List.mem_filter.mp output).1
                                  have named : envelope.id = id := by
                                    have spec := List.find?_some found
                                    simpa using spec
                                  have same : envelope = message :=
                                    (facts.unique.inputs message member).lookup id envelope found
                                      (named.trans idEq.symm)
                                  subst same
                                  have call := reactiveHandle_call accepted
                                  obtain ⟨named', eventNamed, ready, _⟩ :=
                                    handle_config_mem_step runtime _ _ _ call
                                  have eventEq : named' = event := by
                                    rcases witness with ⟨_, _, _, _, callEq, _⟩ |
                                      ⟨_, _, _, _, _, _, _, _, _, callEq, _⟩
                                    · change envelope.payload.call.event? (graph setup) =
                                        some named' at eventNamed
                                      rw [callEq] at eventNamed
                                      exact (Option.some.inj eventNamed).symm
                                    · change envelope.payload.call.event? (graph setup) =
                                        some named' at eventNamed
                                      rw [callEq] at eventNamed
                                      exact (Option.some.inj eventNamed).symm
                                  subst eventEq
                                  exact witness.output_success (stable
                                    ready.1) facts.binding call

omit [DecidableEq Player] in
private theorem exists_of_forall₂_mem {α β : Type} {relation : α → β → Prop} :
    ∀ {left : List α} {right : List β}, List.Forall₂ relation left right →
      ∀ b ∈ right, ∃ a ∈ left, relation a b
  | _, _, .nil, _, member => (List.not_mem_nil member).elim
  | _, _, .cons head tail, b, member => by
      rcases List.mem_cons.mp member with rfl | later
      · exact ⟨_, List.mem_cons_self .., head⟩
      · obtain ⟨a, inTail, related⟩ := exists_of_forall₂_mem tail b later
        exact ⟨a, List.mem_cons_of_mem _ inTail, related⟩

/-- **The invariant holds right after the send.** At a decision of `who` at its
turn `event` in the one-packet game, the canonical decision of an action that
is a successful binding value at a binding, transmitting `material`, leaves the
acceptance invariant at the state it reaches. -/
theorem acceptanceInvariant_respond {remaining : Nat} {who : Player}
    {execution : (application setup runtime leaks).Execution}
    (trace : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (action : (graph setup).Action event) (material : (application setup runtime leaks).Submission)
    (submits : (runtime.canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup runtime leaks) who) event action).transmission =
        some material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (after : ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution.respond (application setup runtime leaks)
        who
        (runtime.canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event action)⟩)) :
    AcceptanceInvariant setup runtime leaks bounds horizon scheduler who
      (respondEntry setup runtime leaks execution who (runtime.canonicalServiceDecision leaks who
        (execution.recall who) (execution.observe (application setup runtime leaks) who) event
          action))
      (sentEnvelope setup runtime leaks execution who material) event execution.application.config
      (some ⟨remaining, none, execution.respond (application setup runtime leaks) who
        (runtime.canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event action)⟩) := by
  have rawTrace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have respondApplication : (execution.respond (application setup runtime leaks) who
      (runtime.canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup runtime leaks) who) event action)).application =
      (application setup runtime leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [submits]
  have sameConfig : ((application setup runtime leaks).submit execution.application who
      material).config = execution.application.config := by
    change (submitStep (material.call.register execution.application who) who
      material.call.packet).config = _
    rw [submitStep_config]
    unfold Submission.register
    split
    · split <;> rfl
    · rfl
  refine ⟨⟨after⟩, recordsEntry_respond (runtime := runtime) execution who _ remaining none,
    by rw [respondEntry_of_transmission (runtime := runtime) execution who _ material submits],
      ready, ?_, ?_, ?_⟩
  · -- The witness.
    change AcceptanceWitness setup event (sentEnvelope setup runtime leaks execution who material)
      execution.application.config (execution.respond (application setup runtime leaks) who
        (runtime.canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup runtime leaks) who) event action)).application
    rw [respondApplication]
    cases node : nodeView (graph setup) event with
    | sample payload law outputEq codeEq =>
        have none := nodeView_sample_actor outputEq codeEq
        rw [owned] at none
        cases none
    | bind actor payload outputEq codeEq =>
        have actorEq : actor = who :=
          Option.some.inj ((nodeView_bind_actor outputEq codeEq).symm.trans owned)
        subst actorEq
        obtain ⟨value, successful⟩ := bindSuccess actor payload outputEq codeEq node
        obtain ⟨choice, rfl⟩ : ∃ choice : PublicationResult (L.Val payload),
            action = cast (congrArg EventGraph.EventField.Action outputEq.symm) choice :=
          ⟨cast (congrArg EventGraph.EventField.Action outputEq) action, by simp⟩
        simp only [cast_cast, cast_eq] at successful
        subst successful
        generalize hview : execution.observe (application setup runtime leaks) actor =
          view at submits
        cases selected : canonicalFreshSlot actor view.application with
        | none =>
            simp only [EventGraphRuntime.canonicalServiceDecision,
              EventGraphRuntime.canonicalReactiveDecision, node, selected, Option.map_none,
              ReactiveApplication.SubmissionNormalization.action] at submits
            cases submits
        | some serial =>
            have fresh := canonicalFreshSlot_spec actor _ serial selected
            rw [← hview] at fresh selected
            rw [← hview] at submits
            rw [runtime.canonicalServiceDecision_binding leaks actor
              (execution.recall actor)
              (execution.observe (application setup runtime leaks) actor) event
              payload outputEq codeEq node serial selected (.success value)] at submits
            cases Option.some.inj submits
            have freshLookup : execution.application.candidates.lookup
                (actor, .prepared serial) = .fresh := fresh
            refine Or.inl ⟨(actor, .prepared serial), actor, payload, value, rfl, outputEq, ?_⟩
            change (submitStep (Submission.register
              ⟨.commitment event (actor, .prepared serial), some ⟨payload, value⟩⟩
              execution.application actor) actor
              (.commitment event (actor, .prepared serial))).candidates.lookup
                (actor, .prepared serial) = _
            simp [submitStep, Submission.register, freshLookup,
              CommitmentCandidates.lookup_freeze_self, CommitmentCandidates.lookup_prepare_self]
    | resolve actor payload binding checks outputEq codeEq =>
        have actorEq : actor = who :=
          Option.some.inj ((nodeView_resolve_actor outputEq codeEq).symm.trans owned)
        subst actorEq
        rw [runtime.canonicalServiceDecision_eq_of_not_bind leaks actor
          (execution.recall actor) (execution.observe (application setup runtime leaks) actor) event
          action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
        unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
        simp only [node] at submits
        rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
            (execution.observe (application setup runtime leaks) actor).application with
          ⟨candidate, raw, packet⟩ | packet
        · obtain ⟨_, value, localResolved, _, _, rawEq⟩ :=
            reactiveResolutionPacket_opening actor event payload binding checks outputEq action
              (execution.observe (application setup runtime leaks) actor).application event
                candidate
              raw packet
          subst rawEq
          have resolved : EventGraph.EventCode.resolveOutput? binding checks true
              execution.application.config.store = some (.success value) := by
            have local' := localResolved
            change EventGraph.EventCode.resolveOutput? binding checks true
              ((graph setup).playerStore actor execution.application.config.store) = _ at local'
            rwa [EventGraph.EventCode.resolveOutput?_playerStore] at local'
          rw [packet] at submits
          simp only [Option.map_some, ReactiveApplication.SubmissionNormalization.action,
            Option.some.injEq] at submits
          refine Or.inr ⟨candidate, ⟨payload, value⟩, actor, payload, binding, checks, outputEq,
            codeEq, value, ?_, node, resolved⟩
          rw [← submits]
          rfl
        · rw [packet] at submits
          cases submits
  · intro _
    change (execution.respond (application setup runtime leaks) who
      (runtime.canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup runtime leaks) who) event
          action)).application.config = _
    rw [respondApplication]
    exact sameConfig
  · intro receipt
    exfalso
    change (_, true) ∈ execution.receipts at receipt
    obtain ⟨ledgerMessage, inLedger, sameId, _⟩ :=
      exists_of_forall₂_mem facts.receipts _ receipt
    have lower := facts.serials.ledger ledgerMessage inLedger
    change (who, execution.network.nextSerial who) = ledgerMessage.id at sameId
    rw [← sameId] at lower
    exact Nat.lt_irrefl _ lower

variable (setup runtime leaks) in
/-- **The event-level failed histories** of the one-packet game: those whose
typed readout records a failure of `event` and a failed reveal of `who`. -/
def EventFailedHistory (who : Player) (event : (graph setup).EventId) :
    Set ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
      scheduler).History :=
  {history | sourceReadout setup runtime leaks history.state ∈ EventFailedReadout setup who event}

end Invariant

end Vegas
