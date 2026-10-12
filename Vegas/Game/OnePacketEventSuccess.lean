/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketFirstActivation
import Vegas.Game.OnePacketEventFailure
import Vegas.Pending.ReactiveAcceptedOutput
import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

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
success. Under the asynchronous contract and the timeliness margin, the
packet sent at the first activation is accepted on every terminal history, so
the event's output is a success there, and no terminal readout is an
event-level failed readout of the sender
(`Vegas.firstActivation_canonical_succeeds`).

On the histories of the one-packet game, the event-level failed histories of a
player are those whose readout is an event-level failed readout
(`Vegas.EventFailedHistory`); they pay exactly the exclusion payoff
(`Vegas.exclusionReadoutUtility_of_eventFailedHistory`). Committing to the
canonical decision at the first activation never reaches one, whatever the
other policies (`Vegas.firstActivation_commit_notFailed`), so its local failure
probability at a first-activation site is zero
(`Vegas.firstActivation_localFailure_eq_zero`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
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

variable (setup) in
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
    (accepted : handle (runtime setup) state ⟨message.id, message.payload.call⟩ = some next) :
    OutputSucceeded next.config.store event := by
  rcases witness with ⟨candidate, owner, payload, value, call, layout, fixed⟩ |
    ⟨candidate, raw, owner, payload, binding, checks, outputEq, codeEq, value, call, node,
      resolved⟩
  · rw [call] at accepted
    exact handle_commitment_output_success (runtime setup) state next message.id event
      candidate accepted valid owner payload layout value fixed
  · rw [call] at accepted
    rw [← sameConfig] at resolved
    exact handle_opening_output_success (runtime setup) state next message.id event candidate
      raw accepted owner payload binding checks outputEq codeEq node value resolved

section Invariant

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (horizon : Nat) (scheduler : (application setup leaks).Scheduler)

variable (setup leaks) in
/-- **The acceptance invariant** after a recorded send of `message` for
`event` from the configuration `sent`. -/
def AcceptanceInvariant (who : Player) (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) : (application setup leaks).ProtocolState → Prop
  | none => False
  | some control =>
      Nonempty (((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).Trace (some control)) ∧
      RecordsEntry setup leaks who entry (some control) ∧
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
    (entry : (application setup leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup))) (event : (graph setup).EventId)
    (sent : (graph setup).Config) (before after : (application setup leaks).ProtocolState)
    (joint : Player → Option (application setup leaks).Action)
    (legal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Legal before joint)
    (holds : AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event
      sent before)
    (reached : after ∈ (((bounds.onePacketMenu (runtime setup) leaks).protocol
      (initialLaw setup) horizon scheduler).step before ⟨joint, legal⟩).support) :
    AcceptanceInvariant setup leaks bounds horizon scheduler who entry message event sent
      after := by
  cases before with
  | none => exact holds.elim
  | some control =>
      obtain ⟨⟨trace⟩, records, emitted, sentReady, witness, stable, settled⟩ := holds
      have afterRecords := recordsEntry_transition who entry (initialLaw setup) horizon scheduler
        _ after joint records reached
      cases after with
      | none => exact afterRecords.elim
      | some next =>
          have nextTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol
              (initialLaw setup) horizon scheduler).Trace (some next) :=
            .extend trace joint legal reached
          have kept := (keepsFixedCandidates_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have keptStore := (keepsStore_step (runtime setup) leaks).transition
            (initialLaw setup) horizon scheduler control next joint reached
          have configStep := transition_configStep (initialLaw setup) horizon scheduler control
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
            have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
                scheduler).Trace (some ⟨remaining, current, execution⟩) :=
              (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
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
                          (execution.includePending (application setup leaks)
                            id).receipts at receipt
                        change OutputSucceeded
                          (execution.includePending (application setup leaks)
                            id).application.config.store event
                        unfold ReactiveApplication.Execution.includePending
                          MessageNetwork.includePending at receipt ⊢
                        cases found : execution.network.lookup id with
                        | none =>
                            simp only [found] at receipt ⊢
                            exact settled receipt
                        | some envelope =>
                            simp only [found] at receipt ⊢
                            cases accepted : (application setup leaks).handle
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
                                    handle_store_of_some (runtime setup) _ _ _
                                      (reactiveHandle_call accepted) field value stored
                                · obtain ⟨idEq, -⟩ := Prod.mk.inj (List.mem_singleton.mp new)
                                  -- The included envelope is the message.
                                  obtain ⟨earlier, later, split⟩ := records
                                  change execution.recall who = _ at split
                                  have output : message ∈ (application setup leaks).outputs
                                      (execution.recall who) := by
                                    rw [split]
                                    exact List.mem_filterMap.mpr ⟨entry, by simp, emitted⟩
                                  rw [← facts.inputs who] at output
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
                                    handle_config_mem_step (runtime setup) _ _ _ call
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
                                  exact witness.output_success (stable ready.1) facts.binding call

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
    {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (after : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution.respond (application setup leaks) who
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event action)⟩)) :
    AcceptanceInvariant setup leaks bounds horizon scheduler who
      (respondEntry setup leaks execution who ((runtime setup).canonicalServiceDecision leaks who
        (execution.recall who) (execution.observe (application setup leaks) who) event action))
      (sentEnvelope setup leaks execution who material) event execution.application.config
      (some ⟨remaining, none, execution.respond (application setup leaks) who
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event action)⟩) := by
  have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) :=
    (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon scheduler
      trace
  have facts := legalFacts setup leaks horizon scheduler _ rawTrace
  have readyView := (PublicView.ownTurn?_spec _ who event turn).1
  have owned := (PublicView.ownTurn?_spec _ who event turn).2
  have ready := (execution.application.publicView_eventReady event).mp readyView
  have respondApplication : (execution.respond (application setup leaks) who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)).application =
      (application setup leaks).submit execution.application who material := by
    unfold ReactiveApplication.Execution.respond
    rw [submits]
  have sameConfig : ((application setup leaks).submit execution.application who
      material).config = execution.application.config := by
    change (submitStep (material.call.register execution.application who) who
      material.call.packet).config = _
    rw [submitStep_config]
    unfold Submission.register
    split
    · split <;> rfl
    · rfl
  refine ⟨⟨after⟩, recordsEntry_respond execution who _ remaining none,
    by rw [respondEntry_of_transmission execution who _ material submits], ready, ?_, ?_, ?_⟩
  · -- The witness.
    change AcceptanceWitness setup event (sentEnvelope setup leaks execution who material)
      execution.application.config (execution.respond (application setup leaks) who
        ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
          (execution.observe (application setup leaks) who) event action)).application
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
        generalize hview : execution.observe (application setup leaks) actor = view at submits
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
            rw [(runtime setup).canonicalServiceDecision_binding leaks actor
              (execution.recall actor)
              (execution.observe (application setup leaks) actor) event
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
        rw [(runtime setup).canonicalServiceDecision_eq_of_not_bind leaks actor
          (execution.recall actor) (execution.observe (application setup leaks) actor) event
          action (fun _ _ _ _ bind => by rw [node] at bind; cases bind)] at submits
        unfold EventGraphRuntime.serviceDecision EventGraphRuntime.reactiveDecision at submits
        simp only [node] at submits
        rcases reactiveResolutionPacket_shape actor event payload binding checks outputEq action
            (execution.observe (application setup leaks) actor).application with
          ⟨candidate, raw, packet⟩ | packet
        · obtain ⟨_, value, localResolved, _, _, rawEq⟩ :=
            reactiveResolutionPacket_opening actor event payload binding checks outputEq action
              (execution.observe (application setup leaks) actor).application event candidate
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
    change (execution.respond (application setup leaks) who
      ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event
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

/-- **Sending at the first activation succeeds surely.** Under the
asynchronous contract and the timeliness margin, let `who` send, at its first
activation for `event` in the one-packet game, the canonical decision of an
action that is a successful binding value at a binding. From the state that
response reaches, under terminal play of any players, every terminal history
has the event's output a success; in particular no terminal readout is an
event-level failed readout of any player for `event`. -/
theorem firstActivation_canonical_succeeds {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (certificate : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (players : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    (current : history.state = some ⟨remaining, none, execution.respond (application setup leaks)
      who ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
        (execution.observe (application setup leaks) who) event action)⟩) :
    ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralTerminalFrom certificate players history).support,
      ∃ control, final.state = some control ∧
        OutputSucceeded control.execution.application.config.store event ∧
        ∀ player, sourceReadout setup leaks (some control) ∉
          EventFailedReadout setup player event := by
  intro final supported
  have afterTrace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨remaining, none, execution.respond
        (application setup leaks) who ((runtime setup).canonicalServiceDecision leaks who
          (execution.recall who) (execution.observe (application setup leaks) who) event
          action)⟩) :=
    current ▸ history.trace
  have start := acceptanceInvariant_respond bounds horizon scheduler trace event turn action
    material submits bindSuccess afterTrace
  rw [← current] at start
  have reachedInvariant := ((bounds.onePacketMenu (runtime setup) leaks).information
    (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom_support_closed certificate
    players _ (fun state joint legal target holds reached =>
      acceptanceInvariant_transition bounds horizon scheduler who _ _ event _ state target joint
        legal holds reached)
    history start final supported
  have stopped := ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
    horizon scheduler).runBehavioralTerminalFrom_support_terminal certificate players history
    final supported
  cases state : final.state with
  | none =>
      rw [state] at reachedInvariant
      exact reachedInvariant.elim
  | some control =>
      rw [state] at reachedInvariant stopped
      obtain ⟨⟨finalTrace⟩, records, _, _, _, _, settled⟩ := reachedInvariant
      have rawTrace : ((application setup leaks).protocol (initialLaw setup) horizon
          scheduler).Trace (some control) :=
        (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
          scheduler finalTrace
      have terminal := contract.completes control rawTrace stopped
      have completed : event ∈ control.execution.application.config.cut.completed := by
        rw [terminal]
        exact Finset.mem_univ _
      have receipt := (firstActivation_canonical_settles bounds contract timely trace event turn
        never action material submits finalTrace records).2 completed
      have succeeded := settled receipt
      refine ⟨control, rfl, succeeded, fun player => ?_⟩
      exact not_mem_eventFailedReadout_of_store setup leaks control player event
        (not_storeEventFailed_of_outputSucceeded succeeded)

variable (setup leaks) in
/-- **The event-level failed histories** of the one-packet game: those whose
typed readout records a failure of `event` and a failed reveal of `who`. -/
def EventFailedHistory (who : Player) (event : (graph setup).EventId) :
    Set ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History :=
  {history | sourceReadout setup leaks history.state ∈ EventFailedReadout setup who event}

/-- **Event failure pays the exclusion payoff.** On an event-level failed
history the exclusion payoff of `who` is exactly its exclusion payoff. -/
theorem exclusionReadoutUtility_of_eventFailedHistory {Parameter : Type}
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) (event : (graph setup).EventId) :
    ∀ history ∈ EventFailedHistory setup leaks bounds horizon scheduler who event,
      exclusionReadoutUtility setup parameter utility excludedPayoff
        (sourceReadout setup leaks history.state) who = excludedPayoff who :=
  fun _ failed =>
    exclusionReadoutUtility_of_eventFailedReadout setup parameter utility excludedPayoff who
      event _ failed

open Classical in
/-- **Committing the canonical decision at the first activation never fails
the event.** Under the asynchronous contract and the timeliness margin, at a
decision history of `who` at its first activation for `event`, committing to
the canonical decision of an action that is a successful binding value at a
binding, play for the horizon from the history, under any other policies,
never reaches an event-level failed history of any player for `event`. -/
theorem firstActivation_commit_notFailed {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (profile : ∀ player, ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).History)
    {remaining : Nat} {who : Player} {execution : (application setup leaks).Execution}
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph setup).EventId)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ execution.recall who, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
      (execution.observe (application setup leaks) who) event action).transmission =
        some material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (info : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).InfoState who)
    (observed : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).infoOf who history.trace = info)
    (choice : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).Choice who info)
    (selected : choice.1 = some ((runtime setup).canonicalServiceDecision leaks who
      (execution.recall who) (execution.observe (application setup leaks) who) event action))
    (player : Player) :
    ∀ final ∈ (((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
        horizon scheduler).runBehavioralFrom
        (Profile.update (sig := ((bounds.onePacketMenu (runtime setup) leaks).information
          (initialLaw setup) horizon scheduler).behavioralSignature) profile who
          ((profile who).commit info choice)) (2 * horizon + 1) history).support,
      final ∉ EventFailedHistory setup leaks bounds horizon scheduler player event := by
  subst observed
  intro final supported
  let model := (bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
    horizon scheduler
  let committed := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  have bounded := (bounds.onePacketMenu (runtime setup) leaks).bounded (initialLaw setup)
    horizon scheduler
  let certificate := bounded.wellFoundedHistories
  -- One more step of play from a terminal history stays there.
  have longer : final ∈ (model.runBehavioralFrom committed (1 + (2 * horizon + 1))
      history).support := by
    rw [Nat.add_comm, model.runBehavioralFrom_add committed (2 * horizon + 1) 1 history,
      PMF.mem_support_bind_iff]
    refine ⟨final, supported, ?_⟩
    have terminal : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
        horizon scheduler).terminal final.state := by
      rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
        at supported
      exact model.runBehavioralTerminalFrom_support_terminal certificate committed history final
        supported
    rw [model.runBehavioralFrom_of_terminal committed 1 terminal]
    exact PMF.mem_support_pure_iff _ _ |>.mpr rfl
  rw [model.runBehavioralFrom_add committed 1 (2 * horizon + 1) history,
    PMF.mem_support_bind_iff] at longer
  obtain ⟨middle, stepped, rest⟩ := longer
  have middleState : middle.state = some ⟨remaining, none, execution.respond
      (application setup leaks) who ((runtime setup).canonicalServiceDecision leaks who
        (execution.recall who) (execution.observe (application setup leaks) who) event
        action)⟩ := by
    have committedStep := (bounds.onePacketMenu (runtime setup) leaks).run_commit_response
      (initialLaw setup) horizon scheduler profile history who remaining execution current
      choice _ selected
    have member : middle.state ∈ (PMF.pure (α := (application setup leaks).ProtocolState)
        (some ⟨remaining, none, execution.respond (application setup leaks) who
          ((runtime setup).canonicalServiceDecision leaks who (execution.recall who)
            (execution.observe (application setup leaks) who) event action)⟩)).support := by
      rw [← committedStep, PMF.support_map]
      exact ⟨middle, stepped, rfl⟩
    exact (PMF.mem_support_pure_iff _ _).mp member
  rw [← model.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded certificate bounded]
    at rest
  have trace : ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ history.trace
  obtain ⟨control, state, _, notFailed⟩ := firstActivation_canonical_succeeds bounds horizon
    scheduler contract timely trace event turn never action material submits bindSuccess
    certificate committed middle middleState final rest
  change sourceReadout setup leaks final.state ∉ EventFailedReadout setup player event
  rw [state]
  exact notFailed player

open Classical in
/-- **Sending at the first activation has event-level failure zero.** Under
the asynchronous contract and the timeliness margin, at a site of `who` whose
information is a first activation for `event`, the local law committing to the
canonical decision of an action that is a successful binding value at a binding
has zero probability of an event-level failed history, for every assessment
and every player. -/
theorem firstActivation_localFailure_eq_zero {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    [Finite ((bounds.onePacketMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).History]
    (assessment : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).BehavioralAssessment)
    {who : Player} (site : ((bounds.onePacketMenu (runtime setup) leaks).information
      (initialLaw setup) horizon scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (atSite : site.1 = some (past, view))
    (event : (graph setup).EventId)
    (turn : view.application.publicView.ownTurn? who = some event)
    (never : ∀ entry ∈ past, ¬ ActivatedAt setup leaks who event entry)
    (action : (graph setup).Action event) (material : (application setup leaks).Submission)
    (submits : ((runtime setup).canonicalServiceDecision leaks who past view event
      action).transmission = some material)
    (bindSuccess : ∀ owner payload outputEq codeEq,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq →
        ∃ value, (cast (congrArg EventGraph.EventField.Action outputEq) action :
          PublicationResult (L.Val payload)) = .success value)
    (choice : ((bounds.onePacketMenu (runtime setup) leaks).information (initialLaw setup)
      horizon scheduler).Choice who site.1)
    (selected : choice.1 = some ((runtime setup).canonicalServiceDecision leaks who past view
      event action))
    (player : Player) :
    InformationModel.localFailure (2 * horizon + 1) assessment site
      (EventFailedHistory setup leaks bounds horizon scheduler player event) (PMF.pure choice) =
        0 := by
  have near := InformationModel.localFailure_near_of_histories (2 * horizon + 1) assessment site
    (EventFailedHistory setup leaks bounds horizon scheduler player event) (PMF.pure choice) 0 0
    (fun history _ => by
      rw [sub_zero, abs_nonpos_iff]
      obtain ⟨history, observed⟩ := history
      have infoEq := observed
      rw [atSite] at infoEq
      change ((bounds.onePacketMenu (runtime setup) leaks).signals (initialLaw setup) horizon
        scheduler).infoOf who history.trace = _ at infoEq
      rw [(bounds.onePacketMenu (runtime setup) leaks).info] at infoEq
      cases state : history.state with
      | none =>
          rw [state] at infoEq
          cases infoEq
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          rw [state] at infoEq
          by_cases active : actor = some who
          · subst active
            simp only [ReactiveApplication.observe, ↓reduceIte] at infoEq
            obtain ⟨pastEq, viewEq⟩ := Prod.mk.inj (Option.some.inj infoEq)
            subst pastEq
            subst viewEq
            refine (expect_congr_on_support (g := fun _ => 0)
              (fun final supported => ?_)).trans (expect_constant _ _)
            have notFailed := firstActivation_commit_notFailed bounds horizon scheduler contract
              timely assessment.strategy history state event turn never action material submits
              bindSuccess site.1 observed choice selected player final supported
            simp only [notFailed, ↓reduceIte]
          · simp only [ReactiveApplication.observe, active, ↓reduceIte] at infoEq
            cases infoEq)
  rw [sub_zero, abs_nonpos_iff] at near
  exact near

end Invariant

end Vegas
