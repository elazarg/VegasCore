/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Pending.ReactiveRuntime
import Vegas.EventGraph.Validation

/-! # Source gameplay with frozen resolution decisions

Binding and chance use the source graph's existing semantics. Each resolution
has two native phases: admission of an opaque decision handle, then opening of
that immutable decision. Admission does not complete a source event. Each phase
has its own authorization and deadline. A public timeout seals gameplay without
inventing source outputs; an authenticated report can still travel through the
same pending-message runner afterward.

This module defines the protocol and its operational boundary. It does not
assert an equilibrium-preservation theorem or a watcher collection bound.
-/

noncomputable section

namespace Vegas.SourceSession

open Interaction GameTheory.Math.Probability
open EventGraph
open EventGraphRuntime (Raw Handle OpeningFact NodeView nodeView)

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [R : IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The reporter is a distinct native participant, with no source decisions
or private source inputs. -/
inductive Principal (Player : Type) where
  | player (who : Player)
  | watcher
  deriving DecidableEq

inductive PhaseKind where
  | binding | admission | opening
  deriving DecidableEq

/-- Different source phases remain distinct even when they start at one clock. -/
inductive PhaseKey (graph : Vegas.EventGraph Player L) where
  | source (event : graph.EventId) (kind : PhaseKind)
  | reporting
  deriving DecidableEq

structure Runtime (graph : Vegas.EventGraph Player L) where
  deadline : PhaseKey graph → Nat

abbrev DecisionHandle (graph : Vegas.EventGraph Player L) :=
  CommitmentHandle Player graph.EventId

structure Admission (graph : Vegas.EventGraph Player L) where
  handle : DecisionHandle graph
  enteredAt : Nat

inductive Status (graph : Vegas.EventGraph Player L) where
  | running
  | completed
  | cancelled (phase : PhaseKey graph)
  deriving DecidableEq

structure State (graph : Vegas.EventGraph Player L) where
  source : EventGraphRuntime.State graph
  decisions : CommitmentCandidates Player graph.EventId (Raw L)
  admissions : graph.EventId → Option (Admission graph)
  receipts : PhaseKey graph → Option (MessageId (Principal Player))
  status : Status graph
  sealedAt : Nat
  report : Option (List (MessageId (Principal Player)))

structure DecisionOpening (graph : Vegas.EventGraph Player L) where
  handle : DecisionHandle graph
  raw : Raw L
  deriving DecidableEq

inductive Certificate (graph : Vegas.EventGraph Player L) where
  | source (fact : OpeningFact graph)
  | decision (fact : DecisionOpening graph)
  deriving DecidableEq

inductive Call (graph : Vegas.EventGraph Player L) where
  | binding (event : graph.EventId) (handle : Handle graph)
  | admission (event : graph.EventId) (handle : DecisionHandle graph)
  | opening (event : graph.EventId) (handle : DecisionHandle graph) (raw : Raw L)
  | giveUp (phase : PhaseKey graph)
  | malformed (raw : Raw L)
  deriving DecidableEq

def Call.phase? : Call graph → Option (PhaseKey graph)
  | .binding event _ => some (.source event .binding)
  | .admission event _ => some (.source event .admission)
  | .opening event _ _ => some (.source event .opening)
  | .giveUp phase => some phase
  | .malformed _ => none

structure GamePacket (graph : Vegas.EventGraph Player L) where
  call : Call graph
  certificates : List (Certificate graph)
  token : Option (PhaseKey graph)
  deriving DecidableEq

/-- Report bodies are authentic previously possessed envelopes. Including
report envelopes lets evidence cover players abusing the reporter's wire
format as well as ordinary gameplay packets. -/
inductive Packet (graph : Vegas.EventGraph Player L) where
  | gameplay (packet : GamePacket graph)
  | report (evidence : List (Message (Principal Player) (Packet graph)))
      (token : Option (PhaseKey graph))

inductive CertificateRequest (graph : Vegas.EventGraph Player L) where
  | owned (certificate : Certificate graph)
  | forward (id : MessageId (Principal Player)) (index : Nat)

structure GameSubmission (graph : Vegas.EventGraph Player L) where
  call : Call graph
  material : Option (Raw L)
  certificates : List (CertificateRequest graph)
  /-- Private source intention stays in the owner's action recall. It is never
  inspected by the handler or serialized into a packet. -/
  resolutionIntent : Option Bool := none

inductive Submission (graph : Vegas.EventGraph Player L) where
  | gameplay (submission : GameSubmission graph)
  | report (ids : List (MessageId (Principal Player)))

inductive EnvironmentCommand (graph : Vegas.EventGraph Player L) where
  | advanceClock
  | executeSample (event : graph.EventId)
  | expire (phase : PhaseKey graph)

namespace State

def finish (state : State graph) : State graph :=
  if state.status = .running ∧ state.source.config.cut.Terminal then
    { state with status := .completed, sealedAt := state.source.clock }
  else state

def initial (inputs : graph.Inputs) : State graph :=
  finish {
    source := EventGraphRuntime.State.initial inputs
    decisions := .empty
    admissions := fun _ => none
    receipts := fun _ => none
    status := .running
    sealedAt := 0
    report := none }

def activePhase? (state : State graph) (event : graph.EventId) : Option PhaseKind :=
  if state.status = .running ∧ state.source.config.cut.Ready event then
    match nodeView graph event with
    | .bind .. => some .binding
    | .resolve .. =>
        if (state.admissions event).isSome then some .opening else some .admission
    | .sample .. => none
  else none

def enteredAt? (state : State graph) : PhaseKey graph → Option Nat
  | .source event .opening => (state.admissions event).map Admission.enteredAt
  | .source event .binding | .source event .admission => state.source.activatedAt event
  | .reporting => if state.status ≠ .running ∧ state.report.isNone then
      some state.sealedAt else none

def tokenFor (state : State graph) : PhaseKey graph → Option (PhaseKey graph)
  | .source event kind =>
      if state.activePhase? event = some kind then some (.source event kind) else none
  | .reporting => if state.status ≠ .running ∧ state.report.isNone then
      some .reporting else none

def timely (runtime : Runtime graph) (state : State graph) (phase : PhaseKey graph) : Bool :=
  match state.enteredAt? phase with
  | none => false
  | some entered => decide (state.source.clock - entered < runtime.deadline phase)

def record (state : State graph) (phase : PhaseKey graph) (id : MessageId (Principal Player)) :
    State graph :=
  { state with receipts := Function.update state.receipts phase (some id) }

def cancel (state : State graph) (phase : PhaseKey graph) : State graph :=
  { state with status := .cancelled phase, sealedAt := state.source.clock }

/-- Only a completed source game yields a source outcome. A cancelled game has
its own status and does not pretend to complete the source cut. -/
def outcome? (state : State graph) : Option graph.Outcome :=
  if state.status = .completed then state.source.config.outcome? else none

/-- Utilities are chosen before play. Cancellation has a fixed payoff vector,
and the separate reporting participant has no gameplay payoff. -/
def baseUtility (normal : graph.Outcome → Player → ℝ) (cancelled : Player → ℝ)
    (state : State graph) : Principal Player → ℝ
  | .player who => state.outcome?.elim (cancelled who) (fun outcome => normal outcome who)
  | .watcher => 0

omit [DecidableEq Player] in
@[simp] theorem cancel_config (state : State graph) (phase : PhaseKey graph) :
    (state.cancel phase).source.config = state.source.config := rfl

@[simp] theorem cancel_outcome? (state : State graph) (phase : PhaseKey graph) :
    (state.cancel phase).outcome? = none := by
  simp [outcome?, cancel]

@[simp] theorem cancel_baseUtility (normal : graph.Outcome → Player → ℝ)
    (cancelled : Player → ℝ) (state : State graph) (phase : PhaseKey graph) (who : Player) :
    baseUtility normal cancelled (state.cancel phase) (.player who) = cancelled who := by
  simp [baseUtility]

end State

/-- Register only the authenticated sender's material. Exposure fixes a fresh
candidate as openable or permanently unopenable; retries cannot replace it. -/
def submit (state : State graph) (who : Principal Player) : Submission graph → State graph
  | .report _ => state
  | .gameplay submission =>
      match who, submission.call with
      | .watcher, _ => state
      | .player who, .binding event handle =>
          let original : EventGraphRuntime.Submission graph :=
            ⟨.commitment event handle, submission.material⟩
          { state with
            source := EventGraphRuntime.submitStep
              (original.register state.source who) who original.packet }
      | .player who, .admission _ handle =>
          if handle.1 = who then
            let prepared := match submission.material with
              | none => state.decisions
              | some raw => state.decisions.prepare who handle.2 raw
            { state with decisions := prepared.freeze handle }
          else state
      | .player _, .opening .. | .player _, .giveUp _ | .player _, .malformed _ => state

def Packet.certificates : Packet graph → List (Certificate graph)
  | .gameplay packet => packet.certificates
  | .report evidence _ => evidence.flatMap fun message => message.payload.certificates
termination_by packet => sizeOf packet
decreasing_by
  simp_wf
  have member := List.sizeOf_lt_of_mem ‹message ∈ evidence›
  have fields : sizeOf message = 1 + sizeOf message.id + sizeOf message.payload := by
    cases message
    rfl
  omega

def Packet.nestedEnvelopes : Packet graph →
    List (Message (Principal Player) (Packet graph))
  | .gameplay _ => []
  | .report evidence _ => evidence.flatMap fun message =>
      message :: message.payload.nestedEnvelopes
termination_by packet => sizeOf packet
decreasing_by
  simp_wf
  have member := List.sizeOf_lt_of_mem ‹message ∈ evidence›
  have fields : sizeOf message = 1 + sizeOf message.id + sizeOf message.payload := by
    cases message
    rfl
  omega

/-- The outer signed envelope is available immediately. Descendant envelopes
come from authenticated report contents, never from guessed identifiers. -/
def Packet.envelopes (id : MessageId (Principal Player)) (packet : Packet graph) :
    List (Message (Principal Player) (Packet graph)) :=
  ⟨id, packet⟩ :: match packet with
    | .gameplay _ => []
    | .report .. => packet.nestedEnvelopes

def certificateFor (state : State graph) (who : Principal Player)
    (known : List (Message (Principal Player) (Packet graph))) :
    CertificateRequest graph → Option (Certificate graph)
  | .owned (.source fact) =>
      if Principal.player fact.handle.1 = who ∧
          state.source.candidates.verify fact.handle fact.raw then
        some (.source fact) else none
  | .owned (.decision fact) =>
      if Principal.player fact.handle.1 = who ∧ state.decisions.verify fact.handle fact.raw then
        some (.decision fact) else none
  | .forward id index =>
      (known.find? fun message => message.id = id).bind fun message =>
        message.payload.certificates[index]?

/-- Materialization is the only route from a private request to authentic wire
evidence. Failed requests remain ordinary unauthenticated transmissions. -/
def emit (state : State graph) (who : Principal Player)
    (known : List (Message (Principal Player) (Packet graph))) : Submission graph → Packet graph
  | .gameplay submission => .gameplay
      ⟨submission.call, submission.certificates.filterMap (certificateFor state who known),
        submission.call.phase?.bind state.tokenFor⟩
  | .report ids =>
      let available := known.flatMap fun message => message.payload.envelopes message.id
      .report (ids.eraseDups.filterMap fun id => available.find? fun message => message.id = id)
        (state.tokenFor .reporting)

/-- The actual admitted handle, independent of its private catalogue meaning. -/
def acceptDecision (state : State graph) (event : graph.EventId) (handle : DecisionHandle graph)
    (id : MessageId (Principal Player)) : State graph :=
  { state.record (.source event .admission) id with
    admissions := Function.update state.admissions event (some ⟨handle, state.source.clock⟩) }

@[simp] theorem acceptDecision_config (state : State graph) (event : graph.EventId)
    (handle : DecisionHandle graph) (id : MessageId (Principal Player)) :
    (acceptDecision state event handle id).source.config = state.source.config := rfl

@[simp] theorem acceptDecision_enteredAt (state : State graph) (event : graph.EventId)
    (handle : DecisionHandle graph) (id : MessageId (Principal Player)) :
    (acceptDecision state event handle id).enteredAt? (.source event .opening) =
      some state.source.clock := by
  simp [acceptDecision, State.enteredAt?, Function.update]

/-- Private original intentions cannot change either certificate issuance or
the public packet. The reactive runner still records the full private action. -/
theorem emit_intention_irrel (state : State graph) (who : Principal Player)
    (known : List (Message (Principal Player) (Packet graph))) (submission : GameSubmission graph)
    (intent : Option Bool) :
    emit state who known (.gameplay { submission with resolutionIntent := intent }) =
      emit state who known (.gameplay submission) := rfl

/-- FALSE is a genuine openable decision value, distinct from a candidate
without any opening. No original private binding evidence belongs in it. -/
def encodeDecision (payload : L.Ty) (decision : PublicationResult (L.Val payload)) : Raw L :=
  ⟨R.result payload, (R.valueEquiv payload).symm decision⟩

def openDecision (state : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (handle : DecisionHandle graph) (raw : Raw L)
    (certificates : List (Certificate graph)) : Option (State graph) := do
  let encoded ← raw.as? (R.result payload)
  let decision := R.valueEquiv payload encoded
  let helper := Certificate.decision (graph := graph) ⟨handle, raw⟩
  let (disclose, result) ← match decision with
    | .failure =>
        if certificates = [helper] then some (false, PublicationResult.failure) else none
    | .success value => do
        let original ← state.source.accepted binding.field
        if certificates = [helper, .source ⟨original, ⟨payload, value⟩⟩] then
          let accepted ← GuardCheck.allAccepted? checks
            (graph.publicStore state.source.config.store) (.success value)
          if accepted then pure (true, .success value) else none
        else none
  let next := state.source.complete event ready
    (cast (congrArg EventField.Action outputEq.symm) disclose)
    (cast (congrArg EventField.Value outputEq.symm) result)
  pure { state with source := next }

theorem openDecision_failure (state : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (handle : DecisionHandle graph) :
    openDecision state event ready owner payload binding checks outputEq handle
        (encodeDecision payload .failure)
        [.decision ⟨handle, encodeDecision payload .failure⟩] =
      some { state with
        source := state.source.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) false)
          (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) } := by
  simp [openDecision, encodeDecision]

theorem openDecision_success (state : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (handle : DecisionHandle graph) (original : Handle graph)
    (value : L.Val payload)
    (associated : state.source.accepted binding.field = some original)
    (verdict : GuardCheck.allAccepted? checks
      (graph.publicStore state.source.config.store) (.success value) = some true) :
    openDecision state event ready owner payload binding checks outputEq handle
        (encodeDecision payload (.success value))
        [.decision ⟨handle, encodeDecision payload (.success value)⟩,
          .source ⟨original, ⟨payload, value⟩⟩] =
      some { state with
        source := state.source.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (PublicationResult.success value)) } := by
  simp [openDecision, encodeDecision, associated, verdict]

/-- A helper TRUE that would disclose extra private data while producing
source FALSE cannot complete the source event. Honest source guard failure
uses encoded FALSE, retaining the original intention only in private recall. -/
theorem openDecision_guard_failure (state : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (handle : DecisionHandle graph) (original : Handle graph) (value : L.Val payload)
    (associated : state.source.accepted binding.field = some original)
    (verdict : GuardCheck.allAccepted? checks
      (graph.publicStore state.source.config.store) (.success value) = some false) :
    openDecision state event ready owner payload binding checks outputEq handle
        (encodeDecision payload (.success value))
        [.decision ⟨handle, encodeDecision payload (.success value)⟩,
          .source ⟨original, ⟨payload, value⟩⟩] = none := by
  simp [openDecision, encodeDecision, associated, verdict]

omit [DecidableEq Player] in
/-- Executing encoded FALSE uses exactly the existing deterministic source
step, including when the original private binding has failed. -/
theorem failure_source_step (state : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks) :
    state.source.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) false) =
      PMF.pure (state.source.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) false)
        (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure)).config := by
  have result := EventGraphRuntime.resolveOutput?_false_eq_failure_of_ready
    state.source event ready owner payload binding checks outputEq codeEq
  rw [state.source.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq false (PMF.pure .failure)]
  · simp [EventGraphRuntime.State.complete, PMF.pure_map]
  · rw [EventCode.resolve_eval?, result]
    rfl

omit [DecidableEq Player] in
/-- The certified original value and public guard verdict determine precisely
the existing TRUE transition. Binding provenance supplies `stored`; the
handler itself never queries a hidden value to compute the guard result. -/
theorem success_source_step (state : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (value : L.Val payload) (accepted : Bool)
    (stored : binding.get? state.source.config.store = some (.success value))
    (verdict : GuardCheck.allAccepted? checks
      (graph.publicStore state.source.config.store) (.success value) = some accepted) :
    state.source.config.step event ready
        (cast (congrArg EventField.Action outputEq.symm) true) =
      PMF.pure (state.source.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) true)
        (cast (congrArg EventField.Value outputEq.symm)
          (if accepted then PublicationResult.success value else .failure))).config := by
  have result := EventCode.resolveOutput?_of_binding binding checks
    state.source.config.store (.success value) stored
  rw [verdict] at result
  simp only [pure, Pure.pure] at result
  rw [state.source.config.step_eq_map_of_code event ready outputEq
    (.resolve owner payload binding checks) codeEq true
    (PMF.pure (if accepted then .success value else .failure))]
  · simp [EventGraphRuntime.State.complete, PMF.pure_map]
  · rw [EventCode.resolve_eval?, result]
    rfl

open scoped Classical in
def handleGame (runtime : Runtime graph) (state : State graph)
    (id : MessageId (Principal Player)) (packet : GamePacket graph) : Option (State graph) := do
  let phase ← packet.call.phase?
  if packet.token = some phase ∧ state.tokenFor phase = some phase ∧
      state.timely runtime phase then
    match packet.call with
    | .binding event handle =>
        if ready : state.source.config.cut.Ready event then
          match nodeView graph event with
          | .bind owner payload outputEq _ =>
              if id.1 = .player owner ∧ handle.1 = owner ∧ packet.certificates = [] ∧
                  state.source.accepted (.inr event) = none ∧ state.source.HandleUnused handle then
                let next := { state with
                  source := EventGraphRuntime.acceptBinding
                    state.source event ready owner payload outputEq handle }
                pure (State.finish (next.record phase id))
              else none
          | _ => none
        else none
    | .admission event handle =>
        match nodeView graph event with
        | .resolve owner .. =>
            if id.1 = .player owner ∧ handle = (owner, event) ∧ packet.certificates = [] then
              some (acceptDecision state event handle id) else none
        | _ => none
    | .opening event handle raw =>
        if ready : state.source.config.cut.Ready event then
          match nodeView graph event with
          | .resolve owner payload binding checks outputEq _ =>
              if id.1 = .player owner ∧
                  (state.admissions event).map Admission.handle = some handle then
                let next ← openDecision state event ready owner payload binding checks
                  outputEq handle raw packet.certificates
                pure (State.finish (next.record phase id))
              else none
          | _ => none
        else none
    | .giveUp (.source event _) =>
        match nodeView graph event with
        | .bind owner .. | .resolve owner .. =>
            if id.1 = .player owner ∧ packet.certificates = [] then
              some (state.cancel phase) else none
        | .sample .. => none
    | .giveUp .reporting | .malformed _ => none
  else none

def handle (runtime : Runtime graph) (state : State graph)
    (message : Message (Principal Player) (Packet graph)) : Option (State graph) :=
  match message.payload with
  | .gameplay packet => handleGame runtime state message.id packet
  | .report evidence token =>
      if message.sender = .watcher ∧ token = some .reporting ∧
          state.tokenFor .reporting = some .reporting ∧ state.timely runtime .reporting then
        some { state.record .reporting message.id with
          report := some (evidence.map Message.id) }
      else none

def environment (runtime : Runtime graph) (state : State graph) :
    EnvironmentCommand graph → PMF (State graph)
  | .advanceClock => PMF.pure
      { state with source := { state.source with clock := state.source.clock + 1 } }
  | .executeSample event =>
      if state.status = .running then
        (EventGraphRuntime.executeSample state.source event).map fun source =>
          State.finish { state with source }
      else PMF.pure state
  | .expire phase => PMF.pure <|
      if state.tokenFor phase = some phase ∧ state.timely runtime phase = false then
        match phase with
        | .source _ _ => state.cancel phase
        | .reporting => { state with report := some [] }
      else state

structure PublicView (graph : Vegas.EventGraph Player L) where
  source : EventGraphRuntime.PublicView graph
  admissions : graph.EventId → Option (Admission graph)
  receipts : PhaseKey graph → Option (MessageId (Principal Player))
  status : Status graph
  sealedAt : Nat
  report : Option (List (MessageId (Principal Player)))

def State.publicView (state : State graph) : PublicView graph :=
  ⟨state.source.publicView, state.admissions, state.receipts,
    state.status, state.sealedAt, state.report⟩

inductive LocalView (graph : Vegas.EventGraph Player L) where
  | player (who : Player) (publicView : PublicView graph) (source : graph.PlayerObservation who)
      (sourceCandidates : EventGraphRuntime.CandidateSlot graph → CommitmentCandidate (Raw L))
      (decisionCandidates : graph.EventId → CommitmentCandidate (Raw L))
  | watcher (publicView : PublicView graph)

def application (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph)) :
    ReactiveApplication (Principal Player) where
  State := State graph
  Payload := Packet graph
  Submission := Submission graph
  EnvironmentCommand := EnvironmentCommand graph
  LocalObservation := LocalView graph
  PublicObservation := PublicView graph
  packet := emit
  submit := submit
  handle := handle runtime
  environment := environment runtime
  observePlayer state
    | .player who => .player who state.publicView
        (graph.playerObserve who state.source.config)
        (fun slot => state.source.candidates.lookup (who, slot))
        (fun event => state.decisions.lookup (who, event))
    | .watcher => .watcher state.publicView
  observePublic := State.publicView
  observePending := leaks

@[simp] theorem submit_watcher (state : State graph) (submission : Submission graph) :
    submit state .watcher submission = state := by
  cases submission <;> rfl

@[simp] theorem certificateFor_watcher_owned (state : State graph)
    (known : List (Message (Principal Player) (Packet graph))) (certificate : Certificate graph) :
    certificateFor state .watcher known (.owned certificate) = none := by
  cases certificate <;> simp [certificateFor]

/-- Private registration and commitment exposure cannot advance gameplay or
change the public phase record. -/
theorem submit_publicView (state : State graph) (who : Principal Player)
    (submission : Submission graph) :
    (submit state who submission).publicView = state.publicView := by
  cases submission with
  | report ids => rfl
  | gameplay submission =>
      cases who with
      | watcher => rfl
      | player who =>
          cases call : submission.call with
          | binding event handle =>
              simp only [submit, call, State.publicView, EventGraphRuntime.submitStep_publicView,
                (EventGraphRuntime.Submission.register_facts
                  ⟨.commitment event handle, submission.material⟩ who state.source).2.2]
          | admission event handle =>
              simp only [submit, call]
              split <;> rfl
          | opening event handle raw | giveUp phase | malformed raw => simp [submit, call]

theorem submit_config (state : State graph) (who : Principal Player)
    (submission : Submission graph) :
    (submit state who submission).source.config = state.source.config := by
  cases submission with
  | report ids => rfl
  | gameplay submission =>
      cases who with
      | watcher => rfl
      | player who =>
          cases call : submission.call with
          | binding event handle =>
              simp only [submit, call, EventGraphRuntime.submitStep_config,
                (EventGraphRuntime.Submission.register_facts
                  ⟨.commitment event handle, submission.material⟩ who state.source).1]
          | admission event handle =>
              simp only [submit, call]
              split <;> rfl
          | opening event handle raw | giveUp phase | malformed raw => simp [submit, call]

theorem emit_report_origin (state : State graph) (who : Principal Player)
    (known : List (Message (Principal Player) (Packet graph)))
    (ids : List (MessageId (Principal Player)))
    (evidence : List (Message (Principal Player) (Packet graph)))
    (token : Option (PhaseKey graph))
    (emitted : emit state who known (.report ids) = .report evidence token)
    (message : Message (Principal Player) (Packet graph)) (member : message ∈ evidence) :
    ∃ original ∈ known, message ∈ original.payload.envelopes original.id := by
  have exact := (Packet.report.inj emitted).1
  rw [← exact] at member
  obtain ⟨id, _, found⟩ := List.mem_filterMap.mp member
  exact List.mem_flatMap.mp (List.mem_of_find?_eq_some found)

theorem handleGame_none_of_closed (runtime : Runtime graph) (state : State graph)
    (closed : state.status ≠ .running) (id : MessageId (Principal Player))
    (packet : GamePacket graph) :
    handleGame runtime state id packet = none := by
  rcases packet with ⟨call, certificates, token⟩
  cases call with
  | binding event handle | admission event handle =>
      simp [handleGame, Call.phase?, State.tokenFor, State.activePhase?, closed]
  | opening event handle raw =>
      simp [handleGame, Call.phase?, State.tokenFor, State.activePhase?, closed]
  | giveUp phase =>
      cases phase <;>
        simp [handleGame, Call.phase?, State.tokenFor, State.activePhase?, closed]
  | malformed raw => simp [handleGame, Call.phase?]

/-- Once sealed, accepted report traffic cannot change source execution or
the normal/cancelled economic outcome. -/
theorem handle_closed (runtime : Runtime graph) (state next : State graph)
    (closed : state.status ≠ .running) (message : Message (Principal Player) (Packet graph))
    (accepted : handle runtime state message = some next) :
    next.status = state.status ∧ next.source.config = state.source.config := by
  cases packet : message.payload with
  | gameplay game =>
      simp [handle, packet, handleGame_none_of_closed runtime state closed] at accepted
  | report evidence token =>
      simp only [handle, packet] at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact ⟨rfl, rfl⟩
      · cases accepted

/-- The scheduler cannot execute future chance nodes or reopen a closed phase.
Only clock and reporting state may change after gameplay is sealed. -/
theorem environment_closed (runtime : Runtime graph) (state : State graph)
    (closed : state.status ≠ .running) (command : EnvironmentCommand graph) :
    (environment runtime state command).map (fun next => (next.status, next.source.config)) =
      PMF.pure (state.status, state.source.config) := by
  cases command with
  | advanceClock => simp [environment, PMF.pure_map]
  | executeSample event => simp [environment, closed, PMF.pure_map]
  | expire phase =>
      cases phase with
      | source event kind =>
          simp [environment, State.tokenFor, State.activePhase?, closed, PMF.pure_map]
      | reporting =>
          simp only [environment, PMF.pure_map]
          split <;> rfl

end Vegas.SourceSession
