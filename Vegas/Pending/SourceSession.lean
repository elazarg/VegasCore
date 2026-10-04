/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Pending.ReactiveRuntime
import Vegas.EventGraph.Validation
import Vegas.Pending.EventCommitmentBinding
import Vegas.Pending.EventBindingInvariant
import Interaction.ReactivePacketEvidence

/-! # Source gameplay with frozen resolution decisions

Binding and chance use the source graph's existing semantics. Each resolution
has two native phases: admission of an opaque decision handle, then opening of
that immutable decision. Admission does not complete a source event. Each phase
has its own authorization and deadline. A public timeout seals gameplay without
inventing source outputs; an authenticated report can still travel through the
same pending-message runner afterward.

The certificate instance reuses the generic packet-evidence theorem at every
legal history, including partial leaks, forwarding and rejected calls. Source
binding provenance and reachability reuse the graph runtime invariants, with
authentic network evidence supplying the source-step premises. Compiler recall,
equilibrium preservation and watcher collection bounds remain separate obligations.
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

namespace PublicView

/-- Phase clocks are public metadata; client timing needs no private state. -/
def enteredAt? (view : PublicView graph) : PhaseKey graph → Option Nat
  | .source event .opening => (view.admissions event).map Admission.enteredAt
  | .source event .binding | .source event .admission => view.source.activatedAt event
  | .reporting => if view.status ≠ .running ∧ view.report.isNone then
      some view.sealedAt else none

def timely (runtime : Runtime graph) (view : PublicView graph) (phase : PhaseKey graph) : Bool :=
  match view.enteredAt? phase with
  | none => false
  | some entered => decide (view.source.clock - entered < runtime.deadline phase)

end PublicView

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

@[simp] theorem finish_source (state : State graph) :
    state.finish.source = state.source := by
  unfold finish
  split <;> rfl

def initial (inputs : graph.Inputs) : State graph :=
  finish {
    source := EventGraphRuntime.State.initial inputs
    decisions := .empty
    admissions := fun _ => none
    receipts := fun _ => none
    status := .running
    sealedAt := 0
    report := none }

theorem initial_bindingInvariant (inputs : graph.Inputs) :
    (initial inputs).source.BindingInvariant := by
  rw [initial, finish_source]
  exact EventGraphRuntime.State.initial_bindingInvariant inputs

def activePhase? (state : State graph) (event : graph.EventId) : Option PhaseKind :=
  if state.status = .running ∧ state.source.config.cut.Ready event then
    match nodeView graph event with
    | .bind .. => some .binding
    | .resolve .. =>
        if (state.admissions event).isSome then some .opening else some .admission
    | .sample .. => none
  else none

def tokenFor (state : State graph) : PhaseKey graph → Option (PhaseKey graph)
  | .source event kind =>
      if state.activePhase? event = some kind then some (.source event kind) else none
  | .reporting => if state.status ≠ .running ∧ state.report.isNone then
      some .reporting else none

def timely (runtime : Runtime graph) (state : State graph) (phase : PhaseKey graph) : Bool :=
  state.publicView.timely runtime phase

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

/-- Carried certificates concern immutable catalogue meanings, independently
of call acceptance, readiness, or which binding handle was selected. -/
def Certificate.Holds : Certificate graph → State graph → Prop
  | .source fact, state => fact.Holds state.source
  | .decision fact, state => state.decisions.lookup fact.handle = .openable fact.raw

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
    (acceptDecision state event handle id).publicView.enteredAt? (.source event .opening) =
      some state.source.clock := by
  simp [acceptDecision, State.publicView, PublicView.enteredAt?, Function.update]

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

/-- Terminal classification never modifies either commitment catalogue. -/
theorem State.finish_catalogues (state : State graph) :
    state.finish.source.candidates = state.source.candidates ∧
      state.finish.decisions = state.decisions := by
  unfold State.finish
  split <;> exact ⟨rfl, rfl⟩

/-- Private registration preserves every already fixed original meaning. -/
theorem submit_source_fixed (state : State graph) (who : Principal Player)
    (submission : Submission graph) (handle : Handle graph)
    (fixed : state.source.candidates.lookup handle ≠ .fresh) :
    (submit state who submission).source.candidates.lookup handle =
      state.source.candidates.lookup handle := by
  cases submission with
  | report ids => rfl
  | gameplay material =>
      cases who with
      | watcher => rfl
      | player who =>
          cases call : material.call with
          | binding event selected =>
              let original : EventGraphRuntime.Submission graph :=
                ⟨.commitment event selected, material.material⟩
              have registered : (original.register state.source who).candidates.lookup handle =
                  state.source.candidates.lookup handle := by
                rw [original.register_eq]
                cases original.registrationCommand who with
                | none => rfl
                | some command =>
                    exact EventGraphRuntime.privateStep_lookup_of_not_fresh
                      state.source who command handle fixed
              simpa only [submit, call] using
                (EventGraphRuntime.submitStep_lookup_of_not_fresh _ who original.packet
                  handle (by rwa [registered])).trans registered
          | admission event selected =>
              simp only [submit, call]
              split <;> rfl
          | opening event selected raw | giveUp phase | malformed raw => simp [submit, call]

/-- Preparing or exposing another helper cannot rewrite a frozen decision. -/
theorem submit_decision_fixed (state : State graph) (who : Principal Player)
    (submission : Submission graph) (handle : DecisionHandle graph)
    (fixed : state.decisions.lookup handle ≠ .fresh) :
    (submit state who submission).decisions.lookup handle = state.decisions.lookup handle := by
  cases submission with
  | report ids => rfl
  | gameplay material =>
      cases who with
      | watcher => rfl
      | player who =>
          cases call : material.call with
          | admission event selected =>
              simp only [submit, call]
              split
              · cases prepared : material.material with
                | none =>
                    exact state.decisions.lookup_freeze_eq_of_not_fresh handle selected fixed
                | some raw =>
                    have unchanged := state.decisions.lookup_prepare_eq_of_not_fresh
                      handle who selected.2 raw fixed
                    have frozen :=
                      (state.decisions.prepare who selected.2 raw).lookup_freeze_eq_of_not_fresh
                        handle selected (by rwa [unchanged])
                    exact frozen.trans unchanged
              · rfl
          | binding event selected | opening event selected raw | giveUp phase | malformed raw =>
              simp [submit, call]

/-- Every accepted opening appends one source completion. Authentic original
evidence and the graph association invariant make it a legal source step. -/
theorem openDecision_complete (state next : State graph) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (handle : DecisionHandle graph) (raw : Raw L) (certificates : List (Certificate graph))
    (accepted : openDecision state event ready owner payload binding checks outputEq
      handle raw certificates = some next) :
    ∃ (disclose : Bool) (result : PublicationResult (L.Val payload)),
      next = { state with
        source := state.source.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) disclose)
          (cast (congrArg EventField.Value outputEq.symm) result) } ∧
        (state.source.BindingInvariant →
          (∀ fact ∈ certificates, fact.Holds state) →
          state.source.config.step event ready
            (cast (congrArg EventField.Action outputEq.symm) disclose) =
              PMF.pure next.source.config) := by
  unfold openDecision at accepted
  simp only [Option.bind_eq_bind, Option.pure_def] at accepted
  cases decoded : raw.as? (R.result payload) with
  | none => simp [decoded] at accepted
  | some encoded =>
      simp only [decoded, Option.bind_some] at accepted
      cases decision : R.valueEquiv payload encoded with
      | failure =>
          simp only [decision] at accepted
          split at accepted
          · simp only [Option.some.injEq] at accepted
            subst next
            refine ⟨false, .failure, rfl, fun _ _ => ?_⟩
            exact failure_source_step state event ready owner payload binding checks outputEq codeEq
          · simp at accepted
      | success value =>
          simp only [decision] at accepted
          cases original : state.source.accepted binding.field with
          | none => simp [original] at accepted
          | some selected =>
              simp only [original, Option.bind_some] at accepted
              split at accepted
              · rename_i exactCertificates
                cases verdict : GuardCheck.allAccepted? checks
                    (graph.publicStore state.source.config.store) (.success value) with
                | none => simp [verdict] at accepted
                | some passed =>
                    cases passed with
                    | false => simp [verdict] at accepted
                    | true =>
                        simp only [verdict, Option.bind_some, ↓reduceIte,
                          Option.some.injEq] at accepted
                        subst next
                        refine ⟨true, .success value, rfl, fun valid certified => ?_⟩
                        have opened : state.source.candidates.lookup selected =
                            .openable ⟨payload, value⟩ :=
                          certified (.source ⟨selected, ⟨payload, value⟩⟩)
                            (by simp [exactCertificates])
                        have stored := valid.toAssociationInvariant.opening_stored binding selected
                          value original opened
                        simpa only [ite_true] using success_source_step state event ready owner
                          payload binding checks outputEq codeEq value true stored verdict
              · simp at accepted

/-- Accepted calls preserve all fixed meanings; binding can only freeze a
fresh original candidate, and no handler changes the helper catalogue. -/
theorem handleGame_preserves (runtime : Runtime graph) (state next : State graph)
    (id : MessageId (Principal Player)) (packet : GamePacket graph)
    (accepted : handleGame runtime state id packet = some next) :
    next.decisions = state.decisions ∧
      (∀ handle : Handle graph, state.source.candidates.lookup handle ≠ .fresh →
        next.source.candidates.lookup handle = state.source.candidates.lookup handle) ∧
      (state.source.BindingInvariant → next.source.BindingInvariant) ∧
      (∀ inputs, state.source.Invariant inputs → state.source.BindingInvariant →
        (∀ fact ∈ packet.certificates, fact.Holds state) → next.source.Invariant inputs) := by
  rcases packet with ⟨call, certificates, token⟩
  cases call with
  | binding event selected =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind, Option.bind_some,
        Option.pure_def] at accepted
      split at accepted
      · split at accepted
        · rename_i ready
          cases view : nodeView graph event with
          | bind owner payload outputEq codeEq =>
              simp only [view] at accepted
              split at accepted
              · rename_i allowed
                cases Option.some.inj accepted
                refine ⟨(State.finish_catalogues _).2, (fun handle fixed => ?_), ?_, ?_⟩
                · rw [(State.finish_catalogues _).1]
                  exact state.source.candidates.lookup_freeze_eq_of_not_fresh handle selected fixed
                · intro valid
                  rw [State.finish_source]
                  exact valid.acceptBinding event ready owner payload outputEq selected
                    allowed.2.1 allowed.2.2.2.2
                · intro inputs valid _ _
                  rw [State.finish_source]
                  have step := EventGraphRuntime.bind_complete_mem_step state.source event ready
                    owner payload outputEq codeEq (state.source.bindingResult selected payload)
                  exact (valid.refreshStep event ready _ _ step).copy rfl rfl rfl
              · cases accepted
          | sample | resolve => simp [view] at accepted
        · cases accepted
      · cases accepted
  | admission event selected =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · cases view : nodeView graph event with
        | resolve owner payload binding checks outputEq codeEq =>
            simp only [view] at accepted
            split at accepted
            · cases Option.some.inj accepted
              exact ⟨rfl, (fun _ _ => rfl), (fun valid => valid), fun _ valid _ _ => valid⟩
            · cases accepted
        | bind | sample => simp [view] at accepted
      · cases accepted
  | opening event selected raw =>
      simp only [handleGame, Call.phase?, Option.bind_eq_bind, Option.bind_some] at accepted
      split at accepted
      · split at accepted
        · rename_i ready
          cases view : nodeView graph event with
          | resolve owner payload binding checks outputEq codeEq =>
              simp only [view] at accepted
              split at accepted
              · simp only [Option.pure_def] at accepted
                cases opened : openDecision state event ready owner payload binding checks
                    outputEq selected raw certificates with
                | none => simp [opened] at accepted
                | some executed =>
                    simp only [opened, Option.bind_some, Option.some.injEq] at accepted
                    subst next
                    obtain ⟨disclose, result, rfl, sourceStep⟩ := openDecision_complete state
                      executed event ready owner payload binding checks outputEq codeEq
                      selected raw certificates opened
                    refine ⟨(State.finish_catalogues _).2, (fun _ _ => ?_), ?_, ?_⟩
                    · rw [(State.finish_catalogues _).1]
                      rfl
                    · intro valid
                      rw [State.finish_source]
                      exact valid.complete_nonbinding event ready _ _ (by
                        intro owner payload
                        rw [outputEq]
                        simp)
                    · intro inputs valid association certified
                      rw [State.finish_source]
                      have step := sourceStep association certified
                      have member :
                          (state.source.complete event ready
                            (cast (congrArg EventField.Action outputEq.symm) disclose)
                            (cast (congrArg EventField.Value outputEq.symm) result)).config ∈
                          (state.source.config.step event ready
                            (cast (congrArg EventField.Action outputEq.symm)
                              disclose)).support := by
                        rw [step]
                        exact (PMF.mem_support_pure_iff _ _).mpr rfl
                      exact (valid.refreshStep event ready _ _ member).copy rfl rfl rfl
              · cases accepted
          | bind | sample => simp [view] at accepted
        · cases accepted
      · cases accepted
  | giveUp phase =>
      cases phase with
      | reporting => simp [handleGame, Call.phase?] at accepted
      | source event kind =>
          simp only [handleGame, Call.phase?, Option.bind_eq_bind, Option.bind_some] at accepted
          split at accepted
          · cases view : nodeView graph event with
            | bind owner payload outputEq codeEq
            | resolve owner payload binding checks outputEq codeEq =>
                simp only [view] at accepted
                split at accepted
                · cases Option.some.inj accepted
                  exact ⟨rfl, (fun _ _ => rfl), (fun valid => valid), fun _ valid _ _ => valid⟩
                · cases accepted
            | sample => simp [view] at accepted
          · cases accepted
  | malformed raw => simp [handleGame, Call.phase?] at accepted

theorem handle_preserves (runtime : Runtime graph) (state next : State graph)
    (message : Message (Principal Player) (Packet graph))
    (accepted : handle runtime state message = some next) :
    next.decisions = state.decisions ∧
      (∀ handle : Handle graph, state.source.candidates.lookup handle ≠ .fresh →
        next.source.candidates.lookup handle = state.source.candidates.lookup handle) ∧
      (state.source.BindingInvariant → next.source.BindingInvariant) ∧
      (∀ inputs, state.source.Invariant inputs → state.source.BindingInvariant →
        (∀ fact ∈ message.payload.certificates, fact.Holds state) →
        next.source.Invariant inputs) := by
  cases packet : message.payload with
  | gameplay game =>
      simpa only [packet, Packet.certificates] using handleGame_preserves runtime state next
        message.id game (by simpa only [handle, packet] using accepted)
  | report evidence token =>
      simp only [handle, packet] at accepted
      split at accepted
      · cases Option.some.inj accepted
        exact ⟨rfl, (fun _ _ => rfl), (fun valid => valid), fun _ valid _ _ => valid⟩
      · cases accepted

/-- Source sampling, clock movement, cancellation and reporting preserve both
catalogues, including before any gameplay outcome exists. -/
theorem environment_preserves (runtime : Runtime graph) (state next : State graph)
    (command : EnvironmentCommand graph)
    (reached : next ∈ (environment runtime state command).support) :
    next.source.candidates = state.source.candidates ∧ next.decisions = state.decisions ∧
      (state.source.BindingInvariant → next.source.BindingInvariant) ∧
      (∀ inputs, state.source.Invariant inputs → next.source.Invariant inputs) := by
  cases command with
  | advanceClock =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      refine ⟨rfl, rfl, (fun valid =>
        valid.copy rfl rfl rfl), ?_⟩
      intro inputs valid
      refine ⟨valid.reachable, valid.activated_iff, ?_⟩
      intro event entered activated
      have := valid.activated_le event entered activated
      change entered ≤ state.source.clock + 1
      omega
  | expire phase =>
      simp only [environment, PMF.mem_support_pure_iff _ _] at reached
      subst next
      split
      · cases phase <;> exact ⟨rfl, rfl, (fun valid => valid), fun _ valid => valid⟩
      · exact ⟨rfl, rfl, (fun valid => valid), fun _ valid => valid⟩
  | executeSample event =>
      simp only [environment] at reached
      split at reached
      · obtain ⟨source, sampled, rfl⟩ := PMF.support_map .. ▸ reached
        have preserved : source.candidates = state.source.candidates ∧
            (state.source.BindingInvariant → source.BindingInvariant) ∧
            (∀ inputs, state.source.Invariant inputs → source.Invariant inputs) := by
          unfold EventGraphRuntime.executeSample at sampled
          split at sampled
          · rename_i ready
            cases view : nodeView graph event with
            | sample payload law outputEq codeEq =>
                simp only [view] at sampled
                obtain ⟨config, step, rfl⟩ := PMF.support_map .. ▸ sampled
                refine ⟨rfl, (fun valid => ?_), ?_⟩
                · exact EventGraphRuntime.bindingInvariant_of_nonbinding_step valid event ready
                    _ step rfl rfl (by
                      intro owner payload
                      rw [outputEq]
                      simp)
                · exact fun _ valid => valid.refreshStep event _ _ config step
            | bind | resolve =>
                simp only [view, PMF.mem_support_pure_iff _ _] at sampled
                subst source
                exact ⟨rfl, (fun valid => valid), fun _ valid => valid⟩
          · cases (PMF.mem_support_pure_iff _ _).mp sampled
            exact ⟨rfl, (fun valid => valid), fun _ valid => valid⟩
        refine ⟨(State.finish_catalogues _).1.trans preserved.1,
          (State.finish_catalogues _).2, ?_, ?_⟩
        · rw [State.finish_source]
          exact preserved.2.1
        · rw [State.finish_source]
          exact preserved.2.2
      · cases (PMF.mem_support_pure_iff _ _).mp reached
        exact ⟨rfl, rfl, (fun valid => valid), fun _ valid => valid⟩

omit [DecidableEq Player] in
/-- Authentication of a report preserves every certificate carried by a
nested signed envelope, including a rejected player report. -/
theorem Packet.nested_certificate (packet : Packet graph)
    (message : Message (Principal Player) (Packet graph))
    (member : message ∈ packet.nestedEnvelopes) (fact : Certificate graph)
    (certified : fact ∈ message.payload.certificates) : fact ∈ packet.certificates := by
  cases shape : packet with
  | gameplay game => simp only [shape, nestedEnvelopes, List.not_mem_nil] at member
  | report evidence token =>
      simp only [shape, nestedEnvelopes] at member
      obtain ⟨parent, present, nested⟩ := List.mem_flatMap.mp member
      simp only [certificates]
      apply List.mem_flatMap.mpr
      refine ⟨parent, present, ?_⟩
      rcases List.mem_cons.mp nested with same | descendant
      · subst message
        exact certified
      · exact parent.payload.nested_certificate message descendant fact certified
termination_by sizeOf packet
decreasing_by
  rw [shape]
  simp_wf
  have member := List.sizeOf_lt_of_mem present
  have fields : sizeOf parent = 1 + sizeOf parent.id + sizeOf parent.payload := by
    cases parent
    rfl
  omega

omit [DecidableEq Player] in
theorem Packet.envelope_certificate (packet : Packet graph)
    (id : MessageId (Principal Player)) (message : Message (Principal Player) (Packet graph))
    (member : message ∈ packet.envelopes id) (fact : Certificate graph)
    (certified : fact ∈ message.payload.certificates) : fact ∈ packet.certificates := by
  unfold envelopes at member
  rcases List.mem_cons.mp member with same | nested
  · subst message
    exact certified
  · cases packet with
    | gameplay game => exact (List.not_mem_nil nested).elim
    | report evidence token =>
        exact (Packet.report evidence token).nested_certificate message nested fact certified

theorem certificateFor_sound (state : State graph) (who : Principal Player)
    (known : List (Message (Principal Player) (Packet graph)))
    (received : ∀ message ∈ known, ∀ fact ∈ message.payload.certificates, fact.Holds state)
    (request : CertificateRequest graph) (fact : Certificate graph)
    (issued : certificateFor state who known request = some fact) : fact.Holds state := by
  cases request with
  | owned certificate =>
      cases certificate with
      | source original =>
          simp only [certificateFor] at issued
          split at issued
          · rename_i verified
            cases Option.some.inj issued
            exact (CommitmentCandidates.verify_eq_true_iff _ _ _).mp verified.2
          · cases issued
      | decision decision =>
          simp only [certificateFor] at issued
          split at issued
          · rename_i verified
            cases Option.some.inj issued
            exact (CommitmentCandidates.verify_eq_true_iff _ _ _).mp verified.2
          · cases issued
  | forward id index =>
      simp only [certificateFor] at issued
      cases found : known.find? (fun message => message.id = id) with
      | none => simp [found] at issued
      | some message =>
          simp only [found, Option.bind_some] at issued
          obtain ⟨within, equal⟩ := List.getElem?_eq_some_iff.mp issued
          exact received message (List.mem_of_find?_eq_some found) fact
            (equal ▸ List.getElem_mem within)

/-- Owned issuance and forwarding are sound even when the surrounding call
is rejected or sent outside its gameplay phase. -/
theorem emit_sound (state : State graph) (who : Principal Player)
    (known : List (Message (Principal Player) (Packet graph))) (submission : Submission graph)
    (received : ∀ message ∈ known, ∀ fact ∈ message.payload.certificates, fact.Holds state)
    (fact : Certificate graph) (issued : fact ∈ (emit state who known submission).certificates) :
    fact.Holds state := by
  cases submission with
  | gameplay material =>
      simp only [emit, Packet.certificates] at issued
      obtain ⟨request, _, certified⟩ := List.mem_filterMap.mp issued
      exact certificateFor_sound state who known received request fact certified
  | report ids =>
      simp only [emit, Packet.certificates] at issued
      obtain ⟨message, reported, certified⟩ := List.mem_flatMap.mp issued
      obtain ⟨original, present, authentic⟩ :=
        emit_report_origin state who known ids _ _ rfl message reported
      exact received original present fact
        (original.payload.envelope_certificate original.id message authentic fact certified)

/-- Both opening capabilities persist through arbitrary raw continuations. -/
theorem certificateInvariant (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (fact : Certificate graph) : (application runtime leaks).Invariant fact.Holds where
  submit state who material valid := by
    cases fact with
    | source original =>
        exact (submit_source_fixed state who material original.handle
          (by rw [valid]; simp)).trans valid
    | decision decision =>
        exact (submit_decision_fixed state who material decision.handle
          (by rw [valid]; simp)).trans valid
  handle state message next valid accepted := by
    have tables := handle_preserves runtime state next message accepted
    cases fact with
    | source original =>
        exact (tables.2.1 original.handle (by rw [valid]; simp)).trans valid
    | decision decision =>
        change next.decisions.lookup decision.handle = .openable decision.raw
        rw [tables.1]
        exact valid
  environment state command next valid reached := by
    have tables := environment_preserves runtime state next command reached
    cases fact with
    | source original =>
        change next.source.candidates.lookup original.handle = .openable original.raw
        rw [tables.1]
        exact valid
    | decision decision =>
        change next.decisions.lookup decision.handle = .openable decision.raw
        rw [tables.2.1]
        exact valid

/-- Private registration and exposure preserve the existing graph binding
association invariant, including arbitrary and rejected submissions. -/
theorem submit_bindingInvariant (state : State graph) (who : Principal Player)
    (submission : Submission graph) (valid : state.source.BindingInvariant) :
    (submit state who submission).source.BindingInvariant := by
  cases submission with
  | report ids => exact valid
  | gameplay material =>
      cases who with
      | watcher => exact valid
      | player who =>
          cases call : material.call with
          | binding event selected =>
              let original : EventGraphRuntime.Submission graph :=
                ⟨.commitment event selected, material.material⟩
              have registered : (original.register state.source who).BindingInvariant := by
                rw [original.register_eq]
                cases original.registrationCommand who with
                | none => exact valid
                | some command =>
                    exact EventGraphRuntime.privateStep_bindingInvariant _ valid who command
              simpa only [submit, call] using
                EventGraphRuntime.submitStep_bindingInvariant _ registered who original.packet
          | admission event selected =>
              simp only [submit, call]
              split <;> exact valid
          | opening event selected raw | giveUp phase | malformed raw =>
              simpa only [submit, call] using valid

/-- The source component retains its accepted-handle meaning at every native
history through the generic application-invariant framework. -/
theorem bindingInvariant (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph)) :
    (application runtime leaks).Invariant (fun state => state.source.BindingInvariant) where
  submit := submit_bindingInvariant
  handle state message next valid accepted :=
    (handle_preserves runtime state next message accepted).2.2.1 valid
  environment state command next valid reached :=
    (environment_preserves runtime state next command reached).2.2.1 valid

/-- Private submissions retain the source configuration, clock and readiness
metadata used by the existing source-runtime invariant. -/
theorem submit_invariant (state : State graph) (who : Principal Player)
    (submission : Submission graph) {inputs : graph.Inputs}
    (valid : state.source.Invariant inputs) :
    (submit state who submission).source.Invariant inputs :=
  valid.copy (submit_config state who submission)
    (congrArg (fun view => view.source.clock) (submit_publicView state who submission))
    (congrArg (fun view => view.source.activatedAt) (submit_publicView state who submission))

/-- The generic evidence theorem applies to every legal native history,
with arbitrary scheduling, deviations, rejected receipts and partial leaks. -/
def packetEvidence (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph)) :
    (application runtime leaks).PacketEvidence where
  Fact := Certificate graph
  valid state fact := fact.Holds state
  decode := Packet.certificates
  persists := certificateInvariant runtime leaks
  issued := emit_sound

/-- The native execution retains a legal source prefix and valid activation
metadata. The network-evidence premise comes from the actual runner, rather
than a restriction on raw player submissions or scheduler inclusions. -/
theorem sourceServiceInvariant (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (inputs : PMF graph.Inputs) (scheduler : (application runtime leaks).Scheduler) :
    (application runtime leaks).ServiceInvariant scheduler (fun execution =>
      (∃ setup ∈ inputs.support, execution.application.source.Invariant setup) ∧
        execution.application.source.BindingInvariant ∧
        (packetEvidence runtime leaks).Sound execution) where
  respond execution who action valid := by
    obtain ⟨⟨setup, supported, legal⟩, association, sound⟩ := valid
    refine ⟨⟨setup, supported, ?_⟩,
      (bindingInvariant runtime leaks).respond execution who action association,
      (packetEvidence runtime leaks).sound_respond execution who action sound⟩
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact legal
    | some material => exact submit_invariant execution.application who material legal
  environment execution next command valid _ reached := by
    obtain ⟨⟨setup, supported, legal⟩, association, sound⟩ := valid
    refine ⟨⟨setup, supported, ?_⟩,
      (bindingInvariant runtime leaks).environmentStep execution next command
        association reached,
      (packetEvidence runtime leaks).sound_environment execution next command sound reached⟩
    cases command with
    | wait =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        exact legal
    | activate who =>
        obtain ⟨updated, learned, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ learned
        exact legal
    | «include» id =>
        simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map] at reached
        cases (PMF.mem_support_pure_iff _ _).mp reached
        unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
        cases found : execution.network.lookup id with
        | none => exact legal
        | some message =>
            change EventGraphRuntime.State.Invariant setup
              ((handle runtime execution.application message).getD execution.application).source
            cases accepted : handle runtime execution.application message with
            | none => exact legal
            | some state =>
                have preserved := handle_preserves runtime execution.application state
                  message accepted
                exact preserved.2.2.2 setup legal association (sound.lookup id message found)
    | application command =>
        obtain ⟨updated, moved, rfl⟩ := PMF.support_map .. ▸ reached
        obtain ⟨state, changed, rfl⟩ := PMF.support_map .. ▸ moved
        have preserved := environment_preserves runtime execution.application state command changed
        exact preserved.2.2.2 setup legal

/-- Every initialized native history has a source configuration reachable from
a supported setup, with exact readiness and bounded activation timestamps.
Cancellation leaves a legal partial prefix; it does not invent a source result.
This theorem asserts semantic legality, not an information or equilibrium lift. -/
theorem history_source_invariant (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (application runtime leaks).Scheduler)
    {state} (trace : ((application runtime leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant (fun state : State graph =>
      ∃ setup ∈ inputs.support, state.source.Invariant setup) state := by
  have preserved := (sourceServiceInvariant runtime leaks inputs scheduler).history
    (inputs.map State.initial) horizon (by
      intro state supported
      obtain ⟨setup, chosen, rfl⟩ := PMF.support_map .. ▸ supported
      refine ⟨⟨setup, chosen, ?_⟩, State.initial_bindingInvariant setup,
        (packetEvidence runtime leaks).sound_initial (State.initial setup)⟩
      change (State.initial setup).source.Invariant setup
      rw [State.initial, State.finish_source]
      exact EventGraphRuntime.State.initial_invariant setup) trace
  cases state with
  | none => trivial
  | some control => exact preserved.1

/-- Authentic original evidence in a pending envelope agrees with the selected
source binding at every initialized history, before or after disclosure. No
honesty, successful handling, inclusion or observer-completeness is assumed. -/
theorem history_opening_stored (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (inputs : graph.Inputs) (horizon : Nat) (scheduler : (application runtime leaks).Scheduler)
    (control : (application runtime leaks).Control)
    (trace : ((application runtime leaks).protocol (PMF.pure (State.initial inputs))
      horizon scheduler).Trace (some control))
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload)) (original : Handle graph)
    (value : L.Val payload) (message : Message (Principal Player) (Packet graph))
    (found : control.execution.network.lookup message.id = some message)
    (certified : Certificate.source ⟨original, ⟨payload, value⟩⟩ ∈ message.payload.certificates)
    (associated : control.execution.application.source.accepted binding.field = some original) :
    binding.get? control.execution.application.source.config.store = some (.success value) := by
  have valid : control.execution.application.source.BindingInvariant :=
    (bindingInvariant runtime leaks).history (PMF.pure (State.initial inputs)) horizon scheduler
      (fun state supported => by
        cases (PMF.mem_support_pure_iff _ _).mp supported
        exact State.initial_bindingInvariant inputs) trace
  have sound : (packetEvidence runtime leaks).Sound control.execution :=
    (packetEvidence runtime leaks).history_sound _ horizon scheduler trace
  exact valid.toAssociationInvariant.opening_stored binding original value associated
    (sound.lookup message.id message found _ certified)

end Vegas.SourceSession
