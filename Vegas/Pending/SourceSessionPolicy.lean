/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.SourceSession
import Vegas.EventGraph.ResolutionProvenance
import Interaction.ReactiveAuthorization
import Vegas.Pending.ReactivePolicy

/-! # Frozen resolution submissions and original private recall

Admission evaluates the source resolution from the owner's projected store and
freezes its effective value. Opening reads the immutable helper candidate, never
resamples the source policy. The original intention is recovered from the actual
admission submission identified by its receipt; it is absent from wire packets.
The client restores the chronological own-action list before sampling a source
policy, sends at most once per phase, and opens without another source choice.
Whole-service observation correspondence and sequential-equilibrium transport
remain separate obligations.
-/

noncomputable section

namespace Vegas.SourceSession

open Interaction GameTheory.Math.Probability EventGraph
open EventGraphRuntime (Raw Handle nodeView)

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [R : IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Choose the effective source result once, retaining the original Boolean
only in private action recall. Unavailable observations produce genuine FALSE. -/
def resolutionAdmission (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (intention : Bool)
    (observation : graph.PlayerObservation owner) : GameSubmission graph where
  call := .admission event (owner, event)
  material := some (encodeDecision payload
    ((EventCode.resolveOutput? binding checks intention observation.store).getD .failure))
  certificates := []
  resolutionIntent := some intention

/-- A fixed FALSE carries only its helper certificate. A fixed TRUE also
requests the owned opening of the selected original binding. -/
def resolutionOpening (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (accepted : graph.Field → Option (Handle graph))
    (decision : PublicationResult (L.Val payload)) : Option (GameSubmission graph) :=
  let raw := encodeDecision payload decision
  let base : GameSubmission graph := {
    call := .opening event (owner, event) raw
    material := none
    certificates := [.owned (.decision ⟨(owner, event), raw⟩)] }
  match decision with
  | .failure => some base
  | .success value => do
      let original ← accepted binding.field
      if original.1 = owner then
        some { base with certificates := base.certificates ++
          [.owned (.source ⟨original, ⟨payload, value⟩⟩)] }
      else none

/-- The mandatory opening is read from the owner's immutable helper table,
with no source-policy argument and no new choice of TRUE or FALSE. -/
def frozenResolutionOpening (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (accepted : graph.Field → Option (Handle graph))
    (candidates : graph.EventId → CommitmentCandidate (Raw L)) :
    Option (GameSubmission graph) :=
  match candidates event with
  | .openable raw => do
      let encoded ← raw.as? (R.result payload)
      resolutionOpening owner event payload binding accepted (R.valueEquiv payload encoded)
  | .fresh | .unopenable => none

/-- Recover an intention only from a canonical admission computed from the
original owner's view. A raw private claim, absent source value, or already
fixed helper cannot replace the source action recorded by its opening. -/
def checkedResolutionIntent? (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (entry : (application runtime leaks).PlayerEntry) (event : graph.EventId) : Option Bool :=
  match entry.beforeView.application, entry.action.transmission, nodeView graph event with
  | .player who _ observation _ helpers, some (.gameplay material),
      .resolve owner payload binding checks _ _ => do
      let intention ← material.resolutionIntent
      if owner = who ∧ material.call = .admission event (owner, event) ∧
          helpers event = .fresh then
        let decision ← EventCode.resolveOutput? binding checks intention observation.store
        if material.material = some (encodeDecision payload decision) then some intention else none
      else none
  | _, _, _ => none

/-- Use the existing submission-origin predicate on the owner's actual recall.
The receipt selects an emitted identifier, rather than an intention guessed
from a public FALSE opening. -/
def recalledResolutionIntent (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (past : List (application runtime leaks).PlayerEntry) (event : graph.EventId)
    (id : MessageId (Principal Player)) : Option Bool := do
  let entry ← past.find? fun entry => entry.submitsId (application runtime leaks) id
  checkedResolutionIntent? runtime leaks entry event

/-- Restore only owned resolution actions whose admission has an actual private
submission origin. Source observations continue to use the original own-action
carrier; public fields and foreign intentions are untouched. -/
def restoreResolutionCompletion (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (past : List (application runtime leaks).PlayerEntry)
    (receipts : PhaseKey graph → Option (MessageId (Principal Player)))
    (completion : graph.Completion) : graph.Completion :=
  match nodeView graph completion.event with
  | .resolve owner _ _ _ outputEq _ =>
      if owner = who then
        match receipts (.source completion.event .admission) with
        | some id => if id.1 = .player who then
            match recalledResolutionIntent runtime leaks past completion.event id with
            | some intention => ⟨completion.event,
                cast (congrArg EventField.Action outputEq.symm) intention⟩
            | none => completion
          else completion
        | none => completion
      else completion
  | .bind .. | .sample .. => completion

/-- Restore the complete own-action list without reconstructing intentions
from public results or exposing foreign private recall. -/
def restoreObservation (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (past : List (application runtime leaks).PlayerEntry)
    (receipts : PhaseKey graph → Option (MessageId (Principal Player)))
    (observation : graph.PlayerObservation who) : graph.PlayerObservation who :=
  { observation with
    ownActions := observation.ownActions.map
      (restoreResolutionCompletion runtime leaks who past receipts) }

/-- One source event may require admission and opening, with a distinct
authored identifier for each. Only actual emitted envelopes count. -/
def alreadySubmitted (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (past : List (application runtime leaks).PlayerEntry) (phase : PhaseKey graph) : Bool :=
  past.any fun entry => entry.emitted.any fun message => match message.payload with
    | .gameplay packet => packet.call.phase? = some phase
    | .report _ _ => false

/-- Compile a source choice at binding or admission. The existing fresh-slot
selector is shared with the graph runtime; resolution evaluates the owner's
projected source store and records the original Boolean privately. -/
def sourceDecision (who : Player) (event : graph.EventId) (action : graph.Action event)
    (publicView : PublicView graph) (observation : graph.PlayerObservation who)
    (candidates : EventGraphRuntime.CandidateSlot graph → CommitmentCandidate (Raw L)) :
    Option (GameSubmission graph) :=
  match nodeView graph event with
  | .sample .. => none
  | .bind _ payload outputEq _ =>
      (EventGraphRuntime.reactiveFreshSlot ⟨who, publicView.source, observation, candidates⟩).map
        fun serial => {
          call := .binding event (who, .prepared serial)
          material := match (cast (congrArg EventField.Action outputEq) action :
              PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩
          certificates := [] }
  | .resolve owner payload binding checks outputEq _ =>
      if owned : owner = who then
        some (resolutionAdmission owner event payload binding checks
          (cast (congrArg EventField.Action outputEq) action) (owned.symm ▸ observation))
      else none

/-- A ready owner's first response samples its source choice at binding or
admission. Opening uses only the admitted fixed helper. Deadline checks and
submission suppression are scoped to the current phase. -/
def prescribedResponse (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (past : List (application runtime leaks).PlayerEntry)
    (publicView : PublicView graph) (observation : graph.PlayerObservation who)
    (candidates : EventGraphRuntime.CandidateSlot graph → CommitmentCandidate (Raw L))
    (helpers : graph.EventId → CommitmentCandidate (Raw L)) :
    PMF (application runtime leaks).Action :=
  if publicView.status = .running then
    match publicView.source.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if actor : graph.actor? event = some who then
          let recalled := restoreObservation runtime leaks who past publicView.receipts observation
          let decideAt (phase : PhaseKey graph) : PMF (application runtime leaks).Action :=
            if alreadySubmitted runtime leaks past phase || !publicView.timely runtime phase then
              PMF.pure ⟨none⟩
            else (graph.normalizePolicy who policy event actor recalled).map fun action =>
              ⟨(sourceDecision who event action publicView recalled candidates).map
                Submission.gameplay⟩
          match nodeView graph event with
          | .sample .. => PMF.pure ⟨none⟩
          | .bind .. => decideAt (.source event .binding)
          | .resolve owner payload binding _ _ _ =>
              match publicView.admissions event with
              | none => decideAt (.source event .admission)
              | some accepted =>
                  if owner = who then
                    if alreadySubmitted runtime leaks past (.source event .opening) ||
                        !publicView.timely runtime (.source event .opening) ||
                        decide (accepted.handle ≠ (owner, event)) then PMF.pure ⟨none⟩
                    else PMF.pure ⟨(frozenResolutionOpening owner event payload binding
                      publicView.source.accepted helpers).map Submission.gameplay⟩
                  else PMF.pure ⟨none⟩
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

/-- The native source policy reads only the activated player's actual view
and private recall. Watcher and mismatched observations cannot drive gameplay. -/
def prescribedPolicy (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (policy : graph.BehavioralPolicy who) :
    (application runtime leaks).Policy := fun past view =>
  match view.application with
  | .watcher _ => PMF.pure ⟨none⟩
  | .player owner publicView observation candidates helpers =>
      if owned : owner = who then
        prescribedResponse runtime leaks who policy past publicView (owned ▸ observation)
          candidates helpers
      else PMF.pure ⟨none⟩

/-- Whole observation restoration uses precisely the same projected store and
completion order. Equality of all restored own actions supplies the last field. -/
theorem restoreObservation_eq (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (past : List (application runtime leaks).PlayerEntry)
    (receipts : PhaseKey graph → Option (MessageId (Principal Player)))
    (observation expected : graph.PlayerObservation who)
    (order : observation.completionOrder = expected.completionOrder)
    (store : observation.store = expected.store)
    (actions : observation.ownActions.map
      (restoreResolutionCompletion runtime leaks who past receipts) = expected.ownActions) :
    restoreObservation runtime leaks who past receipts observation = expected :=
  PlayerObservation.ext graph order store actions

/-- On a genuine activation, the compiler receives the actual private recall
and owner-local catalogues supplied by the pending runner. -/
theorem prescribedPolicy_observe (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (execution : (application runtime leaks).Execution) :
    prescribedPolicy runtime leaks who policy (execution.recall (.player who))
        (execution.observe (application runtime leaks) (.player who)) =
      prescribedResponse runtime leaks who policy (execution.recall (.player who))
        execution.application.publicView
        (graph.playerObserve who execution.application.source.config)
        (fun slot => execution.application.source.candidates.lookup (who, slot))
        (fun event => execution.application.decisions.lookup (who, event)) := by
  simp [prescribedPolicy, ReactiveApplication.Execution.observe, application]

/-- Admission samples the source law using the whole restored observation. -/
theorem prescribedResponse_admission (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (past : List (application runtime leaks).PlayerEntry)
    (view : PublicView graph) (observation : graph.PlayerObservation who)
    (candidates : EventGraphRuntime.CandidateSlot graph → CommitmentCandidate (Raw L))
    (helpers : graph.EventId → CommitmentCandidate (Raw L))
    (event : graph.EventId) (actor : graph.actor? event = some who) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding who payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve who payload binding checks)
    (running : view.status = .running) (turn : view.source.ownTurn? who = some event)
    (missing : view.admissions event = none)
    (unsent : alreadySubmitted runtime leaks past (.source event .admission) = false)
    (timely : view.timely runtime (.source event .admission) = true) :
    prescribedResponse runtime leaks who policy past view observation candidates helpers =
      (graph.normalizePolicy who policy event actor
        (restoreObservation runtime leaks who past view.receipts observation)).map fun action =>
          ⟨(sourceDecision who event action view
            (restoreObservation runtime leaks who past view.receipts observation)
            candidates).map Submission.gameplay⟩ := by
  simp [prescribedResponse, running, turn, actor,
    EventGraphRuntime.nodeView_eq_resolve outputEq codeEq, missing, unsent, timely]

/-- Opening does not sample a source law, even one whose future decisions
depend on private recall. Its only possible payload reads the fixed helper. -/
theorem prescribedResponse_opening (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (policy : graph.BehavioralPolicy who)
    (past : List (application runtime leaks).PlayerEntry)
    (view : PublicView graph) (observation : graph.PlayerObservation who)
    (candidates : EventGraphRuntime.CandidateSlot graph → CommitmentCandidate (Raw L))
    (helpers : graph.EventId → CommitmentCandidate (Raw L))
    (event : graph.EventId) (actor : graph.actor? event = some who) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding who payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve who payload binding checks)
    (entered : Nat) (running : view.status = .running)
    (turn : view.source.ownTurn? who = some event)
    (admitted : view.admissions event = some ⟨(who, event), entered⟩)
    (unsent : alreadySubmitted runtime leaks past (.source event .opening) = false)
    (timely : view.timely runtime (.source event .opening) = true) :
    prescribedResponse runtime leaks who policy past view observation candidates helpers =
      PMF.pure ⟨(frozenResolutionOpening who event payload binding view.source.accepted
        helpers).map Submission.gameplay⟩ := by
  simp [prescribedResponse, running, turn, actor,
    EventGraphRuntime.nodeView_eq_resolve outputEq codeEq, admitted, unsent, timely]

/-- A transmitted gameplay envelope suppresses another submission for that
phase through the runner's actual private recall, regardless of inclusion. -/
theorem alreadySubmitted_respond (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution) (who : Player)
    (material : GameSubmission graph) (phase : PhaseKey graph)
    (addressed : material.call.phase? = some phase) :
    alreadySubmitted runtime leaks
      ((execution.respond (application runtime leaks) (.player who)
        ⟨some (.gameplay material)⟩).recall (.player who)) phase = true := by
  simp [alreadySubmitted, ReactiveApplication.Execution.respond, application, emit, addressed,
    MessageNetwork.submit]

theorem resolutionAdmission_fresh (state : State graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (intention : Bool)
    (observation : graph.PlayerObservation owner) (decision : PublicationResult (L.Val payload))
    (fresh : state.decisions.lookup (owner, event) = .fresh)
    (resolved : EventCode.resolveOutput? binding checks intention observation.store =
      some decision) :
    let material := resolutionAdmission owner event payload binding checks intention observation
    (submit state (.player owner) (.gameplay material)).decisions.lookup (owner, event) =
      .openable (encodeDecision payload decision) := by
  simp [submit, resolutionAdmission, resolved, CommitmentCandidates.lookup_freeze_self,
    CommitmentCandidates.lookup_prepare_self, fresh]

/-- Owner projection preserves the source evaluator, including guard failure. -/
theorem resolutionAdmission_source_value (state : State graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (intention : Bool)
    (decision : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks intention state.source.config.store =
      some decision) :
    (resolutionAdmission owner event payload binding checks intention
      (graph.playerObserve owner state.source.config)).material =
        some (encodeDecision payload decision) := by
  simp only [resolutionAdmission]
  change some (encodeDecision payload ((EventCode.resolveOutput? binding checks intention
    (graph.playerStore owner state.source.config.store)).getD .failure)) = _
  rw [EventCode.resolveOutput?_playerStore, resolved]
  rfl

theorem frozenResolutionOpening_encoded (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (accepted : graph.Field → Option (Handle graph))
    (candidates : graph.EventId → CommitmentCandidate (Raw L))
    (decision : PublicationResult (L.Val payload))
    (fixed : candidates event = .openable (encodeDecision payload decision)) :
    frozenResolutionOpening owner event payload binding accepted candidates =
      resolutionOpening owner event payload binding accepted decision := by
  simp [frozenResolutionOpening, fixed, encodeDecision]

/-- A successful source resolution has an authentic owned original capability,
so the TRUE opening constructor is available. -/
theorem resolutionOpening_success_available (state : State graph)
    (valid : state.source.BindingInvariant) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (intention : Bool) (value : L.Val payload)
    (resolved : EventCode.resolveOutput? binding checks intention state.source.config.store =
      some (.success value)) :
    ∃ original material,
      state.source.accepted binding.field = some original ∧ original.1 = owner ∧
      state.source.candidates.lookup original = .openable ⟨payload, value⟩ ∧
      resolutionOpening owner event payload binding state.source.accepted (.success value) =
        some material := by
  obtain ⟨original, selected, owned, meaning⟩ := valid.success_provenance binding value
    (EventCode.binding_success_of_resolve_success binding checks intention
      state.source.config.store value resolved)
  have available : ∃ material, resolutionOpening owner event payload binding
      state.source.accepted (.success value) = some material := by
    simp [resolutionOpening, selected, owned]
  obtain ⟨material, constructed⟩ := available
  exact ⟨original, material, selected, owned, meaning, constructed⟩

/-- The original private intention is present even when effective TRUE became
wire FALSE. Generic submission-origin and freshness facts supply the recall. -/
theorem recalledResolutionIntent_respond (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (execution : (application runtime leaks).Execution) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (intention : Bool)
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (decision : PublicationResult (L.Val payload))
    (resolved : EventCode.resolveOutput? binding checks intention
      execution.application.source.config.store = some decision)
    (helperFresh : execution.application.decisions.lookup (owner, event) = .fresh)
    (fresh : execution.submissionOrigin? (application runtime leaks)
      (.player owner, execution.network.nextSerial (.player owner)) = none) :
    recalledResolutionIntent runtime leaks
      ((execution.respond (application runtime leaks) (.player owner) ⟨some (.gameplay
        (resolutionAdmission owner event payload binding checks intention
          (graph.playerObserve owner execution.application.source.config)))⟩).recall
        (.player owner)) event
      (.player owner, execution.network.nextSerial (.player owner)) = some intention := by
  let observation := graph.playerObserve owner execution.application.source.config
  have localResolved : EventCode.resolveOutput? binding checks intention observation.store =
      some decision := by
    simpa only [observation, playerObserve, EventCode.resolveOutput?_playerStore] using resolved
  let material := resolutionAdmission owner event payload binding checks intention observation
  change ((execution.respond (application runtime leaks) (.player owner)
    ⟨some (.gameplay material)⟩).submissionOrigin? (application runtime leaks)
      (.player owner, execution.network.nextSerial (.player owner))).bind
        (fun entry => checkedResolutionIntent? runtime leaks entry event) = _
  rw [(application runtime leaks).submissionOrigin_submit execution (.player owner) _ fresh]
  suffices normalized : ((EventCode.resolveOutput? binding checks intention
      (graph.playerObserve owner execution.application.source.config).store).bind fun result =>
      if encodeDecision payload decision = encodeDecision payload result then some intention
        else none) = some intention by
    simpa [checkedResolutionIntent?, material, resolutionAdmission,
      ReactiveApplication.Execution.observe, application,
      EventGraphRuntime.nodeView_eq_resolve outputEq codeEq, helperFresh, localResolved]
      using normalized
  change ((EventCode.resolveOutput? binding checks intention observation.store).bind fun result =>
    if encodeDecision payload decision = encodeDecision payload result then some intention
      else none) = some intention
  rw [localResolved]
  simp

theorem restoreResolutionCompletion_original (runtime : Runtime graph)
    (leaks : MessageNetwork.ObservationRule (Principal Player) (Packet graph))
    (who : Player) (past : List (application runtime leaks).PlayerEntry)
    (receipts : PhaseKey graph → Option (MessageId (Principal Player)))
    (completion : graph.Completion) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding who payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout completion.event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes completion.event) = .resolve who payload binding checks)
    (id : MessageId (Principal Player)) (intention : Bool)
    (accepted : receipts (.source completion.event .admission) = some id)
    (owned : id.1 = .player who)
    (origin : recalledResolutionIntent runtime leaks past completion.event id = some intention) :
    restoreResolutionCompletion runtime leaks who past receipts completion =
      ⟨completion.event, cast (congrArg EventField.Action outputEq.symm) intention⟩ := by
  simp [restoreResolutionCompletion, EventGraphRuntime.nodeView_eq_resolve outputEq codeEq,
    accepted, owned, origin]

/-- Certificate materialization issues exactly the prescribed FALSE witness. -/
theorem resolutionOpening_failure_emit (state : State graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (known : List (Message (Principal Player) (Packet graph)))
    (fixed : state.decisions.lookup (owner, event) =
      .openable (encodeDecision payload .failure)) :
    ∃ material,
      resolutionOpening owner event payload binding state.source.accepted .failure =
        some material ∧
      emit (submit state (.player owner) (.gameplay material)) (.player owner) known
          (.gameplay material) = .gameplay {
        call := .opening event (owner, event) (encodeDecision payload .failure)
        certificates := [.decision ⟨(owner, event), encodeDecision payload .failure⟩]
        token := state.tokenFor (.source event .opening) } := by
  refine ⟨_, rfl, ?_⟩
  simp [submit, emit, certificateFor, CommitmentCandidates.verify, fixed,
    Call.phase?]

/-- The TRUE wire contains the fixed helper and the authentic original value,
without using the handler's access to a private binding. -/
theorem resolutionOpening_success_emit (state : State graph) (owner : Player)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (known : List (Message (Principal Player) (Packet graph)))
    (original : Handle graph) (value : L.Val payload)
    (selected : state.source.accepted binding.field = some original) (owned : original.1 = owner)
    (meaning : state.source.candidates.lookup original = .openable ⟨payload, value⟩)
    (fixed : state.decisions.lookup (owner, event) =
      .openable (encodeDecision payload (.success value))) :
    ∃ material,
      resolutionOpening owner event payload binding state.source.accepted (.success value) =
        some material ∧
      emit (submit state (.player owner) (.gameplay material)) (.player owner) known
          (.gameplay material) = .gameplay {
        call := .opening event (owner, event) (encodeDecision payload (.success value))
        certificates := [.decision ⟨(owner, event), encodeDecision payload (.success value)⟩,
          .source ⟨original, ⟨payload, value⟩⟩]
        token := state.tokenFor (.source event .opening) } := by
  let material : GameSubmission graph := {
    call := .opening event (owner, event) (encodeDecision payload (.success value))
    material := none
    certificates := [.owned (.decision ⟨(owner, event), encodeDecision payload (.success value)⟩),
      .owned (.source ⟨original, ⟨payload, value⟩⟩)] }
  refine ⟨material, ?_, ?_⟩
  · simp [resolutionOpening, selected, owned, material]
  · simp [material, submit, emit, certificateFor, CommitmentCandidates.verify, fixed, meaning,
      owned, Call.phase?]

/-- Under the explicit opening authorization and timing premises, the fixed
helper produces an accepted packet and exactly its source completion. -/
theorem frozenResolutionOpening_accepted (runtime : Runtime graph) (state : State graph)
    (valid : state.source.BindingInvariant) (owner : Player) (event : graph.EventId)
    (ready : state.source.config.cut.Ready event) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (intention : Bool) (decision : PublicationResult (L.Val payload))
    (known : List (Message (Principal Player) (Packet graph))) (serial : Nat)
    (resolved : EventCode.resolveOutput? binding checks intention state.source.config.store =
      some decision)
    (fixed : state.decisions.lookup (owner, event) =
      .openable (encodeDecision payload decision))
    (authorized : state.tokenFor (.source event .opening) = some (.source event .opening))
    (timely : state.timely runtime (.source event .opening) = true)
    (admitted : (state.admissions event).map Admission.handle = some (owner, event)) :
    let disclose := match decision with | .failure => false | .success _ => true
    ∃ material next,
      frozenResolutionOpening owner event payload binding state.source.accepted
        (fun event => state.decisions.lookup (owner, event)) = some material ∧
      handle runtime state ⟨(.player owner, serial),
        emit (submit state (.player owner) (.gameplay material)) (.player owner) known
          (.gameplay material)⟩ = some next ∧
      next.source.config = (state.source.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm) decision)).config := by
  have viewed := EventGraphRuntime.nodeView_eq_resolve outputEq codeEq
  cases decision with
  | failure =>
      obtain ⟨material, constructed, wire⟩ := resolutionOpening_failure_emit state owner event
        payload binding known fixed
      let next := State.finish ({ state with
        source := state.source.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) false)
          (cast (congrArg EventField.Value outputEq.symm) PublicationResult.failure) }.record
            (.source event .opening) (.player owner, serial))
      refine ⟨material, next, ?_, ?_, ?_⟩
      · rw [frozenResolutionOpening_encoded owner event payload binding state.source.accepted
          (fun selected => state.decisions.lookup (owner, selected)) .failure fixed]
        exact constructed
      · rw [wire]
        simp [handle, handleGame, Call.phase?, authorized, timely, ready, viewed, admitted,
          openDecision_failure, next]
      · rw [State.finish_source]
        rfl
  | success value =>
      obtain ⟨original, selected, owned, meaning⟩ := valid.success_provenance binding value
        (EventCode.binding_success_of_resolve_success binding checks intention
          state.source.config.store value resolved)
      have verdict : GuardCheck.allAccepted? checks (graph.publicStore state.source.config.store)
          (.success value) = some true := by
        rw [GuardCheck.allAccepted?_publicStore]
        exact EventCode.guards_pass_of_resolve_success binding checks intention
          state.source.config.store value resolved
      obtain ⟨material, constructed, wire⟩ := resolutionOpening_success_emit state owner event
        payload binding known original value selected owned meaning fixed
      let next := State.finish ({ state with
        source := state.source.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) true)
          (cast (congrArg EventField.Value outputEq.symm) (.success value)) }.record
            (.source event .opening) (.player owner, serial))
      refine ⟨material, next, ?_, ?_, ?_⟩
      · rw [frozenResolutionOpening_encoded owner event payload binding state.source.accepted
          (fun selected => state.decisions.lookup (owner, selected)) (.success value) fixed]
        exact constructed
      · rw [wire]
        simp [handle, handleGame, Call.phase?, authorized, timely, ready, viewed, admitted,
          openDecision_success, selected, verdict, next]
      · rw [State.finish_source]
        rfl

end Vegas.SourceSession
