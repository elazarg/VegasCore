/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBindingOwner
import Vegas.Pending.EventActivationOrigin

/-! # One step of the one-packet game at a late decision

A late-delivery key decides a publication event when it is the owner's turn
at a reveal (`Vegas.PublicationTurn`), and a binding event when it is the
owner's turn at a commitment for which the owner has sent nothing
(`Vegas.BindingTurn`). At a binding, the image also records the success of
the owner's pending commitments to it (`Vegas.bindingImage`); at the site they
are none. At a kept state (`Vegas.decisionKept`), failure of the decided event
is read off the image (`Vegas.decisionFailed_eq`), and every step of the native
kernel is read off the image except the owner's own, which enters as a
hypothesis per kind of turn: within `δ` at a publication, and a law of moves
within `δ / 2` at a binding (`Vegas.OwnerBindingLaw`). Under it the control step
of a decoded profile, read through the image, is within `δ` in total variation of
the key's kernel (`Vegas.decisionKernel_close`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The owner of a key has sent no packet naming the event. -/
def UnsentFor (key : LateKey setup runtime leaks) (event : (graph setup).EventId) : Prop :=
  ∀ entry ∈ key.recalled, ∀ message, entry.2 = some message →
    message.payload.call.event? (graph setup) ≠ some event

/-- **A binding turn of a key.** It is the key owner's turn at the event in
the key's public view, the event binds a value of the owner of the payload
type, and the owner has sent nothing for it. -/
def BindingTurn (key : LateKey setup runtime leaks) (event : (graph setup).EventId) (payload :
  L.Ty) :
    Prop :=
  key.current.1.ownTurn? key.owner = some event ∧
    (∃ (outputEq : (graph setup).outputLayout event = .binding key.owner
      payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind key.owner payload),
      nodeView (graph setup) event = .bind key.owner payload outputEq codeEq) ∧
    UnsentFor (runtime := runtime) key event

open Classical in
/-- The binding event a key decides, with its payload type, if any. -/
def bindingTurn (key : LateKey setup runtime leaks) : Option ((graph setup).EventId × L.Ty) :=
  if turn : ∃ decided : (graph setup).EventId × L.Ty, BindingTurn (runtime := runtime) key
    decided.1 decided.2 then
    some turn.choose
  else none

theorem bindingTurn_spec {key : LateKey setup runtime leaks} {decided : (graph setup).EventId ×
  L.Ty}
    (found : bindingTurn (runtime := runtime) key = some decided) : BindingTurn (runtime :=
      runtime) key decided.1 decided.2 := by
  unfold bindingTurn at found
  split at found
  · rename_i turn
    cases found
    exact turn.choose_spec
  · cases found

/-- The event a key decides: its publication event, else its binding event. -/
def decidedEvent (key : LateKey setup runtime leaks) : Option (graph setup).EventId :=
  match turnEvent (runtime := runtime) key with
  | some event => some event
  | none => (bindingTurn (runtime := runtime) key).map Prod.fst

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- At a history of a site, an event that is the key owner's turn is ready. -/
theorem ready_of_ownTurn {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    {control : (application setup runtime leaks).Control} (current : history.1.state = some control)
    {event : (graph setup).EventId} (owned : key.current.1.ownTurn? key.owner = some event) :
    control.execution.application.config.cut.Ready event := by
  obtain ⟨_, keyEq⟩ := lateKey_of_history (runtime := runtime) siteKey history current
  simp only [lateKey, Option.some.injEq] at keyEq
  rw [← keyEq] at owned
  have spec := PublicView.ownTurn?_spec _ _ _ owned
  exact (control.execution.application.publicView_eventReady event).mp spec.1

/-- **No pending commitment at a binding turn.** At a history of a site whose
key leaves an event unsent, the owner has no pending commitment to it. -/
theorem commitStatuses_nil_of_unsent {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    {control : (application setup runtime leaks).Control} (current : history.1.state = some control)
    {event : (graph setup).EventId} (unsent : UnsentFor (runtime := runtime) key event) (payload :
      L.Ty) :
    commitStatuses (runtime := runtime) event who payload control.execution.application
      control.execution.network.pending = [] := by
  obtain ⟨_, keyEq⟩ := lateKey_of_history (runtime := runtime) siteKey history current
  simp only [lateKey, Option.some.injEq] at keyEq
  have trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    current ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.1.trace
  obtain ⟨inputRecall, _, _⟩ := runtime.countRecall_history leaks trace
  have facts := settledFacts_history (initialLaw setup) horizon scheduler trace
  unfold commitStatuses
  rw [List.filterMap_eq_nil_iff]
  intro message member
  unfold commitStatus
  split
  · rename_i named candidate call
    split
    · rename_i owned
      exfalso
      obtain ⟨namedEq, sender⟩ := owned
      have emitted : message ∈ control.execution.network.inputs :=
        facts.carried.pending message member
      have recalled : message ∈ (application setup runtime leaks).outputs
          (control.execution.recall who) := by
        rw [← inputRecall who]
        exact List.mem_filter.mpr ⟨emitted, by simp [sender]⟩
      obtain ⟨entry, inRecall, entryEmitted⟩ := List.mem_filterMap.mp recalled
      apply unsent (operationalView setup runtime leaks entry.beforeView, entry.emitted)
        (by rw [← keyEq]; exact List.mem_map_of_mem inRecall) message entryEmitted
      rw [call, namedEq]
      rfl
    · rfl
  · rfl

/-- The image at a late decision: the pending image at a publication, the
binding image at a binding. -/
abbrev DecisionImage :=
  PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) ⊕ BindingImage (runtime :=
    runtime) (setup := setup) (leaks := leaks)

/-- The image of a protocol state at a key. -/
def decisionImage (key : LateKey setup runtime leaks) (state : (application setup runtime
  leaks).ProtocolState) :
    DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks) :=
  match turnEvent (runtime := runtime) key with
  | some event => .inl (pendingImage (runtime := runtime) event state)
  | none => match bindingTurn (runtime := runtime) key with
    | some decided => .inr (bindingImage (runtime := runtime) decided.1 key.owner decided.2 state)
    | none => .inl (.inr false)

/-- Failure read off the decision image. -/
def decisionFailure : DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks) → ℝ
  | .inl image => imageFailure (runtime := runtime) image
  | .inr (.inl _) => 0
  | .inr (.inr failed) => if failed then 1 else 0

/-- The image of a site's history read off its operational record. -/
def decisionRecordImage (key : LateKey setup runtime leaks)
    (record : List (Option (OperationalState setup runtime leaks))) :
    DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks) :=
  match turnEvent (runtime := runtime) key with
  | some _ => .inl (recordImage (runtime := runtime) key record)
  | none => match bindingTurn (runtime := runtime) key with
    | some _ => .inr (.inl (record.head?.getD none, []))
    | none => .inl (.inr false)

open Classical in
/-- **Failure at a key.** The decided event has completed with a failed
output; never at a key deciding none. -/
def DecisionFailed (key : LateKey setup runtime leaks) : (application setup runtime
  leaks).ProtocolState → Prop
  | none => False
  | some control => match decidedEvent (runtime := runtime) key with
    | none => False
    | some event => event ∈ control.execution.application.config.cut.completed ∧
        StoreEventFailed control.execution.application.config.store event

variable (bounds horizon scheduler) in
/-- The kept states at a key: states of one-packet histories at which the
decided event has completed, or which are forced for the owner with the event
ready. -/
def decisionKept (key : LateKey setup runtime leaks) : Set (application setup runtime
  leaks).ProtocolState :=
  match decidedEvent (runtime := runtime) key with
  | none => Set.univ
  | some event => {state | (∃ history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History, history.state = state) ∧ ∃ control, state = some control ∧
      (event ∈ control.execution.application.config.cut.completed ∨
        (ForcedState setup runtime leaks key.owner (some control) ∧
          control.execution.application.config.cut.Ready event))}

variable (horizon scheduler) in
open Classical in
/-- A scheduler round at a pending binding from an operational state and
statuses, read off a representative execution with the binding ready; the
image itself when there is none. -/
def bindingRoundKernel (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (remaining : Nat)
    (image : Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool)) :
    PMF (BindingImage (runtime := runtime) (setup := setup) (leaks := leaks)) :=
  if represented : ∃ execution : (application setup runtime leaks).Execution,
      operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩) = image.1 ∧
      commitStatuses (runtime := runtime) event owner payload execution.application
        execution.network.pending =
        image.2 ∧
      execution.application.config.cut.Ready event then
    ((application setup runtime leaks).transition (initialLaw setup) horizon scheduler
      (some ⟨remaining + 1, none, represented.choose⟩) (fun _ => none)).map
        (bindingImage (runtime := runtime) event owner payload)
  else PMF.pure (.inl image)

variable (horizon scheduler) in
/-- **The kernel at a pending binding.** Completed and uninitialized images
stay put; the owner's step follows its law of moves; another player keeps
silence; a scheduler round is read off a representative. -/
def bindingKernel (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (moves : Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool) →
      PMF (Option (Handle (graph setup)))) :
    BindingImage (runtime := runtime) (setup := setup) (leaks := leaks) →
      PMF (BindingImage (runtime := runtime) (setup := setup) (leaks := leaks))
  | .inr failed => PMF.pure (.inr failed)
  | .inl (none, statuses) => PMF.pure (.inl (none, statuses))
  | .inl (some state, statuses) => match state.actor with
    | some player => if player = owner then
          (moves (some state, statuses)).map (moveImage (runtime := runtime) event owner (some
            state, statuses))
        else PMF.pure (.inl (some (state.respond player none), statuses))
    | none => match state.remaining with
      | 0 => PMF.pure (.inl (some state, statuses))
      | remaining + 1 =>
          bindingRoundKernel (runtime := runtime) horizon scheduler event owner payload remaining
            (some state, statuses)

variable (bounds horizon scheduler) in
/-- **The kernel at a key.** -/
def decisionKernel {LateOption : Type}
    (ownerKernel : LateKey setup runtime leaks → LateOption → Option (OperationalState setup
      runtime leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)))
    (moves : LateKey setup runtime leaks → LateOption →
      Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup runtime leaks) (option : LateOption) :
    DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks) →
      PMF (DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks)) :=
  match turnEvent (runtime := runtime) key with
  | some _ => fun image => match image with
    | .inl pending => (lateKernel (runtime := runtime) bounds horizon scheduler ownerKernel key
      option pending).map .inl
    | .inr _ => PMF.pure image
  | none => match bindingTurn (runtime := runtime) key with
    | some decided => fun image => match image with
      | .inr binding => (bindingKernel (runtime := runtime) horizon scheduler decided.1
          key.owner decided.2
          (moves key option) binding).map .inr
      | .inl _ => PMF.pure image
    | none => fun _ => PMF.pure (.inl (.inr false))

variable (bounds horizon scheduler) in
open Classical in
/-- **The owner's law of moves at a binding turn.** At every forced state with
the decided binding ready and the owner acting, the owner's decoded response,
sorted into moves, is within `δ` in total variation of the key's law of moves at
the operational state and statuses. -/
def OwnerBindingLaw {LateOption : Type}
    (moves : LateKey setup runtime leaks → LateOption →
      Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (δ : ℝ) (allowed : (application setup runtime leaks).ProtocolState → Prop := fun _ => True) :
    Prop :=
  ∀ event payload, BindingTurn (runtime := runtime) key event payload →
    ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
      (remaining : Nat) (execution : (application setup runtime leaks).Execution),
      history.state = some ⟨remaining, some key.owner, execution⟩ →
      allowed history.state →
      ForcedState setup runtime leaks key.owner history.state →
      execution.application.config.cut.Ready event →
      PMF.WithinTV δ (((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile key.owner (execution.recall key.owner)
          (execution.observe (application setup runtime leaks) key.owner)).map
            (commitMove (runtime := runtime) event key.owner payload
              execution))
        ((moves key option (operationalState setup runtime leaks
          (some ⟨remaining, some key.owner, execution⟩),
          commitStatuses (runtime := runtime) event key.owner payload
            execution.application
            execution.network.pending)).map some)

omit [Fintype Player] in
/-- The decided event is the key owner's turn. -/
theorem ownTurn_of_decidedEvent {key : LateKey setup runtime leaks} {event : (graph setup).EventId}
    (decided : decidedEvent (runtime := runtime) key = some event) : key.current.1.ownTurn?
      key.owner = some event := by
  unfold decidedEvent at decided
  cases turn : turnEvent (runtime := runtime) key with
  | some published =>
      rw [turn] at decided
      cases decided
      exact (publicationTurn_of_turnEvent (runtime := runtime) turn).1
  | none =>
      rw [turn] at decided
      cases binding : bindingTurn (runtime := runtime) key with
      | none => rw [binding] at decided; cases decided
      | some pair =>
          rw [binding] at decided
          cases decided
          exact (bindingTurn_spec (runtime := runtime) binding).1

section Fields

variable {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some key)
include siteKey

/-- A forced history of a site is kept at its key. -/
theorem decisionKept_of_history
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    (forced : ForcedState setup runtime leaks who history.1.state) :
    history.1.state ∈ decisionKept (runtime := runtime) bounds horizon scheduler key := by
  unfold decisionKept
  cases decided : decidedEvent (runtime := runtime) key with
  | none => trivial
  | some event =>
      cases current : history.1.state with
      | none =>
          rw [current] at forced
          exact forced.elim
      | some control =>
          rw [current] at forced
          refine ⟨⟨history.1, current⟩, control, rfl, Or.inr ⟨?_, ?_⟩⟩
          · rw [owner_of_lateKey (runtime := runtime) siteKey]
            exact forced
          · exact ready_of_ownTurn (runtime := runtime) siteKey history current
              (ownTurn_of_decidedEvent (runtime := runtime) decided)

/-- The image of a forced history's state is read off its operational record. -/
theorem decisionImage_of_history
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    (forced : ForcedState setup runtime leaks who history.1.state) :
    decisionImage (runtime := runtime) key history.1.state =
      decisionRecordImage (runtime := runtime) key
        (operationalRecord setup runtime leaks bounds horizon scheduler history.1.trace) := by
  unfold decisionImage decisionRecordImage
  cases turn : turnEvent (runtime := runtime) key with
  | some event =>
      have lumped := lateImage_of_history (runtime := runtime) siteKey history forced
      simp only [lateImage, turn] at lumped
      simp only
      rw [lumped]
  | none =>
      cases binding : bindingTurn (runtime := runtime) key with
      | none => rfl
      | some decided =>
          have spec := bindingTurn_spec (runtime := runtime) binding
          obtain ⟨rest, record⟩ := operationalRecord_head (runtime := runtime) history.1.trace
          rw [record]
          cases current : history.1.state with
          | none =>
              rw [current] at forced
              exact forced.elim
          | some control =>
              have ready := ready_of_ownTurn (runtime := runtime) siteKey history current spec.1
              have empty := commitStatuses_nil_of_unsent (runtime := runtime) siteKey history
                current spec.2.2
                decided.2
              rw [← owner_of_lateKey (runtime := runtime) siteKey] at empty
              simp only [bindingImage, stateStatuses, empty,
                pendingImage_of_pending (runtime := runtime) control ready.1, attachStatuses
                  , List.head?_cons,
                Option.getD_some]

end Fields

/-- Kept states stay kept along the control step of every decoded profile. -/
theorem decisionKept_step (key : LateKey setup runtime leaks)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {state : (application setup runtime leaks).ProtocolState}
    (kept : state ∈ decisionKept (runtime := runtime) bounds horizon scheduler key)
    {next : (application setup runtime leaks).ProtocolState}
    (member : next ∈ ((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
      ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
        scheduler profile) state).support) :
    next ∈ decisionKept (runtime := runtime) bounds horizon scheduler key := by
  unfold decisionKept at kept ⊢
  cases decided : decidedEvent (runtime := runtime) key with
  | none => trivial
  | some event =>
      rw [decided] at kept
      obtain ⟨⟨history, current⟩, control, rfl, status⟩ := kept
      obtain ⟨extended, reached⟩ := controlStep_history (runtime := runtime) bounds horizon
        scheduler profile history
        (by rw [current]; exact member)
      obtain ⟨control', rfl, step⟩ := controlStep_configStep (runtime := runtime) horizon
        scheduler _ control member
      refine ⟨⟨extended, reached⟩, control', rfl, ?_⟩
      rcases status with completed | ⟨forced, ready⟩
      · exact Or.inl (completed_of_configStep step completed)
      · exact forced_or_completed_of_configStep (runtime := runtime) step forced ready

open Classical in
/-- Failure of a kept state is read off its image. -/
theorem decisionFailed_eq (key : LateKey setup runtime leaks)
    {state : (application setup runtime leaks).ProtocolState}
    (kept : state ∈ decisionKept (runtime := runtime) bounds horizon scheduler key) :
    (if DecisionFailed (runtime := runtime) key state then (1 : ℝ) else 0) =
      decisionFailure (runtime := runtime) (decisionImage (runtime := runtime) key state) := by
  unfold decisionKept at kept
  cases decided : decidedEvent (runtime := runtime) key with
  | none =>
      have turn : turnEvent (runtime := runtime) key = none := by
        unfold decidedEvent at decided
        cases turn : turnEvent (runtime := runtime) key with
        | none => rfl
        | some _ => rw [turn] at decided; cases decided
      have binding : bindingTurn (runtime := runtime) key = none := by
        unfold decidedEvent at decided
        rw [turn] at decided
        cases binding : bindingTurn (runtime := runtime) key with
        | none => rfl
        | some _ => rw [binding] at decided; cases decided
      cases state with
      | none => simp only [DecisionFailed, ↓reduceIte, decisionImage, turn, binding,
          decisionFailure , imageFailure ,
            Bool.false_eq_true]
      | some control => simp only [DecisionFailed, decided, ↓reduceIte, decisionImage, turn,
          binding, decisionFailure , imageFailure ,
            Bool.false_eq_true]
  | some event =>
      rw [decided] at kept
      obtain ⟨_, control, rfl, _⟩ := kept
      unfold decidedEvent at decided
      cases turn : turnEvent (runtime := runtime) key with
      | some published =>
          rw [turn] at decided
          cases decided
          by_cases completed : event ∈ control.execution.application.config.cut.completed
          · simp only [DecisionFailed, decidedEvent, turn, completed, true_and, ↓reduceIte,
              decisionImage , pendingImage ,
                decisionFailure , imageFailure ,
                decide_eq_true_eq]
          · simp only [DecisionFailed, decidedEvent, turn, completed, false_and, ↓reduceIte,
              decisionImage , pendingImage ,
                decisionFailure , imageFailure ]
      | none =>
          rw [turn] at decided
          cases binding : bindingTurn (runtime := runtime) key with
          | none => rw [binding] at decided; cases decided
          | some pair =>
              rw [binding] at decided
              cases decided
              by_cases completed : pair.1 ∈ control.execution.application.config.cut.completed
              · simp only [DecisionFailed, decidedEvent, turn, binding, Option.map_some,
                  completed, true_and, ↓reduceIte, decisionImage ,
                    bindingImage , pendingImage ,
                  attachStatuses , decisionFailure ,
                    decide_eq_true_eq]
              · simp only [DecisionFailed, decidedEvent, turn, binding, Option.map_some,
                  completed, false_and, ↓reduceIte, decisionImage ,
                    bindingImage , pendingImage ,
                  attachStatuses , decisionFailure ]

/-- **One step at a pending binding.** From a kept state, the control step of
a decoded profile, read through the binding image, is within `δ` in total
variation of the binding kernel, provided the owner's law of moves is within
`δ`. -/
theorem bindingKernel_close {LateOption : Type}
    (moves : LateKey setup runtime leaks → LateOption →
      Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {δ : ℝ} (nonneg : 0 ≤ δ) {allowed : (application setup runtime leaks).ProtocolState → Prop}
    (law : OwnerBindingLaw (runtime := runtime) bounds horizon scheduler moves key option profile
      δ allowed)
    {event : (graph setup).EventId} {payload : L.Ty} (turn : BindingTurn (runtime := runtime) key
      event payload)
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    (allowedState : allowed (some control))
    (status : event ∈ control.execution.application.config.cut.completed ∨
      (ForcedState setup runtime leaks key.owner (some control) ∧
        control.execution.application.config.cut.Ready event)) :
    PMF.WithinTV δ (((application setup runtime leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile) (some control)).map (bindingImage (runtime := runtime) event
            key.owner payload))
      (bindingKernel (runtime := runtime) horizon scheduler event key.owner
        payload (moves key option)
        (bindingImage (runtime := runtime) event key.owner payload (some
          control))) := by
  obtain ⟨_, ⟨outputEq, codeEq, view⟩, _⟩ := turn
  rcases status with completed | ⟨forced, ready⟩
  · convert (PMF.WithinTV.refl _).mono nonneg using 1
    have constant : ((application setup runtime leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
          (initialLaw setup) horizon scheduler profile) (some control)).map
          (bindingImage (runtime := runtime) event key.owner payload) =
        ((application setup runtime leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
          (initialLaw setup) horizon scheduler profile) (some control)).map
          (Function.const _ (bindingImage (runtime := runtime) event key.owner payload (some
            control))) := by
      apply map_congr_on_support
      intro next member
      obtain ⟨control', rfl, step⟩ :=
        controlStep_configStep (runtime := runtime) horizon scheduler _ control member
      have completed' := completed_of_configStep step completed
      have image := pendingImage_of_configStep (runtime := runtime) step completed
      simp only [bindingImage, image, Function.const_apply]
      simp only [pendingImage, completed, ↓reduceIte, attachStatuses]
    rw [constant, PMF.map_const]
    simp only [bindingImage, pendingImage, completed, ↓reduceIte, attachStatuses, bindingKernel]
  · have pending := ready.1
    have imageEq : bindingImage (runtime := runtime) event key.owner payload
      (some control) =
        .inl (operationalState setup runtime leaks (some control),
          commitStatuses (runtime := runtime) event key.owner payload
            control.execution.application
            control.execution.network.pending) := by
      simp only [bindingImage, stateStatuses, pendingImage_of_pending (runtime := runtime) control
        pending,
        attachStatuses ]
    rw [imageEq]
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some player =>
        by_cases owned : player = key.owner
        · subst owned
          have kernelOwner : bindingKernel (runtime := runtime) horizon scheduler event
            key.owner payload
              (moves key option) (.inl (operationalState setup runtime leaks
                (some ⟨remaining, some key.owner, execution⟩),
                commitStatuses (runtime := runtime) event key.owner payload
                  execution.application
                  execution.network.pending)) =
              (moves key option (operationalState setup runtime leaks
                (some ⟨remaining, some key.owner, execution⟩),
                commitStatuses (runtime := runtime) event key.owner payload
                  execution.application
                  execution.network.pending)).map
                (moveImage (runtime := runtime) event key.owner
                  (operationalState setup runtime leaks
                  (some ⟨remaining, some key.owner, execution⟩),
                  commitStatuses (runtime := runtime) event key.owner payload
                    execution.application
                    execution.network.pending)) := by
            simp only [operationalState, bindingKernel, ↓reduceIte]
          rw [kernelOwner]
          exact ownerBindingStep_close (runtime := runtime) bounds profile history current pending _
            (law event payload ⟨‹_›, ⟨outputEq, codeEq, view⟩, ‹_›⟩ history remaining execution
              current (by rw [current]; exact allowedState) (by rw [current]; exact forced) ready)
        · convert (PMF.WithinTV.refl _).mono nonneg using 1
          rw [controlStep_other_of_pending (runtime := runtime) bounds horizon scheduler profile
            key.owner history
            (by rw [current]; exact forced) current ready
            (nodeView_bind_actor outputEq codeEq) rfl owned, PMF.pure_map,
            bindingImage_respond_silent (runtime := runtime) pending rfl]
          simp only [operationalState, Option.map_some, bindingKernel, owned, ↓reduceIte]
    | none =>
        cases remaining with
        | zero =>
            convert (PMF.WithinTV.refl _).mono nonneg using 1
            have step : (application setup runtime leaks).controlStep (initialLaw setup) horizon
                scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
                  (initialLaw setup) horizon scheduler profile) (some ⟨0, none, execution⟩) =
                PMF.pure (some ⟨0, none, execution⟩) := rfl
            rw [step, PMF.pure_map, ← imageEq]
            simp only [bindingImage, stateStatuses, pendingImage_of_pending (runtime := runtime) _
              pending,
              attachStatuses , operationalState ,
                bindingKernel ]
        | succ remaining =>
            convert (PMF.WithinTV.refl _).mono nonneg using 1
            have step : (application setup runtime leaks).controlStep (initialLaw setup) horizon
                scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
                  (initialLaw setup) horizon scheduler profile)
                  (some ⟨remaining + 1, none, execution⟩) =
                (application setup runtime leaks).transition (initialLaw setup) horizon scheduler
                  (some ⟨remaining + 1, none, execution⟩) (fun _ => none) := rfl
            rw [step]
            obtain ⟨state, stateEq⟩ : ∃ state, operationalState setup runtime leaks
                (some ⟨remaining + 1, none, execution⟩) = some state := ⟨_, rfl⟩
            have represented : ∃ other : (application setup runtime leaks).Execution,
                operationalState setup runtime leaks (some ⟨remaining + 1, none, other⟩) = some
                  state ∧
                commitStatuses (runtime := runtime) event key.owner payload
                  other.application
                    other.network.pending =
                  commitStatuses (runtime := runtime) event key.owner payload
                    execution.application
                    execution.network.pending ∧
                other.application.config.cut.Ready event :=
              ⟨execution, stateEq, rfl, ready⟩
            have kernelRound : bindingKernel (runtime := runtime) horizon scheduler event
              key.owner payload
                (moves key option) (.inl (some state,
                  commitStatuses (runtime := runtime) event key.owner payload
                    execution.application
                    execution.network.pending)) =
                bindingRoundKernel (runtime := runtime) horizon scheduler event key.owner
                  payload remaining
                  (some state, commitStatuses (runtime := runtime) event key.owner payload
                    execution.application
                    execution.network.pending) := by
              have actorNone : state.actor = none := by
                have := congrArg (Option.map OperationalState.actor) stateEq
                simpa only [operationalState, Option.map_some, Option.some.injEq] using
                  this.symm
              have remainingEq : state.remaining = remaining + 1 := by
                have := congrArg (Option.map OperationalState.remaining)
                  stateEq
                simpa only [operationalState, Option.map_some, Option.some.injEq] using
                  this.symm
              simp only [bindingKernel, actorNone, remainingEq]
            rw [stateEq, kernelRound]
            unfold bindingRoundKernel
            rw [dite_eq_left represented]
            obtain ⟨repSame, repStatuses, _⟩ := represented.choose_spec
            exact (binding_round_image_congr (runtime := runtime) (initialLaw setup) horizon
              scheduler remaining
              execution represented.choose (stateEq.trans repSame.symm) repStatuses.symm ready
              view).symm

/-- **One step of the native kernel at a late decision.** From a kept state,
the control step of a decoded profile, read through the key's image, is within
`δ` in total variation of the key's kernel, provided the owner's step at a
publication is within `δ` and its law of moves at a binding within `δ / 2`. -/
theorem decisionKernel_close {LateOption : Type}
    (ownerKernel : LateKey setup runtime leaks → LateOption → Option (OperationalState setup
      runtime leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)))
    (moves : LateKey setup runtime leaks → LateOption →
      Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {δ δBinding : ℝ} (nonneg : 0 ≤ δ) (bindingNonneg : 0 ≤ δBinding)
    (bindingLe : 2 * δBinding ≤ δ)
    {allowed : (application setup runtime leaks).ProtocolState → Prop}
    (owner : OwnerStepClose (runtime := runtime) ownerKernel key option profile δ allowed)
    (law : OwnerBindingLaw (runtime := runtime) bounds horizon scheduler moves key option profile
      δBinding allowed)
    {state : (application setup runtime leaks).ProtocolState}
    (kept : state ∈ decisionKept (runtime := runtime) bounds horizon scheduler key) (allowedState
      : allowed state) :
    PMF.WithinTV δ (((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
        ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
          scheduler profile) state).map (decisionImage (runtime := runtime) key))
      (decisionKernel (runtime := runtime) bounds horizon scheduler ownerKernel moves key option
        (decisionImage (runtime := runtime) key state)) := by
  unfold decisionKept at kept
  cases turn : turnEvent (runtime := runtime) key with
  | some event =>
      have imageEq : decisionImage (runtime := runtime) key = Sum.inl ∘ lateImage (runtime :=
        runtime) key := by
        funext state
        simp only [decisionImage, lateImage, turn, Function.comp]
      have keptPublication : state ∈ lateKept (runtime := runtime) bounds horizon scheduler key :=
        by
        unfold lateKept
        rw [turn]
        simp only [decidedEvent, turn] at kept
        exact kept
      have close := PMF.WithinTV.map (lateKernel_close (runtime := runtime) ownerKernel key option
        profile nonneg owner
        keptPublication allowedState) (Sum.inl : PendingImage (runtime := runtime) (setup :=
          setup) (leaks := leaks) →
          DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks))
      rw [imageEq, ← PMF.map_comp]
      simp only [decisionKernel, turn, Function.comp]
      exact close
  | none =>
      cases binding : bindingTurn (runtime := runtime) key with
      | none =>
          convert (PMF.WithinTV.refl _).mono nonneg using 1
          have constant : decisionImage (runtime := runtime) key = Function.const _ (.inl (.inr
            false)) := by
            funext state
            simp only [decisionImage, turn, binding, Function.const_apply]
          simp only [constant, decisionKernel, turn, binding, PMF.map_const]
      | some decided =>
          have spec := bindingTurn_spec (runtime := runtime) binding
          have imageEq : decisionImage (runtime := runtime) key =
              Sum.inr ∘ bindingImage (runtime := runtime) decided.1 key.owner
                decided.2 := by
            funext state
            simp only [decisionImage, turn, binding, Function.comp]
          simp only [decidedEvent, turn, binding, Option.map_some] at kept
          obtain ⟨⟨history, current⟩, control, rfl, status⟩ := kept
          have close := PMF.WithinTV.map (bindingKernel_close (runtime := runtime) moves key
            option profile bindingNonneg
            law spec history current allowedState status) (Sum.inr :
              BindingImage (runtime := runtime) (setup := setup) (leaks := leaks) →
                DecisionImage (runtime := runtime) (setup := setup) (leaks := leaks))
          rw [imageEq, ← PMF.map_comp]
          simp only [decisionKernel, turn, binding, Function.comp]
          exact PMF.WithinTV.mono (by linarith) close

end Vegas
