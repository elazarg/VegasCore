/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketBindingOwner

/-! # The one-step lumping of the one-packet game at a late decision

A late-delivery key decides a publication event when it is the owner's turn
at a reveal (`Vegas.PublicationTurn`), and a binding event when it is the
owner's turn at a commitment for which the owner has sent nothing
(`Vegas.BindingTurn`). At a binding, the image also records the success of
the owner's pending commitments to it (`Vegas.bindingImage`); at the site they
are none. Every step of the native kernel from a forced state with the event
ready is read off the image, except the owner's own, which enters as a
hypothesis per kind of turn. Under it the late-delivery failure lumps
(`Vegas.onePacketLateLumping`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The owner of a key has sent no packet naming the event. -/
def UnsentFor (key : LateKey setup leaks) (event : (graph setup).EventId) : Prop :=
  ∀ entry ∈ key.recalled, ∀ message, entry.2 = some message →
    message.payload.call.event? (graph setup) ≠ some event

/-- **A binding turn of a key.** It is the key owner's turn at the event in
the key's public view, the event binds a value of the owner of the payload
type, and the owner has sent nothing for it. -/
def BindingTurn (key : LateKey setup leaks) (event : (graph setup).EventId) (payload : L.Ty) :
    Prop :=
  key.current.1.ownTurn? key.owner = some event ∧
    (∃ (outputEq : (graph setup).outputLayout event = .binding key.owner payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind key.owner payload),
      nodeView (graph setup) event = .bind key.owner payload outputEq codeEq) ∧
    UnsentFor key event

open Classical in
/-- The binding event a key decides, with its payload type, if any. -/
def bindingTurn (key : LateKey setup leaks) : Option ((graph setup).EventId × L.Ty) :=
  if turn : ∃ decided : (graph setup).EventId × L.Ty, BindingTurn key decided.1 decided.2 then
    some turn.choose
  else none

theorem bindingTurn_spec {key : LateKey setup leaks} {decided : (graph setup).EventId × L.Ty}
    (found : bindingTurn key = some decided) : BindingTurn key decided.1 decided.2 := by
  unfold bindingTurn at found
  split at found
  · rename_i turn
    cases found
    exact turn.choose_spec
  · cases found

/-- The event a key decides: its publication event, else its binding event. -/
def decidedEvent (key : LateKey setup leaks) : Option (graph setup).EventId :=
  match turnEvent key with
  | some event => some event
  | none => (bindingTurn key).map Prod.fst

variable [Fintype Player] {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}

/-- At a history of a site, an event that is the key owner's turn is ready. -/
theorem ready_of_ownTurn {who : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    {control : (application setup leaks).Control} (current : history.1.state = some control)
    {event : (graph setup).EventId} (owned : key.current.1.ownTurn? key.owner = some event) :
    control.execution.application.config.cut.Ready event := by
  obtain ⟨_, keyEq⟩ := lateKey_of_history siteKey history current
  simp only [lateKey, Option.some.injEq] at keyEq
  rw [← keyEq] at owned
  have spec := PublicView.ownTurn?_spec _ _ _ owned
  exact (control.execution.application.publicView_eventReady event).mp spec.1

/-- **No pending commitment at a binding turn.** At a history of a site whose
key leaves an event unsent, the owner has no pending commitment to it. -/
theorem commitStatuses_nil_of_unsent {who : Player}
    {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    {control : (application setup leaks).Control} (current : history.1.state = some control)
    {event : (graph setup).EventId} (unsent : UnsentFor key event) (payload : L.Ty) :
    commitStatuses event who payload control.execution.application
      control.execution.network.pending = [] := by
  obtain ⟨_, keyEq⟩ := lateKey_of_history siteKey history current
  simp only [lateKey, Option.some.injEq] at keyEq
  have trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control) :=
    current ▸ (bounds.onePacketMenu (runtime setup) leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.1.trace
  obtain ⟨inputRecall, _, _⟩ := (runtime setup).countRecall_history leaks trace
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
      have recalled : message ∈ (application setup leaks).outputs
          (control.execution.recall who) := by
        rw [← inputRecall who]
        exact List.mem_filter.mpr ⟨emitted, by simp [sender]⟩
      obtain ⟨entry, inRecall, entryEmitted⟩ := List.mem_filterMap.mp recalled
      apply unsent (operationalView setup leaks entry.beforeView, entry.emitted)
        (by rw [← keyEq]; exact List.mem_map_of_mem inRecall) message entryEmitted
      rw [call, namedEq]
      rfl
    · rfl
  · rfl

/-- The image at a late decision: the pending image at a publication, the
binding image at a binding. -/
abbrev DecisionImage :=
  PendingImage (setup := setup) (leaks := leaks) ⊕ BindingImage (setup := setup) (leaks := leaks)

/-- The image of a protocol state at a key. -/
def decisionImage (key : LateKey setup leaks) (state : (application setup leaks).ProtocolState) :
    DecisionImage (setup := setup) (leaks := leaks) :=
  match turnEvent key with
  | some event => .inl (pendingImage event state)
  | none => match bindingTurn key with
    | some decided => .inr (bindingImage decided.1 key.owner decided.2 state)
    | none => .inl (.inr false)

/-- Failure read off the decision image. -/
def decisionFailure : DecisionImage (setup := setup) (leaks := leaks) → ℝ
  | .inl image => imageFailure image
  | .inr (.inl _) => 0
  | .inr (.inr failed) => if failed then 1 else 0

/-- The image of a site's history read off its operational record. -/
def decisionRecordImage (key : LateKey setup leaks)
    (record : List (Option (OperationalState setup leaks))) :
    DecisionImage (setup := setup) (leaks := leaks) :=
  match turnEvent key with
  | some _ => .inl (recordImage key record)
  | none => match bindingTurn key with
    | some _ => .inr (.inl (record.head?.getD none, []))
    | none => .inl (.inr false)

open Classical in
/-- **Failure at a key.** The decided event has completed with a failed
output; never at a key deciding none. -/
def DecisionFailed (key : LateKey setup leaks) : (application setup leaks).ProtocolState → Prop
  | none => False
  | some control => match decidedEvent key with
    | none => False
    | some event => event ∈ control.execution.application.config.cut.completed ∧
        StoreEventFailed control.execution.application.config.store event

variable (bounds horizon scheduler) in
/-- The kept states at a key: states of one-packet histories at which the
decided event has completed, or which are forced for the owner with the event
ready. -/
def decisionKept (key : LateKey setup leaks) : Set (application setup leaks).ProtocolState :=
  match decidedEvent key with
  | none => Set.univ
  | some event => {state | (∃ history : (onePacketProtocol setup leaks bounds horizon
      scheduler).History, history.state = state) ∧ ∃ control, state = some control ∧
      (event ∈ control.execution.application.config.cut.completed ∨
        (ForcedState setup leaks key.owner (some control) ∧
          control.execution.application.config.cut.Ready event))}

variable (horizon scheduler) in
open Classical in
/-- A scheduler round at a pending binding from an operational state and
statuses, read off a representative execution with the binding ready; the
image itself when there is none. -/
def bindingRoundKernel (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (remaining : Nat)
    (image : Option (OperationalState setup leaks) × List (MessageId Player × Bool)) :
    PMF (BindingImage (setup := setup) (leaks := leaks)) :=
  if represented : ∃ execution : (application setup leaks).Execution,
      operationalState setup leaks (some ⟨remaining + 1, none, execution⟩) = image.1 ∧
      commitStatuses event owner payload execution.application execution.network.pending =
        image.2 ∧
      execution.application.config.cut.Ready event then
    ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some ⟨remaining + 1, none, represented.choose⟩) (fun _ => none)).map
        (bindingImage event owner payload)
  else PMF.pure (.inl image)

variable (horizon scheduler) in
/-- **The kernel at a pending binding.** Completed and uninitialized images
stay put; the owner's step follows its law of moves; another player keeps
silence; a scheduler round is read off a representative. -/
def bindingKernel (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (moves : Option (OperationalState setup leaks) × List (MessageId Player × Bool) →
      PMF (Option (Handle (graph setup)))) :
    BindingImage (setup := setup) (leaks := leaks) →
      PMF (BindingImage (setup := setup) (leaks := leaks))
  | .inr failed => PMF.pure (.inr failed)
  | .inl (none, statuses) => PMF.pure (.inl (none, statuses))
  | .inl (some state, statuses) => match state.actor with
    | some player => if player = owner then
          (moves (some state, statuses)).map (moveImage event owner (some state, statuses))
        else PMF.pure (.inl (some (state.respond player none), statuses))
    | none => match state.remaining with
      | 0 => PMF.pure (.inl (some state, statuses))
      | remaining + 1 =>
          bindingRoundKernel horizon scheduler event owner payload remaining (some state, statuses)

variable (bounds horizon scheduler) in
/-- **The kernel at a key.** -/
def decisionKernel {LateOption : Type}
    (ownerKernel : LateKey setup leaks → LateOption → Option (OperationalState setup leaks) →
      PMF (PendingImage (setup := setup) (leaks := leaks)))
    (moves : LateKey setup leaks → LateOption →
      Option (OperationalState setup leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup leaks) (option : LateOption) :
    DecisionImage (setup := setup) (leaks := leaks) →
      PMF (DecisionImage (setup := setup) (leaks := leaks)) :=
  match turnEvent key with
  | some _ => fun image => match image with
    | .inl pending => (lateKernel bounds horizon scheduler ownerKernel key option pending).map .inl
    | .inr _ => PMF.pure image
  | none => match bindingTurn key with
    | some decided => fun image => match image with
      | .inr binding => (bindingKernel horizon scheduler decided.1 key.owner decided.2
          (moves key option) binding).map .inr
      | .inl _ => PMF.pure image
    | none => fun _ => PMF.pure (.inl (.inr false))

variable (bounds horizon scheduler) in
open Classical in
/-- **The owner's law of moves at a binding turn.** At every forced state with
the decided binding ready and the owner acting, the owner's decoded response,
sorted into moves, is within `δ` on unit payoffs of the key's law of moves at
the operational state and statuses. -/
def OwnerBindingLaw {LateOption : Type}
    (moves : LateKey setup leaks → LateOption →
      Option (OperationalState setup leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    (δ : ℝ) : Prop :=
  ∀ event payload, BindingTurn key event payload →
    ∀ (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
      (remaining : Nat) (execution : (application setup leaks).Execution),
      history.state = some ⟨remaining, some key.owner, execution⟩ →
      ForcedState setup leaks key.owner history.state →
      execution.application.config.cut.Ready event →
      UnitClose δ (((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile key.owner (execution.recall key.owner)
          (execution.observe (application setup leaks) key.owner)).map
            (commitMove event key.owner payload execution))
        ((moves key option (operationalState setup leaks
          (some ⟨remaining, some key.owner, execution⟩),
          commitStatuses event key.owner payload execution.application
            execution.network.pending)).map some)

omit [Fintype Player] in
/-- The decided event is the key owner's turn. -/
theorem ownTurn_of_decidedEvent {key : LateKey setup leaks} {event : (graph setup).EventId}
    (decided : decidedEvent key = some event) : key.current.1.ownTurn? key.owner = some event := by
  unfold decidedEvent at decided
  cases turn : turnEvent key with
  | some published =>
      rw [turn] at decided
      cases decided
      exact (publicationTurn_of_turnEvent turn).1
  | none =>
      rw [turn] at decided
      cases binding : bindingTurn key with
      | none => rw [binding] at decided; cases decided
      | some pair =>
          rw [binding] at decided
          cases decided
          exact (bindingTurn_spec binding).1

section Fields

variable {who : Player}
  {site : (onePacketInformation setup leaks bounds horizon scheduler).InformationSite who}
  {key : LateKey setup leaks} (siteKey : lateKey setup leaks who site.1 = some key)
include siteKey

/-- A forced history of a site is kept at its key. -/
theorem decisionKept_of_history
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    (forced : ForcedState setup leaks who history.1.state) :
    history.1.state ∈ decisionKept bounds horizon scheduler key := by
  unfold decisionKept
  cases decided : decidedEvent key with
  | none => trivial
  | some event =>
      cases current : history.1.state with
      | none =>
          rw [current] at forced
          exact forced.elim
      | some control =>
          rw [current] at forced
          refine ⟨⟨history.1, current⟩, control, rfl, Or.inr ⟨?_, ?_⟩⟩
          · rw [owner_of_lateKey siteKey]
            exact forced
          · exact ready_of_ownTurn siteKey history current (ownTurn_of_decidedEvent decided)

/-- The image of a forced history's state is read off its operational record. -/
theorem decisionImage_of_history
    (history : (onePacketInformation setup leaks bounds horizon scheduler).InformationHistory who
      site.1)
    (forced : ForcedState setup leaks who history.1.state) :
    decisionImage key history.1.state =
      decisionRecordImage key
        (operationalRecord setup leaks bounds horizon scheduler history.1.trace) := by
  unfold decisionImage decisionRecordImage
  cases turn : turnEvent key with
  | some event =>
      have lumped := lateImage_of_history siteKey history forced
      simp only [lateImage, turn] at lumped
      simp only
      rw [lumped]
  | none =>
      cases binding : bindingTurn key with
      | none => rfl
      | some decided =>
          have spec := bindingTurn_spec binding
          obtain ⟨rest, record⟩ := operationalRecord_head history.1.trace
          rw [record]
          cases current : history.1.state with
          | none =>
              rw [current] at forced
              exact forced.elim
          | some control =>
              have ready := ready_of_ownTurn siteKey history current spec.1
              have empty := commitStatuses_nil_of_unsent siteKey history current spec.2.2
                decided.2
              rw [← owner_of_lateKey siteKey] at empty
              simp only [bindingImage, stateStatuses, empty,
                pendingImage_of_pending control ready.1, attachStatuses, List.head?_cons,
                Option.getD_some]

end Fields

/-- Kept states stay kept along the control step of every decoded profile. -/
theorem decisionKept_step (key : LateKey setup leaks)
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {state : (application setup leaks).ProtocolState}
    (kept : state ∈ decisionKept bounds horizon scheduler key)
    {next : (application setup leaks).ProtocolState}
    (member : next ∈ ((application setup leaks).controlStep (initialLaw setup) horizon scheduler
      ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon
        scheduler profile) state).support) :
    next ∈ decisionKept bounds horizon scheduler key := by
  unfold decisionKept at kept ⊢
  cases decided : decidedEvent key with
  | none => trivial
  | some event =>
      rw [decided] at kept
      obtain ⟨⟨history, current⟩, control, rfl, status⟩ := kept
      obtain ⟨extended, reached⟩ := controlStep_history bounds horizon scheduler profile history
        (by rw [current]; exact member)
      obtain ⟨control', rfl, step⟩ := controlStep_configStep horizon scheduler _ control member
      refine ⟨⟨extended, reached⟩, control', rfl, ?_⟩
      rcases status with completed | ⟨forced, ready⟩
      · exact Or.inl (completed_of_configStep step completed)
      · exact forced_or_completed_of_configStep step forced ready

open Classical in
/-- Failure of a kept state is read off its image. -/
theorem decisionFailed_eq (key : LateKey setup leaks)
    {state : (application setup leaks).ProtocolState}
    (kept : state ∈ decisionKept bounds horizon scheduler key) :
    (if DecisionFailed key state then (1 : ℝ) else 0) =
      decisionFailure (decisionImage key state) := by
  unfold decisionKept at kept
  cases decided : decidedEvent key with
  | none =>
      have turn : turnEvent key = none := by
        unfold decidedEvent at decided
        cases turn : turnEvent key with
        | none => rfl
        | some _ => rw [turn] at decided; cases decided
      have binding : bindingTurn key = none := by
        unfold decidedEvent at decided
        rw [turn] at decided
        cases binding : bindingTurn key with
        | none => rfl
        | some _ => rw [binding] at decided; cases decided
      cases state with
      | none => simp only [DecisionFailed, ↓reduceIte, decisionImage, turn, binding,
          decisionFailure, imageFailure, Bool.false_eq_true]
      | some control => simp only [DecisionFailed, decided, ↓reduceIte, decisionImage, turn,
          binding, decisionFailure, imageFailure, Bool.false_eq_true]
  | some event =>
      rw [decided] at kept
      obtain ⟨_, control, rfl, _⟩ := kept
      unfold decidedEvent at decided
      cases turn : turnEvent key with
      | some published =>
          rw [turn] at decided
          cases decided
          by_cases completed : event ∈ control.execution.application.config.cut.completed
          · simp only [DecisionFailed, decidedEvent, turn, completed, true_and, ↓reduceIte,
              decisionImage, pendingImage, decisionFailure, imageFailure, decide_eq_true_eq]
          · simp only [DecisionFailed, decidedEvent, turn, completed, false_and, ↓reduceIte,
              decisionImage, pendingImage, decisionFailure, imageFailure]
      | none =>
          rw [turn] at decided
          cases binding : bindingTurn key with
          | none => rw [binding] at decided; cases decided
          | some pair =>
              rw [binding] at decided
              cases decided
              by_cases completed : pair.1 ∈ control.execution.application.config.cut.completed
              · simp only [DecisionFailed, decidedEvent, turn, binding, Option.map_some,
                  completed, true_and, ↓reduceIte, decisionImage, bindingImage, pendingImage,
                  attachStatuses, decisionFailure, decide_eq_true_eq]
              · simp only [DecisionFailed, decidedEvent, turn, binding, Option.map_some,
                  completed, false_and, ↓reduceIte, decisionImage, bindingImage, pendingImage,
                  attachStatuses, decisionFailure]

omit [Fintype Player] in
private theorem unitClose_of_eq' {α : Type} {δ : ℝ} (nonneg : 0 ≤ δ) {μ ν : PMF α}
    (same : μ = ν) : UnitClose δ μ ν := by
  intro f _
  rw [same, sub_self, abs_zero]
  exact nonneg

omit [Fintype Player] in
private theorem unitClose_mono {α : Type} {δ δ' : ℝ} {μ ν : PMF α} (close : UnitClose δ μ ν)
    (le : δ ≤ δ') : UnitClose δ' μ ν := fun f unit => (close f unit).trans le

omit [Fintype Player] in
private theorem unitClose_map {α β : Type} {δ : ℝ} {μ ν : PMF α} (close : UnitClose δ μ ν)
    (f : α → β) : UnitClose δ (μ.map f) (ν.map f) := by
  intro g unit
  rw [expect_map, expect_map]
  exact close (g ∘ f) fun a => unit (f a)

/-- **One step at a pending binding.** From a kept state, the control step of
a decoded profile, read through the binding image, is within `2 δ` on unit
payoffs of the binding kernel, provided the owner's law of moves is within
`δ`. -/
theorem bindingKernel_close {LateOption : Type}
    (moves : LateKey setup leaks → LateOption →
      Option (OperationalState setup leaks) × List (MessageId Player × Bool) →
        PMF (Option (Handle (graph setup))))
    (key : LateKey setup leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup leaks bounds horizon scheduler).BehavioralPolicy player)
    {δ : ℝ} (nonneg : 0 ≤ δ)
    (law : OwnerBindingLaw bounds horizon scheduler moves key option profile δ)
    {event : (graph setup).EventId} {payload : L.Ty} (turn : BindingTurn key event payload)
    (history : (onePacketProtocol setup leaks bounds horizon scheduler).History)
    {control : (application setup leaks).Control} (current : history.state = some control)
    (status : event ∈ control.execution.application.config.cut.completed ∨
      (ForcedState setup leaks key.owner (some control) ∧
        control.execution.application.config.cut.Ready event)) :
    UnitClose (2 * δ) (((application setup leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile) (some control)).map (bindingImage event key.owner payload))
      (bindingKernel horizon scheduler event key.owner payload (moves key option)
        (bindingImage event key.owner payload (some control))) := by
  have twice : 0 ≤ 2 * δ := by linarith
  obtain ⟨_, ⟨outputEq, codeEq, view⟩, _⟩ := turn
  rcases status with completed | ⟨forced, ready⟩
  · apply unitClose_of_eq' twice
    have constant : ((application setup leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile
          (initialLaw setup) horizon scheduler profile) (some control)).map
          (bindingImage event key.owner payload) =
        ((application setup leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile
          (initialLaw setup) horizon scheduler profile) (some control)).map
          (Function.const _ (bindingImage event key.owner payload (some control))) := by
      apply map_congr_on_support
      intro next member
      obtain ⟨control', rfl, step⟩ :=
        controlStep_configStep horizon scheduler _ control member
      have completed' := completed_of_configStep step completed
      have image := pendingImage_of_configStep step completed
      simp only [bindingImage, image, Function.const_apply]
      simp only [pendingImage, completed, ↓reduceIte, attachStatuses]
    rw [constant, PMF.map_const]
    simp only [bindingImage, pendingImage, completed, ↓reduceIte, attachStatuses, bindingKernel]
  · have pending := ready.1
    have imageEq : bindingImage event key.owner payload (some control) =
        .inl (operationalState setup leaks (some control),
          commitStatuses event key.owner payload control.execution.application
            control.execution.network.pending) := by
      simp only [bindingImage, stateStatuses, pendingImage_of_pending control pending,
        attachStatuses]
    rw [imageEq]
    rcases control with ⟨remaining, actor, execution⟩
    cases actor with
    | some player =>
        by_cases owned : player = key.owner
        · subst owned
          have kernelOwner : bindingKernel horizon scheduler event key.owner payload
              (moves key option) (.inl (operationalState setup leaks
                (some ⟨remaining, some key.owner, execution⟩),
                commitStatuses event key.owner payload execution.application
                  execution.network.pending)) =
              (moves key option (operationalState setup leaks
                (some ⟨remaining, some key.owner, execution⟩),
                commitStatuses event key.owner payload execution.application
                  execution.network.pending)).map
                (moveImage event key.owner (operationalState setup leaks
                  (some ⟨remaining, some key.owner, execution⟩),
                  commitStatuses event key.owner payload execution.application
                    execution.network.pending)) := by
            simp only [operationalState, bindingKernel, ↓reduceIte]
          rw [kernelOwner]
          exact ownerBindingStep_close bounds profile history current pending _
            (law event payload ⟨‹_›, ⟨outputEq, codeEq, view⟩, ‹_›⟩ history remaining execution
              current (by rw [current]; exact forced) ready)
        · apply unitClose_of_eq' twice
          rw [controlStep_other_of_pending bounds horizon scheduler profile key.owner history
            (by rw [current]; exact forced) current ready
            (nodeView_bind_actor outputEq codeEq) rfl owned, PMF.pure_map,
            bindingImage_respond_silent pending rfl]
          simp only [operationalState, Option.map_some, bindingKernel, owned, ↓reduceIte]
    | none =>
        cases remaining with
        | zero =>
            apply unitClose_of_eq' twice
            have step : (application setup leaks).controlStep (initialLaw setup) horizon
                scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile
                  (initialLaw setup) horizon scheduler profile) (some ⟨0, none, execution⟩) =
                PMF.pure (some ⟨0, none, execution⟩) := rfl
            rw [step, PMF.pure_map, ← imageEq]
            simp only [bindingImage, stateStatuses, pendingImage_of_pending _ pending,
              attachStatuses, operationalState, bindingKernel]
        | succ remaining =>
            apply unitClose_of_eq' twice
            have step : (application setup leaks).controlStep (initialLaw setup) horizon
                scheduler ((bounds.onePacketMenu (runtime setup) leaks).decodeProfile
                  (initialLaw setup) horizon scheduler profile)
                  (some ⟨remaining + 1, none, execution⟩) =
                (application setup leaks).transition (initialLaw setup) horizon scheduler
                  (some ⟨remaining + 1, none, execution⟩) (fun _ => none) := rfl
            rw [step]
            obtain ⟨state, stateEq⟩ : ∃ state, operationalState setup leaks
                (some ⟨remaining + 1, none, execution⟩) = some state := ⟨_, rfl⟩
            have represented : ∃ other : (application setup leaks).Execution,
                operationalState setup leaks (some ⟨remaining + 1, none, other⟩) = some state ∧
                commitStatuses event key.owner payload other.application
                    other.network.pending =
                  commitStatuses event key.owner payload execution.application
                    execution.network.pending ∧
                other.application.config.cut.Ready event :=
              ⟨execution, stateEq, rfl, ready⟩
            have kernelRound : bindingKernel horizon scheduler event key.owner payload
                (moves key option) (.inl (some state,
                  commitStatuses event key.owner payload execution.application
                    execution.network.pending)) =
                bindingRoundKernel horizon scheduler event key.owner payload remaining
                  (some state, commitStatuses event key.owner payload execution.application
                    execution.network.pending) := by
              have actorNone : state.actor = none := by
                have := congrArg (Option.map OperationalState.actor) stateEq
                simpa only [operationalState, Option.map_some, Option.some.injEq] using
                  this.symm
              have remainingEq : state.remaining = remaining + 1 := by
                have := congrArg (Option.map OperationalState.remaining) stateEq
                simpa only [operationalState, Option.map_some, Option.some.injEq] using
                  this.symm
              simp only [bindingKernel, actorNone, remainingEq]
            rw [stateEq, kernelRound]
            unfold bindingRoundKernel
            rw [dite_eq_left represented]
            obtain ⟨repSame, repStatuses, _⟩ := represented.choose_spec
            exact binding_round_image_congr (initialLaw setup) horizon scheduler remaining
              execution represented.choose (stateEq.trans repSame.symm) repStatuses.symm ready
              view

end Vegas
