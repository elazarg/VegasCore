/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketPendingLumping
import Vegas.Pending.EventActivationOrigin

/-! # The image kernel of the one-packet game at a pending publication

At a late-delivery key whose owner's turn is a publication event, the image of
a protocol state is its operational state while the event is pending and
whether the event failed once it has completed (`Vegas.pendingImage`). Every
step of the native kernel from a forced state with the event ready is then
read off the image: scheduler rounds (`Vegas.round_image_congr_of_forced`),
silent responses of the other players (`Vegas.controlStep_other_of_pending`),
and the absorbing completed states. Only the owner's own responses remain, and
they enter as one hypothesis: read through the image, the owner's step is
within `δ` in total variation of a kernel of the key, the option and the
operational state (`Vegas.OwnerStepClose`). Under it, the step of the native
kernel from every kept state, read through the image, is within `δ` of the
key's image kernel (`Vegas.lateKernel_close`). At a key whose owner's turn is
not a publication event, the image is constant and nothing is claimed.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- **A publication turn of a key.** It is the key owner's turn at the event in
the key's public view, and the event resolves a binding of the owner. -/
def PublicationTurn (key : LateKey setup runtime leaks) (event : (graph setup).EventId) : Prop :=
  key.current.1.ownTurn? key.owner = some event ∧
    ∃ (payload : L.Ty) (binding : EventGraph.FieldRef (graph setup).layout
        (.binding key.owner payload))
      (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
      (outputEq : (graph setup).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .resolve key.owner payload binding
          checks),
      nodeView (graph setup) event = .resolve key.owner payload binding
        checks outputEq codeEq

open Classical in
/-- The publication event a key decides, if any. -/
def turnEvent (key : LateKey setup runtime leaks) : Option (graph setup).EventId :=
  if turn : ∃ event, PublicationTurn (runtime := runtime) key event then some turn.choose else none

theorem publicationTurn_of_turnEvent {key : LateKey setup runtime leaks} {event : (graph
  setup).EventId}
    (found : turnEvent (runtime := runtime) key = some event) : PublicationTurn (runtime :=
      runtime) key event := by
  unfold turnEvent at found
  split at found
  · rename_i turn
    cases found
    exact turn.choose_spec
  · cases found

/-- The image of the pending lumping. -/
abbrev PendingImage := Option (OperationalState setup runtime leaks) ⊕ Bool

open Classical in
/-- The image at a key: the pending image of the decided event, constant at a
key deciding none. -/
def lateImage (key : LateKey setup runtime leaks) (state : (application setup runtime
  leaks).ProtocolState) :
    PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) :=
  match turnEvent (runtime := runtime) key with
  | none => .inr false
  | some event => pendingImage (runtime := runtime) event state

/-- Failure read off the image. -/
def imageFailure : PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) → ℝ
  | .inl _ => 0
  | .inr failed => if failed then 1 else 0

/-- The image of a history read off its operational record: the newest
operational state, pending. -/
def recordImage (key : LateKey setup runtime leaks)
    (record : List (Option (OperationalState setup runtime leaks))) :
    PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) :=
  match turnEvent (runtime := runtime) key with
  | none => .inr false
  | some _ => match record with
    | [] => .inl none
    | newest :: _ => .inl newest

variable [Fintype Player] (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

open Classical in
/-- A scheduler round from an operational state, read through the image of a
representative forced state with the event ready; the state itself when there
is none. -/
def roundKernel (event : (graph setup).EventId) (owner : Player) (remaining : Nat)
    (state : OperationalState setup runtime leaks) : PMF (PendingImage (runtime := runtime) (setup
      := setup) (leaks := leaks)) :=
  if represented : ∃ (history : (onePacketProtocol setup runtime leaks bounds horizon
    scheduler).History)
      (execution : (application setup runtime leaks).Execution),
      history.state = some ⟨remaining + 1, none, execution⟩ ∧
        ForcedState setup runtime leaks owner history.state ∧
        execution.application.config.cut.Ready event ∧
        operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩) = some state
          then
    ((application setup runtime leaks).transition (initialLaw setup) horizon scheduler
      (some ⟨remaining + 1, none, represented.choose_spec.choose⟩) (fun _ => none)).map
        (pendingImage (runtime := runtime) event)
  else PMF.pure (.inl (some state))

/-- **The pending kernel.** Completed and uninitialized images stay put; the
owner's step is ownerStep; another player's step is its silent response; a
scheduler round is read off a representative. -/
def pendingKernel (event : (graph setup).EventId) (owner : Player)
    (ownerStep : Option (OperationalState setup runtime leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks))) :
    PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks))
  | .inr failed => PMF.pure (.inr failed)
  | .inl none => PMF.pure (.inl none)
  | .inl (some state) => match state.actor with
    | some player => if player = owner then ownerStep (some state)
        else PMF.pure (.inl (some (state.silent player)))
    | none => match state.remaining with
      | 0 => PMF.pure (.inl (some state))
      | remaining + 1 => roundKernel (runtime := runtime) bounds horizon scheduler event owner
        remaining state

/-- The kept states at a key: at a key deciding a publication event, the states
of one-packet histories at which the event has completed, or which are forced
for the key's owner with the event ready. -/
def lateKept (key : LateKey setup runtime leaks) : Set (application setup runtime
  leaks).ProtocolState :=
  match turnEvent (runtime := runtime) key with
  | none => Set.univ
  | some event => {state | (∃ history : (onePacketProtocol setup runtime leaks bounds horizon
      scheduler).History, history.state = state) ∧ ∃ control, state = some control ∧
      (event ∈ control.execution.application.config.cut.completed ∨
        (ForcedState setup runtime leaks key.owner (some control) ∧
          control.execution.application.config.cut.Ready event))}

/-- The image kernel at a key and an option. -/
def lateKernel {LateOption : Type}
    (ownerKernel : LateKey setup runtime leaks → LateOption → Option (OperationalState setup
      runtime leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)))
    (key : LateKey setup runtime leaks) (option : LateOption) :
    PendingImage (runtime := runtime) (setup := setup) (leaks := leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)) :=
  match turnEvent (runtime := runtime) key with
  | none => fun _ => PMF.pure (.inr false)
  | some event => pendingKernel (runtime := runtime) bounds horizon scheduler event key.owner
      (ownerKernel key option)

variable {bounds horizon scheduler}

omit [Fintype Player] in
/-- The key of an observer's information is its own. -/
theorem owner_of_lateKey {who : Player} {info : (application setup runtime leaks).Info}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who info = some
      key) :
    key.owner = who := by
  cases info with
  | none => cases siteKey
  | some info =>
      simp only [lateKey, Option.some.injEq] at siteKey
      rw [← siteKey]

/-- **The key of a site's history.** At a history of a site with a key, the
observer acts, and the key is that of its current information. -/
theorem lateKey_of_history {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    {control : (application setup runtime leaks).Control} (current : history.1.state = some
      control) :
    control.actor = some who ∧
      lateKey setup runtime leaks who (some (control.execution.recall who,
        control.execution.observe (application setup runtime leaks) who)) = some key := by
  have info := history.2
  rw [onePacket_infoOf, current] at info
  rw [← info] at siteKey
  by_cases acting : control.actor = some who
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte] at siteKey
    exact ⟨acting, siteKey⟩
  · simp only [ReactiveApplication.observe, acting, ↓reduceIte, lateKey, reduceCtorEq] at siteKey

/-- At a history of a site whose key decides a publication event, the event is
ready. -/
theorem ready_of_publicationTurn {who : Player}
    {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
    {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some
      key)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    {control : (application setup runtime leaks).Control} (current : history.1.state = some control)
    {event : (graph setup).EventId} (turn : PublicationTurn (runtime := runtime) key event) :
    control.execution.application.config.cut.Ready event := by
  obtain ⟨_, keyEq⟩ := lateKey_of_history (runtime := runtime) siteKey history current
  simp only [lateKey, Option.some.injEq] at keyEq
  have owned := turn.1
  rw [← keyEq] at owned
  have spec := PublicView.ownTurn?_spec _ _ _ owned
  exact (control.execution.application.publicView_eventReady event).mp spec.1

section Fields

variable {who : Player}
  {site : (onePacketInformation setup runtime leaks bounds horizon scheduler).InformationSite who}
  {key : LateKey setup runtime leaks} (siteKey : lateKey setup runtime leaks who site.1 = some key)
include siteKey

omit siteKey in
/-- The image of a forced history's state is read off its operational record. -/
theorem lateImage_of_history
    (siteKey : lateKey setup runtime leaks who site.1 = some key)
    (history : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).InformationHistory who
      site.1)
    (forced : ForcedState setup runtime leaks who history.1.state) :
    lateImage (runtime := runtime) key history.1.state =
      recordImage (runtime := runtime) key (operationalRecord setup runtime leaks bounds horizon
        scheduler history.1.trace) := by
  unfold lateImage recordImage
  cases turn : turnEvent (runtime := runtime) key with
  | none => rfl
  | some event =>
      obtain ⟨rest, record⟩ := operationalRecord_head (runtime := runtime) history.1.trace
      rw [record]
      cases current : history.1.state with
      | none =>
          rw [current] at forced
          exact forced.elim
      | some control =>
          have ready := ready_of_publicationTurn (runtime := runtime) siteKey history current
            (publicationTurn_of_turnEvent (runtime := runtime) turn)
          exact pendingImage_of_pending (runtime := runtime) control ready.1

end Fields

/-- **The owner's step at a key.** Read through the pending image, the
owner's control step from an allowed forced state with the decided event ready
is within `δ` in total variation of a kernel of the key, the option and the
operational state. Every state is allowed unless a restriction is given. -/
def OwnerStepClose {LateOption : Type}
    (ownerKernel : LateKey setup runtime leaks → LateOption → Option (OperationalState setup
      runtime leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)))
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (δ : ℝ) (allowed : (application setup runtime leaks).ProtocolState → Prop := fun _ => True) :
    Prop :=
  ∀ event, PublicationTurn (runtime := runtime) key event →
    ∀ (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
      (control : (application setup runtime leaks).Control), history.state = some control →
      allowed (some control) →
      ForcedState setup runtime leaks key.owner (some control) →
      control.execution.application.config.cut.Ready event →
      control.actor = some key.owner →
      PMF.WithinTV δ (((application setup runtime leaks).controlStep (initialLaw setup) horizon
        scheduler
          ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
            scheduler profile) (some control)).map (pendingImage (runtime := runtime) event))
        (ownerKernel key option (operationalState setup runtime leaks (some control)))

/-- **One step of the native kernel at a key.** From a kept state, the control
step of a decoded profile, read through the key's image, is within `δ` in total
variation of the key's kernel, provided the owner's own step is. -/
theorem lateKernel_close {LateOption : Type}
    (ownerKernel : LateKey setup runtime leaks → LateOption → Option (OperationalState setup
      runtime leaks) →
      PMF (PendingImage (runtime := runtime) (setup := setup) (leaks := leaks)))
    (key : LateKey setup runtime leaks) (option : LateOption)
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {δ : ℝ} (nonneg : 0 ≤ δ) {allowed : (application setup runtime leaks).ProtocolState → Prop}
    (owner : OwnerStepClose (runtime := runtime) ownerKernel key option profile δ allowed)
    {state : (application setup runtime leaks).ProtocolState}
    (kept : state ∈ lateKept (runtime := runtime) bounds horizon scheduler key) (allowedState :
      allowed state) :
    PMF.WithinTV δ (((application setup runtime leaks).controlStep (initialLaw setup) horizon
      scheduler
        ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup) horizon
          scheduler profile) state).map (lateImage (runtime := runtime) key))
      (lateKernel (runtime := runtime) bounds horizon scheduler ownerKernel key option (lateImage
        (runtime := runtime) key state)) := by
  unfold lateKept at kept
  cases turn : turnEvent (runtime := runtime) key with
  | none =>
      convert (PMF.WithinTV.refl _).mono nonneg using 1
      have constant : lateImage (runtime := runtime) key = Function.const _ (.inr false) := by
        funext state
        simp only [lateImage, turn, Function.const_apply]
      simp only [constant, lateKernel, turn, PMF.map_const]
  | some event =>
      rw [turn] at kept
      obtain ⟨⟨history, current⟩, control, rfl, status⟩ := kept
      obtain ⟨_, payload, binding, checks, outputEq, codeEq, view⟩ :=
        publicationTurn_of_turnEvent (runtime := runtime) turn
      have imageEq : lateImage (runtime := runtime) key = pendingImage (runtime := runtime) event
        := by
        funext state
        simp only [lateImage, turn]
      have kernelEq : lateKernel (runtime := runtime) bounds horizon scheduler ownerKernel key
        option =
          pendingKernel (runtime := runtime) bounds horizon scheduler event key.owner
            (ownerKernel key option) := by
        simp only [lateKernel, turn]
      rw [imageEq, kernelEq]
      rcases status with completed | ⟨forced, ready⟩
      · convert (PMF.WithinTV.refl _).mono nonneg using 1
        have constant : ((application setup runtime leaks).controlStep (initialLaw setup) horizon
            scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
              (initialLaw setup) horizon scheduler profile) (some control)).map
              (pendingImage (runtime := runtime) event) =
            ((application setup runtime leaks).controlStep (initialLaw setup) horizon
            scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
              (initialLaw setup) horizon scheduler profile) (some control)).map
              (Function.const _ (pendingImage (runtime := runtime) event (some control))) := by
          apply map_congr_on_support
          intro next member
          obtain ⟨control', rfl, step⟩ :=
            controlStep_configStep (runtime := runtime) horizon scheduler _ control member
          exact pendingImage_of_configStep (runtime := runtime) step completed
        rw [constant, PMF.map_const]
        simp only [pendingImage, completed, ↓reduceIte, pendingKernel]
      · have pending := ready.1
        rw [pendingImage_of_pending (runtime := runtime) control pending]
        rcases control with ⟨remaining, actor, execution⟩
        cases actor with
        | some player =>
            by_cases owned : player = key.owner
            · subst owned
              have kernelOwner : pendingKernel (runtime := runtime) bounds horizon scheduler event
                key.owner
                  (ownerKernel key option) (.inl (operationalState setup runtime leaks
                    (some ⟨remaining, some key.owner, execution⟩))) =
                  ownerKernel key option (operationalState setup runtime leaks
                    (some ⟨remaining, some key.owner, execution⟩)) := by
                simp only [operationalState, pendingKernel, ↓reduceIte]
              rw [kernelOwner]
              exact owner event (publicationTurn_of_turnEvent (runtime := runtime) turn) history _
                current allowedState
                forced ready rfl
            · convert (PMF.WithinTV.refl _).mono nonneg using 1
              rw [controlStep_other_of_pending (runtime := runtime) bounds horizon scheduler
                profile key.owner history
                (by rw [current]; exact forced) current ready
                (nodeView_resolve_actor outputEq codeEq) rfl owned, PMF.pure_map,
                pendingImage_of_pending (runtime := runtime) _ (by
                  change event ∉ (execution.respond (application setup runtime leaks) player
                    ⟨none⟩).application.config.cut.completed
                  rw [(runtime.reactive_respond_application leaks execution player _).1]
                  exact pending),
                operationalState_silent]
              simp only [operationalState, Option.map_some, pendingKernel, owned, ↓reduceIte]
        | none =>
            cases remaining with
            | zero =>
                convert (PMF.WithinTV.refl _).mono nonneg using 1
                have law : (application setup runtime leaks).controlStep (initialLaw setup) horizon
                    scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
                      (initialLaw setup) horizon scheduler profile) (some ⟨0, none, execution⟩) =
                    PMF.pure (some ⟨0, none, execution⟩) := rfl
                rw [law, PMF.pure_map, pendingImage_of_pending (runtime := runtime) _ pending]
                rfl
            | succ remaining =>
                convert (PMF.WithinTV.refl _).mono nonneg using 1
                have law : (application setup runtime leaks).controlStep (initialLaw setup) horizon
                    scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile
                      (initialLaw setup) horizon scheduler profile)
                      (some ⟨remaining + 1, none, execution⟩) =
                    (application setup runtime leaks).transition (initialLaw setup) horizon
                      scheduler
                      (some ⟨remaining + 1, none, execution⟩) (fun _ => none) := rfl
                rw [law]
                obtain ⟨state, stateEq⟩ : ∃ state, operationalState setup runtime leaks
                    (some ⟨remaining + 1, none, execution⟩) = some state := ⟨_, rfl⟩
                have represented : ∃ (history : (onePacketProtocol setup runtime leaks bounds
                  horizon
                      scheduler).History) (execution : (application setup runtime leaks).Execution),
                    history.state = some ⟨remaining + 1, none, execution⟩ ∧
                      ForcedState setup runtime leaks key.owner history.state ∧
                      execution.application.config.cut.Ready event ∧
                      operationalState setup runtime leaks (some ⟨remaining + 1, none, execution⟩) =
                        some state :=
                  ⟨history, execution, current, by rw [current]; exact forced, ready, stateEq⟩
                have kernelRound : pendingKernel (runtime := runtime) bounds horizon scheduler
                  event key.owner
                    (ownerKernel key option) (.inl (some state)) =
                    roundKernel (runtime := runtime) bounds horizon scheduler event key.owner
                      remaining state := by
                  have actorNone : state.actor = none := by
                    have := congrArg (Option.map OperationalState.actor)
                      stateEq
                    simpa only [operationalState, Option.map_some, Option.some.injEq] using
                      this.symm
                  have remainingEq : state.remaining = remaining + 1 := by
                    have := congrArg (Option.map OperationalState.remaining)
                      stateEq
                    simpa only [operationalState, Option.map_some, Option.some.injEq] using
                      this.symm
                  simp only [pendingKernel, actorNone, remainingEq]
                rw [stateEq, kernelRound]
                unfold roundKernel
                rw [dite_eq_left represented]
                obtain ⟨repCurrent, _, _, repSame⟩ :=
                  represented.choose_spec.choose_spec
                exact (round_image_congr_of_forced (runtime := runtime) bounds horizon scheduler
                  key.owner remaining
                  history represented.choose current repCurrent (by rw [current]; exact forced)
                  (stateEq.trans repSame.symm) pending ready view).symm

end Vegas
