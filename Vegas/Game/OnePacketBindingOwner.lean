/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketBindingTurn

/-! # The owner's step of the one-packet game at a pending binding

A menu commitment emits the responder's next envelope with the commitment, no
evidence, and the event's token (`Vegas.emittedEnvelope_of_commitment`). When
the owner has no pending commitment to the binding, a commitment of its own to
the binding whose candidate succeeds leads to an image read off the
operational state and the handle: the new envelope joins the network and is
the only pending commitment, with a successful status
(`Vegas.committed_bindingImage`). So if the owner's decoded response, sorted
into silence, such a commitment at each handle, and the rest, is close to a
keyed law of moves (`Vegas.OwnerBindingLaw`), the owner's step is close to the
kernel of that law (`Vegas.ownerBindingStep_close`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- No status in a list for one contract state means none for any other. -/
theorem commitStatuses_eq_nil_congr {event : (graph setup).EventId} {owner : Player}
    {payload : L.Ty} {first second : EventGraphRuntime.State (graph setup)}
    {packets : List (Message Player (application setup runtime leaks).Payload)}
    (empty : commitStatuses (runtime := runtime) event owner payload first packets = []) :
    commitStatuses (runtime := runtime) event owner payload second packets = [] := by
  unfold commitStatuses at empty ⊢
  rw [List.filterMap_eq_nil_iff] at empty ⊢
  intro message member
  have none_ := empty message member
  have someEq := commitStatus_isSome_congr (runtime := runtime) event owner payload first second
    message
  rw [none_] at someEq
  cases status : commitStatus (runtime := runtime) event owner payload second message with
  | none => rfl
  | some _ => rw [status] at someEq; cases someEq

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- **The envelope of a menu commitment.** At a state of a one-packet history,
a one-packet response committing to an event emits the next envelope of the
responder carrying that commitment, no evidence, and the event's token. -/
theorem emittedEnvelope_of_commitment {horizon : Nat}
    {scheduler : (application setup runtime leaks).Scheduler}
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {control : (application setup runtime leaks).Control} (current : history.state = some control)
    (who : Player) (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks who
      (control.execution.recall who) (control.execution.observe (application setup runtime leaks)
        who))
    {submission : (application setup runtime leaks).Submission}
    (sent : action.transmission = some submission)
    {event : (graph setup).EventId} {candidate : Handle (graph setup)}
    (call : submission.call.packet = .commitment event candidate) :
    emittedEnvelope (runtime := runtime) control.execution who action =
      some ⟨(who, control.execution.network.nextSerial who),
        ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩ := by
  rcases ((bounds.mem_onePacketActions runtime leaks who _ _ action).mp member).2 with
    silent | ⟨material, sentMaterial, permitted⟩
  · rw [sent] at silent
    cases silent
  rw [sent] at sentMaterial
  cases sentMaterial
  have trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
    scheduler).Trace
      (some control) :=
    current ▸ (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
      scheduler history.trace
  obtain ⟨inputRecall, serialRecall, _⟩ := runtime.countRecall_history leaks trace
  have local_ := runtime.localEnvelope_eq_of_recall leaks control.execution inputRecall
    serialRecall who submission
  obtain ⟨tokenValid, correct, _⟩ := (countPermits_eq_true_iff _ _).mp permitted
  rw [local_] at tokenValid correct
  unfold emittedEnvelope
  rw [sent]
  simp only [Option.some.injEq, Message.mk.injEq, true_and]
  set packet := (application setup runtime leaks).packet ((application setup runtime leaks).submit
    control.execution.application who submission) who (control.execution.network.known who)
    submission with packetEq
  have packetCall : packet.call = .commitment event candidate := call
  have evidence : packet.evidence = none := by
    unfold CountCallCorrect at correct
    simp only [packetCall] at correct
    exact correct.2.1
  obtain ⟨tokenEvent, tokenNamed, tokenEq⟩ := (WitnessedPacket.tokenValid_iff packet).mp tokenValid
  rw [packetCall] at tokenNamed
  cases tokenNamed
  rcases packetShape : packet with ⟨shapeCall, shapeEvidence, shapeToken⟩
  rw [packetShape] at packetCall evidence tokenEq
  cases packetCall
  cases evidence
  cases tokenEq
  rfl

omit [Fintype Player] in
/-- The image at a pending binding after a response. -/
theorem bindingImage_respond {remaining : Nat} {who : Player}
    {execution : (application setup runtime leaks).Execution} {event : (graph setup).EventId}
    {owner : Player} {payload : L.Ty}
    (pending : event ∉ execution.application.config.cut.completed)
    (action : (application setup runtime leaks).Action) :
    bindingImage (runtime := runtime) event owner payload (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) who action⟩) =
      .inl ((operationalState setup runtime leaks (some ⟨remaining, some who, execution⟩)).map
          (OperationalState.respond who (emittedEnvelope (runtime := runtime)
            execution who action)),
        commitStatuses (runtime := runtime) event owner payload
          (execution.respond (application setup runtime leaks) who action).application
          (execution.respond (application setup runtime leaks) who action).network.pending) := by
  unfold bindingImage
  rw [pendingImage_respond pending]
  rfl

omit [Fintype Player] in
/-- Silence keeps the statuses. -/
theorem bindingImage_respond_silent {remaining : Nat} {who : Player}
    {execution : (application setup runtime leaks).Execution} {event : (graph setup).EventId}
    {owner : Player} {payload : L.Ty}
    (pending : event ∉ execution.application.config.cut.completed)
    {action : (application setup runtime leaks).Action} (silent : action.transmission = none) :
    bindingImage (runtime := runtime) event owner payload (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) who action⟩) =
      .inl ((operationalState setup runtime leaks (some ⟨remaining, some who, execution⟩)).map
          (OperationalState.respond who none),
        commitStatuses (runtime := runtime) event owner payload execution.application
          execution.network.pending) := by
  rw [bindingImage_respond pending]
  rcases action with ⟨transmission⟩
  change transmission = none at silent
  subst silent
  rfl

/-- The image after the owner commits to the binding at a handle with a
successful candidate, from an operational state with no pending commitment of
the owner to the binding. -/
def committedImage (event : (graph setup).EventId) (owner : Player)
    (candidate : Handle (graph setup)) :
    Option (OperationalState setup runtime leaks) → BindingImage (runtime := runtime) (setup :=
      setup) (leaks := leaks)
  | none => .inl (none, [])
  | some state => .inl (some (state.respond owner (some ⟨(owner,
    state.network.nextSerial owner),
      ⟨.commitment event candidate, none, some ⟨event⟩⟩⟩)),
      [((owner, state.network.nextSerial owner), true)])

/-- **A successful commitment is read off the operational state and the
handle.** -/
theorem committed_bindingImage {horizon : Nat} {scheduler : (application setup runtime
  leaks).Scheduler}
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {remaining : Nat} {owner : Player} {execution : (application setup runtime leaks).Execution}
    (current : history.state = some ⟨remaining, some owner, execution⟩)
    {event : (graph setup).EventId} {payload : L.Ty}
    (pending : event ∉ execution.application.config.cut.completed)
    (empty : commitStatuses (runtime := runtime) event owner payload execution.application
      execution.network.pending =
      [])
    (action : (application setup runtime leaks).Action)
    (member : action ∈ bounds.onePacketActions runtime leaks owner
      (execution.recall owner) (execution.observe (application setup runtime leaks) owner))
    {submission : (application setup runtime leaks).Submission}
    (sent : action.transmission = some submission) {candidate : Handle (graph setup)}
    (call : submission.call.packet = .commitment event candidate)
    (succeeds : candidateSucceeds ((application setup runtime leaks).submit execution.application
      owner
      submission) candidate payload = true) :
    bindingImage (runtime := runtime) event owner payload (some ⟨remaining, none,
        execution.respond (application setup runtime leaks) owner action⟩) =
      committedImage (runtime := runtime) event owner candidate
        (operationalState setup runtime leaks (some ⟨remaining, some owner, execution⟩)) := by
  have emitted := emittedEnvelope_of_commitment (runtime := runtime) bounds history current owner
    action member sent
    call
  rw [bindingImage_respond pending, emitted]
  have packetEq : (application setup runtime leaks).packet ((application setup runtime leaks).submit
      execution.application owner submission) owner (execution.network.known owner) submission =
      ⟨.commitment event candidate, none, some ⟨event⟩⟩ := by
    unfold emittedEnvelope at emitted
    rw [sent] at emitted
    exact (Message.mk.inj (Option.some.inj emitted)).2
  rcases action with ⟨transmission⟩
  change transmission = some submission at sent
  subst sent
  have statuses : commitStatuses (runtime := runtime) event owner payload
      (execution.respond (application setup runtime leaks) owner ⟨some submission⟩).application
      (execution.respond (application setup runtime leaks) owner ⟨some
        submission⟩).network.pending =
      [((owner, execution.network.nextSerial owner), true)] := by
    change commitStatuses (runtime := runtime) event owner payload
      ((application setup runtime leaks).submit execution.application owner submission)
      (execution.network.pending ++ [⟨(owner, execution.network.nextSerial owner),
        (application setup runtime leaks).packet ((application setup runtime leaks).submit
          execution.application owner submission) owner (execution.network.known owner)
          submission⟩]) = _
    rw [packetEq]
    unfold commitStatuses
    rw [List.filterMap_append]
    have nil := commitStatuses_eq_nil_congr (runtime := runtime) (second := (application setup
      runtime leaks).submit
      execution.application owner submission) empty
    unfold commitStatuses at nil
    rw [nil]
    simp [commitStatus, succeeds, Message.sender]
  rw [statuses]
  rfl

omit [Fintype Player] in
open Classical in
/-- **The move of an owner's response at a pending binding.** Silence; a
commitment to the binding at a handle whose candidate succeeds, made while the
owner has no pending commitment to it; or anything else, unclassified. -/
def commitMove (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (execution : (application setup runtime leaks).Execution)
    (action : (application setup runtime leaks).Action) : Option (Option (Handle (graph setup))) :=
  if action.transmission = none then some none
  else if committed : ∃ (submission : (application setup runtime leaks).Submission)
      (candidate : Handle (graph setup)), action.transmission = some submission ∧
      submission.call.packet = .commitment event candidate ∧
      candidateSucceeds ((application setup runtime leaks).submit execution.application owner
        submission) candidate payload = true ∧
      commitStatuses (runtime := runtime) event owner payload execution.application
        execution.network.pending = [] then
    some (some committed.choose_spec.choose)
  else none

/-- The image of a move from an operational state and statuses. -/
def moveImage (event : (graph setup).EventId) (owner : Player)
    (image : Option (OperationalState setup runtime leaks) × List (MessageId Player × Bool)) :
    Option (Handle (graph setup)) → BindingImage (runtime := runtime) (setup := setup) (leaks :=
      leaks)
  | none => .inl (image.1.map (OperationalState.respond owner none), image.2)
  | some candidate => committedImage (runtime := runtime) event owner candidate image.1

/-- **The owner's step at a pending binding.** If the owner's decoded response,
sorted into moves, is within `δ` in total variation of a law of moves, its control
step read through the image is within `2 δ` of that law read through the move
images. -/
theorem ownerBindingStep_close {horizon : Nat} {scheduler : (application setup runtime
  leaks).Scheduler}
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (history : (onePacketProtocol setup runtime leaks bounds horizon scheduler).History)
    {remaining : Nat} {owner : Player} {execution : (application setup runtime leaks).Execution}
    (current : history.state = some ⟨remaining, some owner, execution⟩)
    {event : (graph setup).EventId} {payload : L.Ty}
    (pending : event ∉ execution.application.config.cut.completed)
    (moves : PMF (Option (Handle (graph setup)))) {δ : ℝ}
    (close : PMF.WithinTV δ (((bounds.onePacketMenu runtime leaks).decodeProfile
        (initialLaw setup) horizon scheduler profile owner (execution.recall owner)
        (execution.observe (application setup runtime leaks) owner)).map
          (commitMove (runtime := runtime) event owner payload execution)) (moves.map some)) :
    PMF.WithinTV δ (((application setup runtime leaks).controlStep (initialLaw setup) horizon
        scheduler ((bounds.onePacketMenu runtime leaks).decodeProfile (initialLaw setup)
          horizon scheduler profile) (some ⟨remaining, some owner, execution⟩)).map
          (bindingImage (runtime := runtime) event owner payload))
      (moves.map (moveImage (runtime := runtime) event owner
        (operationalState setup runtime leaks (some ⟨remaining, some owner, execution⟩),
          commitStatuses (runtime := runtime) event owner payload execution.application
            execution.network.pending))) := by
  rw [controlStep_owner, PMF.map_comp]
  apply withinTV_map_of_partial_classes _ _ _ _ _ _ close
  intro action supported move classified
  simp only [Function.comp]
  unfold commitMove at classified
  by_cases silent : action.transmission = none
  · simp only [silent, ↓reduceIte, Option.some.injEq] at classified
    subst classified
    rw [bindingImage_respond_silent (runtime := runtime) pending silent]
    rfl
  · simp only [silent, ↓reduceIte] at classified
    split at classified
    · rename_i committed
      cases classified
      obtain ⟨sent, call, succeeds, empty⟩ := committed.choose_spec.choose_spec
      have member := (bounds.onePacketMenu runtime leaks).decodeProfile_support
        (initialLaw setup) horizon scheduler profile owner _ _ action supported
      rw [committed_bindingImage (runtime := runtime) bounds history current pending empty action
        member sent call
        succeeds]
      rfl
    · cases classified

end Vegas
