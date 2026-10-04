/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveResolutionWindowSupport

/-! # Network state inside a retained disclosure window

Within a served resolve phase every retained response keeps the application.
Before the owner's opening all traffic stays published. The owner's opening is
its only possible submission; afterwards that envelope is pending and
unpublished, and every in-flight envelope is either published or a copy of it.
Replay copies and previously published traffic may remain in flight, but they
identify no other unpublished envelope. Transport responses and passive samples
preserve this, so it holds at every point of every retained roster window, for
arbitrary policies of the permitted menu.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The network at a point of a disclosure window whose application is fixed:
all traffic published before the owner's opening; afterwards the opening is
pending and unpublished, and every in-flight envelope is published or a copy of
it. -/
def ResolutionWindowState (owner : Player) (event : graph.EventId) (application : State graph)
    (execution : (runtime.reactiveApplication leaks).Execution) : Prop :=
  execution.application = application ∧ execution.network.SerialsBeforeNext ∧
    (runtime.eventRecorded leaks (execution.recall owner) event = false →
      execution.network.Satisfies fun message =>
        message.id ∈ execution.network.ledger.map Message.id) ∧
    (runtime.eventRecorded leaks (execution.recall owner) event = true →
      ∃ message : Message Player (WitnessedPacket graph), message.sender = owner ∧
        message.payload.call.event? graph = some event ∧ message ∈ execution.network.pending ∧
        message.id ∉ execution.network.ledger.map Message.id ∧
        execution.network.Satisfies fun packet =>
          packet.id ∈ execution.network.ledger.map Message.id ∨ packet = message)

omit [Fintype Player] in
/-- A transport response records no submission for any player. -/
theorem eventRecorded_respond_transport
    (execution : (runtime.reactiveApplication leaks).Execution) (who observer : Player)
    (response : (runtime.reactiveApplication leaks).Action)
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (event : graph.EventId) :
    runtime.eventRecorded leaks
      ((execution.respond (runtime.reactiveApplication leaks) who response).recall observer) event =
      runtime.eventRecorded leaks (execution.recall observer) event := by
  classical
  rcases transport with rfl | ⟨id, rfl⟩ <;>
  · by_cases same : observer = who
    · subst same
      simp [ReactiveApplication.Execution.respond, eventRecorded, List.any_append,
        submittedEvent?]
    · simp [ReactiveApplication.Execution.respond, same]

omit [Fintype Player] in
/-- An all-published network with no owner submission is a window state. -/
theorem ResolutionWindowState.initial (owner : Player) (event : graph.EventId)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (serials : execution.network.SerialsBeforeNext)
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (unsent : runtime.eventRecorded leaks (execution.recall owner) event = false) :
    runtime.ResolutionWindowState leaks owner event execution.application execution :=
  ⟨rfl, serials, fun _ => published, fun recorded => by
    rw [unsent] at recorded
    cases recorded⟩

omit [Fintype Player] in
/-- A passive sample changes no application, recall, ledger or pending list. -/
theorem ResolutionWindowState.learn {owner : Player} {event : graph.EventId}
    {application : State graph} {execution : (runtime.reactiveApplication leaks).Execution}
    (state : runtime.ResolutionWindowState leaks owner event application execution)
    (who : Player) (sample : Finset (MessageId Player)) :
    runtime.ResolutionWindowState leaks owner event application
      (execution.sampledActivation (runtime.reactiveApplication leaks) who sample) := by
  obtain ⟨sameApp, serials, unsentPublished, recordedMessage⟩ := state
  refine ⟨sameApp, serials.learn who sample, fun unsent =>
    (unsentPublished unsent).learn who sample, fun recorded => ?_⟩
  obtain ⟨message, sender, addressed, pending, unpublished, packets⟩ := recordedMessage recorded
  exact ⟨message, sender, addressed, pending, unpublished, packets.learn who sample⟩

/-- Every retained response of every player keeps the window state of a
served resolve phase. -/
theorem ResolutionWindowState.respond (bounds : MessageBounds graph)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    {application : State graph} {execution : (runtime.reactiveApplication leaks).Execution}
    (state : runtime.ResolutionWindowState leaks owner event application execution)
    (sole : execution.application.publicView.SoleReady event)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)) :
    runtime.ResolutionWindowState leaks owner event application
      (execution.respond (runtime.reactiveApplication leaks) who response) := by
  let app := runtime.reactiveApplication leaks
  obtain ⟨sameApp, serials, unsentPublished, recordedMessage⟩ := state
  have applicationAfter := bounds.compiled_resolution_application runtime leaks who execution
    event owner payload binding checks outputEq codeEq node sole response member
  have serialsAfter := (app.serialsBeforeNextInvariant (fun _ _ => PMF.pure .wait)).respond
    execution who response serials
  have transportCase (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩) :
      runtime.ResolutionWindowState leaks owner event application
        (execution.respond app who response) := by
    have recordedEq := runtime.eventRecorded_respond_transport leaks execution who owner response
      transport event
    refine ⟨applicationAfter.trans sameApp, serialsAfter, fun unsent => ?_, fun recorded => ?_⟩
    · rw [recordedEq] at unsent
      have preserved := runtime.replay_response_preserves leaks _ execution
        (unsentPublished unsent) who response transport
      rw [preserved.2.1]
      exact preserved.2.2.2.2.1
    · rw [recordedEq] at recorded
      obtain ⟨message, sender, addressed, pending, unpublished, packets⟩ :=
        recordedMessage recorded
      have preserved := runtime.replay_response_preserves leaks _ execution packets who response
        transport
      refine ⟨message, sender, addressed, preserved.2.2.2.2.2 pending, ?_, ?_⟩
      · rw [preserved.2.1]
        exact unpublished
      · rw [preserved.2.1]
        exact preserved.2.2.2.2.1
  rcases bounds.compiled_resolution_cases runtime leaks who _ _ event owner payload binding checks
    outputEq codeEq node sole response member with silent | replay |
      ⟨candidate, value, evidence, acting, _, _, _, candidateOwned, first, shape⟩
  · exact transportCase (Or.inl silent)
  · exact transportCase (app.replayPolicy_cases _ _ response replay)
  · have owned : graph.actor? event = some owner := by
      have actor := congrArg EventCode.actor codeEq
      rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
      exact actor
    have equal : who = owner := Option.some.inj (acting.symm.trans owned)
    clear candidateOwned
    subst who
    subst response
    let submission : WitnessedSubmission graph :=
      ⟨⟨.opening event candidate ⟨payload, value⟩, none⟩, evidence⟩
    have unsent : runtime.eventRecorded leaks (execution.recall owner) event = false := by
      simpa only [firstSubmission, submittedEvent?, Payload.event?, Bool.not_eq_true'] using first
    have recordedAfter : runtime.eventRecorded leaks
        ((execution.respond app owner ⟨some (.submit submission)⟩).recall owner) event = true :=
      runtime.eventRecorded_respond leaks execution owner _ event rfl
    let packet := app.packet (app.submit execution.application owner submission) owner
      (execution.network.known owner) submission
    let message : Message Player (WitnessedPacket graph) :=
      ⟨(owner, execution.network.nextSerial owner), packet⟩
    refine ⟨applicationAfter.trans sameApp, serialsAfter, fun unsentAfter => ?_,
      fun _ => ⟨message, rfl, rfl, List.mem_append_right _ (List.mem_singleton_self _),
        serials.next_unpublished owner, ?_⟩⟩
    · rw [recordedAfter] at unsentAfter
      cases unsentAfter
    · change (execution.network.submit owner packet).2.Satisfies _
      exact ((unsentPublished unsent).mono (fun _ prior => Or.inl prior)).submit owner packet
        (Or.inr rfl)

/-- Every point of a retained roster window of a sole resolve phase keeps
the window state. -/
theorem ResolutionWindowState.run (bounds : MessageBounds graph)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (lawful : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ bounds.compiledActions runtime leaks who past view)
    (network : runtime.NetworkPolicy leaks)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (visits : List Player) {application : State graph}
    (initial final : (runtime.reactiveApplication leaks).Execution)
    (state : runtime.ResolutionWindowState leaks owner event application initial)
    (sole : initial.application.publicView.SoleReady event)
    (reached : final ∈ (runtime.runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support) :
    runtime.ResolutionWindowState leaks owner event application final := by
  let app := runtime.reactiveApplication leaks
  induction visits generalizing initial with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact state
  | cons who rest ih =>
      obtain ⟨middle, step, tail⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      simp only [interactionStep, interactionInstruction, PMF.pure_bind] at step
      change middle ∈ ((initial.environmentStep app (.activate who)).bind
        (app.invoke players who)).support at step
      rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map] at step
      obtain ⟨sample, _, step⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ step)
      obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ step
      let activated := initial.sampledActivation app who sample
      have activatedState := state.learn runtime leaks who sample
      have activatedSole : activated.application.publicView.SoleReady event := sole
      have next := activatedState.respond runtime leaks bounds owner event payload binding checks
        outputEq codeEq node activatedSole who response (lawful who _ _ response chosen)
      have nextSole : (activated.respond app who response).application.publicView.SoleReady
          event := by
        rw [bounds.compiled_resolution_application runtime leaks who activated event owner payload
          binding checks outputEq codeEq node activatedSole response
          (lawful who _ _ response chosen)]
        exact activatedSole
      exact ih (activated.respond app who response) next nextSole tail

end Vegas.EventGraphRuntime
