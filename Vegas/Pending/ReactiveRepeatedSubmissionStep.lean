/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingAuditStep

/-! # A repeated fresh submission is a stopped audit departure

Before reserved inclusion, a prior fresh submission has increased the sender's
serial while the published count is unchanged. Every further fresh packet is
then rejected by the public checker, independent of its event or payload. Known
replays and silence preserve the actual joint repair; their identifiers are not
charged again.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

/-- The unpublished serial check distinguishes every further fresh response
from existing-envelope forwarding. It uses actual serial freshness, so the
published-ID exception cannot accidentally admit the new envelope. -/
theorem repeated_submission_response_cases (bounds : MessageBounds graph)
    (execution : (runtime.reactiveApplication leaks).Execution) (owner : Player)
    (remaining : Nat)
    (recalled : execution.InputRecall (runtime.reactiveApplication leaks))
    (serials : execution.network.SerialsBeforeNext)
    (repeated : execution.network.nextSerial owner ≠
      Message.distinctAuthoredCount execution.network.ledger owner)
    (response : (runtime.reactiveApplication leaks).Action)
    (available : response ∈ (bounds.menu runtime leaks).actions owner (execution.recall owner)
      (execution.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    response ∈ (app.replayPolicy (execution.recall owner) (execution.observe app owner)).support ∨
      ∃ record, app.trafficStep (some ⟨remaining, some owner, execution⟩)
          (some ⟨remaining, none, execution.respond app owner response⟩) = [record] ∧
        record.input.envelope.sender = owner ∧
        runtime.permittedServiceEnvelope record.observation record.ledger
          record.input.envelope = false := by
  classical
  let app := runtime.reactiveApplication leaks
  have member := (bounds.menu_mem runtime leaks owner _ _ response).mp available
  have known := app.known_from_recall execution owner recalled
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact Or.inl (app.replayPolicy_support _ _ none (Finset.mem_insert_self _ _))
  | some transmission =>
      cases transmission with
      | replay id =>
          obtain ⟨message, present, same⟩ :=
            (ReactiveApplication.SubmissionNormalization.replayKnown_iff execution owner
              recalled id).mp member.1
          apply Or.inl
          apply app.replayPolicy_support _ _ (some id)
          apply Finset.mem_insert_of_mem
          apply Finset.mem_image.mpr
          refine ⟨id, ?_, rfl⟩
          apply List.mem_toFinset.mpr
          apply List.mem_map.mpr
          rw [known] at present
          exact ⟨message, present, same⟩
      | submit submission =>
          let record : app.TrafficRecord :=
            ⟨execution.application.publicView, execution.network.ledger,
              ⟨owner, ⟨(owner, execution.network.nextSerial owner), submission.emit
                (app.submit execution.application owner submission) owner
                  (execution.network.known owner)⟩⟩⟩
          refine Or.inr ⟨record, app.trafficStep_submit execution remaining owner submission,
            rfl, ?_⟩
          exact runtime.permittedServiceEnvelope_wrong_serial record.observation record.ledger
            record.input.envelope (serials.next_unpublished owner) repeated

namespace BindingMemory.Frame

variable {runtime leaks} {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The fixed legal repair covers a repeated owner opportunity without
requiring the already-fixed candidate to be fresh. Every new submission stops
at actual audit evidence; all known replays keep the same joint frame. -/
theorem repeated_submission_stopped_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (remaining : Nat)
    (serials : original.network.SerialsBeforeNext)
    (repeated : original.network.nextSerial owner ≠
      Message.distinctAuthoredCount original.network.ledger owner)
    (coverage : bounds.compiledActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) ⊆
        menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining, some owner, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.input.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner) := by
  classical
  let app := runtime.reactiveApplication leaks
  let law := players owner (original.recall owner) (original.observe app owner)
  let proposed (response : app.Action) :=
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let adjusted (response : app.Action) :=
    (if (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
        (repaired.observe app owner) then (proposed response).1
      else (menu.nonempty owner (repaired.recall owner) (repaired.observe app owner)).choose,
      (proposed response).2)
  let coupling := law.map fun response =>
    (original.respond app owner response, repaired.respond app owner (adjusted response).1,
      (adjusted response).2)
  have responseLaw :
      (retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) = law.map adjusted := by
    change ((implementation runtime leaks owner reference (players owner)).respond memory
      (repaired.recall owner, repaired.observe app owner)).map _ = _
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed,
        PMF.map_comp]
    simp only [law, adjusted, proposed, frame.observed, app, Function.comp_def]
  have replayLaw := app.replayPolicy_eq_of_network_eq original repaired owner leftRecall
    rightRecall frame.network
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ =
      ((retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner)).map _
    rw [responseLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, selected, rfl⟩ := PMF.support_map .. ▸ supported
    rcases runtime.repeated_submission_response_cases leaks bounds original owner remaining
        leftRecall serials repeated response (available response selected) with replay | departure
    · have unchanged : memory.repairResponse runtime leaks owner
          (repaired.observe app owner) response = (response, memory.shadow) := by
        rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> rfl
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        dsimp only [proposed]
        rw [unchanged]
        rw [replayLaw] at replay
        exact bounds.replay_compiled runtime leaks owner _ _ response replay
      right
      dsimp only [adjusted]
      rw [ite_eq_left legal]
      dsimp only [proposed]
      rw [unchanged]
      refine ⟨frame.transport_response response ?_, ?_, rfl, ?_⟩
      · intro material
        rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> simp
      · rw [app.respond_recall_length]
        omega
      · rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> rfl
    · exact Or.inl departure

/-- The repeated-submission split includes the real passive pending sample at
this visit, without restricting which foreign envelopes may be observed. -/
theorem repeated_submission_stopped_activation_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (remaining : Nat)
    (serials : original.network.SerialsBeforeNext)
    (repeated : original.network.nextSerial owner ≠
      Message.distinctAuthoredCount original.network.ledger owner)
    (coverage : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := repaired.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      bounds.compiledActions runtime leaks owner (activated.recall owner)
        (activated.observe (runtime.reactiveApplication leaks) owner) ⊆
          menu.actions owner (activated.recall owner)
            (activated.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ selected ∈ (leaks owner original.network.pending).support,
      let activated := original.sampledActivation (runtime.reactiveApplication leaks)
        owner selected
      ∀ response ∈ (players owner (activated.recall owner)
        (activated.observe (runtime.reactiveApplication leaks) owner)).support,
          response ∈ (bounds.menu runtime leaks).actions owner (activated.recall owner)
            (activated.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.dispatch players (.activate owner) original ∧
      coupling.map Prod.snd = (repaired.environmentStep app (.activate owner)).bind
        (fun execution => strategy.resume owner players (some owner) execution memory) ∧
      ∀ next ∈ coupling.support,
        (∃ record, app.trafficStep (some ⟨remaining + 1, none, original⟩)
            (some ⟨remaining, none, next.1⟩) = [record] ∧
          record.input.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        (Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.2.2.shadow = memory.shadow ∧
          next.2.1.application.playerView owner = repaired.application.playerView owner) := by
  classical
  let app := runtime.reactiveApplication leaks
  let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
  let sample := leaks owner original.network.pending
  have existsStep (selected) (supported : selected ∈ sample.support) :=
    (frame.activate owner selected).repeated_submission_stopped_response_coupling
      bounds menu players
      reference started leftRecall rightRecall remaining (serials.learn owner selected) repeated
      (coverage selected supported) (available selected supported)
  let step := fun selected supported => (existsStep selected supported).choose
  refine ⟨sample.bindOnSupport step, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    change _ = (original.environmentStep app (.activate owner)).bind _
    rw [ReactiveApplication.Execution.activation_samples, PMF.bind_map]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.1
  · rw [map_bindOnSupport, ReactiveApplication.Execution.activation_samples,
      PMF.bind_map]
    have same : leaks owner repaired.network.pending = sample := by
      rw [← frame.network]
    change _ = (leaks owner repaired.network.pending).bind _
    rw [same]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro selected supported
    exact (existsStep selected supported).choose_spec.2.1
  · intro next supported
    obtain ⟨selected, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    rcases (existsStep selected member).choose_spec.2.2 next reached with bad | good
    · left
      exact bad
    · exact Or.inr good

end BindingMemory.Frame

end Vegas.EventGraphRuntime
