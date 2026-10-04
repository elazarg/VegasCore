/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingRequiredStep
import Vegas.Pending.ReactiveBindingForeignInclusion
import Vegas.Pending.ReactiveServiceTraffic

/-! # The complete stopped required-binding block

One fixed legal repair is coupled to an arbitrary effective mixed response and
the whole remaining physical binding block. Every terminal branch either retains
the joint frame, carries an actual rejected traffic record, or has actual public
missed-binding evidence. Foreign responses are never assumed conforming.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- The stopping alternatives follow from actual responses and the protected
service tail. The repaired marginal is the same retained implementation across
all hidden responses, including both detectable and unobservable deviations. -/
theorem required_binding_final_block_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (network : runtime.NetworkPolicy leaks)
    (before : (runtime.reactiveApplication leaks).Execution)
    (sampled : original ∈ (before.environmentStep
      (runtime.reactiveApplication leaks) (.activate owner)).support)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (remaining : Nat) (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (fresh : original.application.candidates.lookup
      (owner, .prepared (original.application.publicView.bindingCount owner)) = .fresh)
    (actualSlot : reactiveFreshSlot
      (repaired.observe (runtime.reactiveApplication leaks) owner).application =
        some (original.application.publicView.bindingCount owner))
    (capacity : original.application.publicView.bindingCount owner < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (turn : original.application.publicView.OwnTurn owner event)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (unused : original.application.HandleUnused
      (owner, .prepared (original.application.publicView.bindingCount owner)))
    (unsent : runtime.eventRecorded leaks (repaired.recall owner) event = false)
    (unbound : original.application.accepted (.inr event) = none)
    (published : original.network.Satisfies fun message => message.sender = owner →
      message.id ∈ original.network.ledger.map Message.id)
    (entered ticks : Nat)
    (activated : original.application.activatedAt event = some entered)
    (due : runtime.deadline event ≤ original.application.clock + ticks - entered)
    (visits : List Player) (absent : owner ∉ visits)
    (serials : original.network.SerialsBeforeNext)
    (coverage : bounds.requiredBindingActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) ⊆
        menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (available : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
          (original.observe (runtime.reactiveApplication leaks) owner)) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    let plan := (visits.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
      (List.replicate ticks .tick ++ [.expire event])
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        (runtime.runInteractionPlan leaks players network plan) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          (runtime.runInteractionPlan leaks players network plan next.1).map
            fun execution => (execution, next.2)) ∧
      ∀ next ∈ coupling.support,
        (∃ record ∈ app.executionTraffic next.1, record.input.envelope.sender = owner ∧
          runtime.permittedServiceEnvelope record.observation record.ledger
            record.input.envelope = false) ∨
        next.1.application.publicView.missedBinding event = true ∨
        Frame runtime leaks next.2.2 owner next.1 next.2.1 := by
  classical
  have turnSome := original.application.publicView.ownTurn?_of_ownTurn owner event turn
  intro app strategy plan
  let serial := original.application.publicView.bindingCount owner
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
  let leftRun (response : app.Action) := runtime.runInteractionPlan leaks players network plan
    (original.respond app owner response)
  let rightRun (response : app.Action) :=
    (runtime.runInteractionPlan leaks players network plan
      (repaired.respond app owner (adjusted response).1)).map
        fun execution => (execution, (adjusted response).2)
  let bad (execution : app.Execution) :=
    (∃ record ∈ app.executionTraffic execution, record.input.envelope.sender = owner ∧
      runtime.permittedServiceEnvelope record.observation record.ledger
        record.input.envelope = false) ∨
    execution.application.publicView.missedBinding event = true
  have responseLaw : strategy.respond memory (repaired.recall owner,
      repaired.observe app owner) = law.map adjusted := by
    change ((implementation runtime leaks owner reference (players owner)).respond memory
      (repaired.recall owner, repaired.observe app owner)).map _ = _
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed,
        PMF.map_comp]
    simp only [law, adjusted, proposed, frame.observed, app, Function.comp_def]
  have owned : graph.actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq (graph.nodes event)] at actor
    exact actor
  have rightReady : repaired.application.publicView.EventReady event := by
    rw [← frame.publicView]
    exact (original.application.publicView_eventReady event).mpr ready
  have rightTurn : repaired.application.publicView.OwnTurn owner event := by
    rw [← frame.publicView]
    exact turn
  have originalFresh : (memory.shadow.inputView runtime leaks
      (repaired.observe app owner)).application.candidates (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have badBranch (response : app.Action)
      (evidence : ∀ final ∈ (leftRun response).support, bad final) :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
        coupling.map Prod.fst = leftRun response ∧ coupling.map Prod.snd = rightRun response ∧
        ∀ next ∈ coupling.support,
          bad next.1 ∨ Frame runtime leaks next.2.2 owner next.1 next.2.1 := by
    refine ⟨bindPairLaw (leftRun response) (fun _ => (rightRun response)),
      bindPairLaw_map_fst .., bindPairLaw_const_map_snd .., ?_⟩
    intro next supported
    left
    apply evidence
    rw [← bindPairLaw_map_fst (leftRun response) (fun _ => rightRun response), PMF.support_map]
    exact ⟨next, supported, rfl⟩
  have existsBranch (response : app.Action) (member : response ∈ law.support) :
      ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
        coupling.map Prod.fst = leftRun response ∧ coupling.map Prod.snd = rightRun response ∧
        ∀ next ∈ coupling.support,
          bad next.1 ∨ Frame runtime leaks next.2.2 owner next.1 next.2.1 := by
    rcases runtime.binding_audit_response_cases leaks bounds original owner remaining event
        payload outputEq codeEq node turn fresh leftRecall serials response
          (available response member) with replay | canonical | departure
    · apply badBranch response
      intro final supported
      right
      have transport : ∀ material, response.transmission ≠ some (.submit material) := by
        intro material
        rcases app.replayPolicy_cases _ _ response replay with rfl | ⟨id, rfl⟩ <;> simp
      apply runtime.last_binding_transport_omission leaks players network original owner event
        payload outputEq codeEq node ready unbound published entered ticks activated due
          visits absent response transport final
      simpa only [leftRun, plan, List.append_assoc, List.singleton_append, List.cons_append,
        List.nil_append]
        using supported
    · obtain ⟨opening, bounded, _, rfl⟩ := canonical
      let response : app.Action :=
        ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩
      have legal : (proposed response).1 ∈ menu.actions owner (repaired.recall owner)
          (repaired.observe app owner) := by
        apply coverage
        exact repairResponse_binding_available runtime leaks bounds owner memory
          (repaired.recall owner) (repaired.observe app owner) event payload outputEq codeEq node
          rightTurn owned rightReady unsent serial actualSlot capacity default opening bounded
          originalFresh
      have adjustedEq : adjusted response = proposed response := by
        dsimp only [adjusted]
        rw [ite_eq_left legal]
      obtain ⟨coupling, first, second, related⟩ := frame.binding_submission_foreign_block_coupling
        players network event payload outputEq codeEq node serial opening fresh ready timely
          unbound unused serials published visits absent ticks
      refine ⟨coupling.map (fun pair => (pair.1, pair.2, (proposed response).2)), ?_, ?_, ?_⟩
      · rw [PMF.map_comp]
        exact first
      · change _ = rightRun response
        dsimp only [rightRun]
        rw [adjustedEq, PMF.map_comp]
        rw [← second, PMF.map_comp]
        rfl
      · intro next supported
        obtain ⟨pair, chosen, rfl⟩ := PMF.support_map .. ▸ supported
        right
        exact related pair chosen
    · obtain ⟨record, emitted, author, forbidden⟩ := departure
      apply badBranch response
      intro final supported
      left
      refine ⟨record, ?_, author, forbidden⟩
      apply runtime.trafficRecord_after_activation_plan leaks players network plan before original
        final owner response remaining sampled record _ supported
      rw [ReactiveApplication.Execution.activation_samples] at sampled
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ sampled
      rw [show app.trafficStep (some ⟨remaining + 1, none, before⟩)
          (some ⟨remaining, none, (before.sampledActivation app owner selected).respond
            app owner response⟩) = app.trafficStep
              (some ⟨remaining, some owner, before.sampledActivation app owner selected⟩)
              (some ⟨remaining, none, (before.sampledActivation app owner selected).respond
                app owner response⟩) from rfl, emitted]
      exact List.mem_singleton_self _
  let branch := fun response member => (existsBranch response member).choose
  refine ⟨law.bindOnSupport branch, ?_, ?_, ?_⟩
  · rw [map_bindOnSupport]
    change _ = (law.map (original.respond app owner)).bind _
    rw [PMF.bind_map]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro response member
    exact (existsBranch response member).choose_spec.1
  · rw [map_bindOnSupport]
    simp only [ReactiveApplication.Implementation.resume, ↓reduceIte, PMF.bind_map]
    change _ = (strategy.respond memory (repaired.recall owner,
      repaired.observe app owner)).bind _
    rw [responseLaw, PMF.bind_map]
    apply bindOnSupport_eq_bind_of_eq_on_support _
    intro response member
    exact (existsBranch response member).choose_spec.2.1
  · intro next supported
    obtain ⟨response, member, reached⟩ :=
      Set.mem_iUnion₂.mp (PMF.support_bindOnSupport .. ▸ supported)
    rcases (existsBranch response member).choose_spec.2.2 next reached with bad | good
    · exact bad.elim Or.inl (fun omitted => Or.inr (Or.inl omitted))
    · exact Or.inr (Or.inr good)

end Vegas.EventGraphRuntime.BindingMemory.Frame
