/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameOpening

/-! # Actual mixed protected binding responses

The private implementation and the original policy sample the same original
response. Their real response and reserved inclusion laws are the marginals of
one finite coupling. No implementation memory is added to the game state.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Any mixed canonical raw binding law is repaired by the actual private
implementation. The hidden raw material may be usable, absent, or mistyped.
The support condition states the clean branch of the response classification;
it does not assert that all raw deviations are clean. -/
theorem binding_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (completedMemory : memory.shadow.CompletedAt original.application.config)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (scheduler : runtime.NetworkPolicy leaks)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat)
    (fresh : original.application.candidates.lookup (owner, .prepared serial) = .fresh)
    (ready : original.application.config.cut.Ready event)
    (timely : original.application.WithinDeadline runtime event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused (owner, .prepared serial))
    (serials : original.network.SerialsBeforeNext)
    (canonical : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      ∃ opening, response =
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩) :
    let app := runtime.reactiveApplication leaks
    let strategy := implementation runtime leaks owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        (runtime.interactionStep leaks players scheduler (.includeLatest event owner)) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
            next.1).map fun execution => (execution, next.2)) ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.CompletedAt next.1.application.config := by
  let app := runtime.reactiveApplication leaks
  let strategy := implementation runtime leaks owner reference (players owner)
  let law := players owner (original.recall owner) (original.observe app owner)
  let id : MessageId Player := (owner, original.network.nextSerial owner)
  let finish (execution : app.Execution) : app.Execution :=
    { execution.includePending app id with environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .include id⟩] }
  let responsePair (response : app.Action) :=
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let coupling := law.map fun response =>
    (finish (original.respond app owner response),
      finish (repaired.respond app owner (responsePair response).1), (responsePair response).2)
  have selected (execution : app.Execution) (opening : Option (Raw L))
      (before : execution.network.SerialsBeforeNext)
      (nonce : execution.network.nextSerial owner = original.network.nextSerial owner) :
      runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        (execution.respond app owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩) =
        PMF.pure (finish (execution.respond app owner
          ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩)) := by
    rw [runtime.rawBinding_reserved_selection leaks execution owner event serial opening
      before players scheduler, nonce]
    simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
    rfl
  have originalStep (response : app.Action) (member : response ∈ law.support) :
      runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        (original.respond app owner response) =
        PMF.pure (finish (original.respond app owner response)) := by
    obtain ⟨opening, rfl⟩ := canonical response member
    exact selected original opening serials rfl
  have repairedStep (response : app.Action) (member : response ∈ law.support) :
      runtime.interactionStep leaks players scheduler (.includeLatest event owner)
        (repaired.respond app owner (responsePair response).1) =
        PMF.pure (finish (repaired.respond app owner (responsePair response).1)) := by
    obtain ⟨opening, rfl⟩ := canonical response member
    have originalFresh : (memory.shadow.inputView runtime leaks
        (repaired.observe app owner)).application.candidates (.prepared serial) = .fresh := by
      rw [frame.observed]
      exact fresh
    have actualFresh := (frame.slots (.prepared serial)).mp fresh
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        change runtime.interactionStep leaks players scheduler (.includeLatest event owner)
          (repaired.respond app owner
            (memory.repairResponse runtime leaks owner (repaired.observe app owner) _).1) = _
        rw [memory.repairResponse_unusable runtime leaks owner (repaired.observe app owner)
          event payload outputEq codeEq node serial opening originalFresh actualFresh decoded]
        exact selected repaired (some ⟨payload, L.someValue payload⟩)
          (frame.network ▸ serials)
          (congrArg (fun net => net.nextSerial owner) frame.network.symm)
    | some value =>
        change runtime.interactionStep leaks players scheduler (.includeLatest event owner)
          (repaired.respond app owner
            (memory.repairResponse runtime leaks owner (repaired.observe app owner) _).1) = _
        rw [congrArg Prod.fst (memory.repairResponse_usable runtime leaks owner
          (repaired.observe app owner) event payload outputEq codeEq node serial opening
          originalFresh actualFresh value decoded)]
        exact selected repaired opening (frame.network ▸ serials)
          (congrArg (fun net => net.nextSerial owner) frame.network.symm)
  have responseLaw : strategy.respond memory (repaired.recall owner,
      repaired.observe app owner) = law.map responsePair := by
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed]
    simp only [responsePair, law, app, frame.observed]
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp, ReactiveApplication.invoke, PMF.bind_map, Function.comp_def]
    change law.map (fun response => finish (original.respond app owner response)) = _
    rw [← PMF.bind_pure_comp, Function.comp_def]
    apply bind_congr_on_support _
    intro response member
    exact (originalStep response member).symm
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume,
      ↓reduceIte, PMF.bind_map, Function.comp_def]
    change law.map (fun response =>
      (finish (repaired.respond app owner (responsePair response).1),
        (responsePair response).2)) =
      (strategy.respond memory (repaired.recall owner, repaired.observe app owner)).bind
        (fun response => (runtime.interactionStep leaks players scheduler
          (.includeLatest event owner) (repaired.respond app owner response.1)).map
            fun execution => (execution, response.2))
    rw [responseLaw, PMF.bind_map]
    rw [← PMF.bind_pure_comp, Function.comp_def]
    apply bind_congr_on_support _
    intro response member
    simp only [Function.comp_apply]
    rw [repairedStep response member, PMF.pure_map]
  · intro next member
    obtain ⟨response, supported, rfl⟩ := PMF.support_map .. ▸ member
    obtain ⟨opening, rfl⟩ := canonical response supported
    refine ⟨frame.binding event payload outputEq codeEq node serial opening
      (fun _ _ => completedMemory.ready_none event ready) fresh ready timely vacant unused serials,
      ?_⟩
    have configLaw := runtime.rawBinding_reserved_config leaks original owner event payload
      outputEq codeEq node serial opening ready timely fresh vacant unused serials players scheduler
    change (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
      (original.respond app owner
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩)).map
          (fun final => (final.application.config, final.receipts)) = _ at configLaw
    rw [selected original opening serials rfl, PMF.pure_map] at configLaw
    have configEq := congrArg Prod.fst ((PMF.mem_support_pure_iff _ _).mp
      (configLaw ▸ ((PMF.mem_support_pure_iff _ _).mpr rfl)))
    let final := finish (original.respond app owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩)
    change final.application.config = _ at configEq
    have advanced : original.application.config.cut.completed ⊆
        final.application.config.cut.completed := by
      rw [configEq, Config.complete_cut]
      exact fun _ present => Finset.mem_insert_of_mem present
    have completed : event ∈ final.application.config.cut.completed := by
      rw [configEq, Config.complete_cut]
      exact Finset.mem_insert_self _ _
    exact memory.repairResponse_completedAt runtime leaks owner (repaired.observe app owner)
      event payload outputEq codeEq node serial opening
      (by rw [frame.observed]; exact fresh) ((frame.slots (.prepared serial)).mp fresh)
      original.application.config _ completedMemory advanced completed

end Vegas.EventGraphRuntime.BindingMemory.Frame
