/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingFrameLaw
import Vegas.Pending.ReactiveBindingMenuRepair

/-! # Protected binding in the legal repaired continuation

The real compiled-menu implementation, including its total off-path fallback,
has the same coupled protected binding law as the private repair. This covers
all bounded canonical hidden material, not only unusable bindings.
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

/-- The finite mixed protected binding branch is realized by an actual legal
compiled-menu continuation. In particular the same repaired strategy works
across all hidden initial executions sharing its private-memory seed. -/
theorem binding_retained_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph)
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
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
    (actualSlot : reactiveFreshSlot
      (repaired.observe (runtime.reactiveApplication leaks) owner).application = some serial)
    (capacity : serial < bounds.candidateCount)
    (default : (⟨payload, L.someValue payload⟩ : Raw L) ∈ bounds.values)
    (granted : repaired.application.serviceGrant = some event)
    (ready : original.application.config.cut.Ready event)
    (unsent : runtime.eventRecorded leaks (repaired.recall owner) event = false)
    (timely : original.application.WithinDeadline runtime event)
    (vacant : original.application.accepted (.inr event) = none)
    (unused : original.application.HandleUnused (owner, .prepared serial))
    (serials : original.network.SerialsBeforeNext)
    (coverage : bounds.requiredBindingActions runtime leaks owner (repaired.recall owner)
      (repaired.observe (runtime.reactiveApplication leaks) owner) ⊆
        menu.actions owner (repaired.recall owner)
          (repaired.observe (runtime.reactiveApplication leaks) owner))
    (canonical : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      ∃ opening, bounds.AllowsOpening opening ∧ response =
        ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks menu owner reference (players owner)
    ∃ coupling : FinDist (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = (app.invoke players owner original).bind
        (runtime.interactionStep leaks players scheduler (.includeLatest event owner)) ∧
      coupling.map Prod.snd =
        (strategy.resume owner players (some owner) repaired memory).bind (fun next =>
          (runtime.interactionStep leaks players scheduler (.includeLatest event owner)
            next.1).map fun execution => (execution, next.2)) ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 := by
  let app := runtime.reactiveApplication leaks
  have owned : graph.actor? event = some owner := by
    have actor := congrArg EventCode.actor codeEq
    rw [EventCode.actor_cast outputEq ((graph.nodes event))] at actor
    exact actor
  have rightReady : repaired.application.publicView.EventReady event := by
    rw [← frame.publicView]
    exact (original.application.publicView_eventReady event).mpr ready
  have originalFresh : (memory.shadow.inputView runtime leaks
      (repaired.observe app owner)).application.candidates (.prepared serial) = .fresh := by
    rw [frame.observed]
    exact fresh
  have currentCanonical : ∀ response ∈ (players owner
      (memory.restoreRecall runtime leaks (repaired.recall owner))
      (memory.shadow.inputView runtime leaks (repaired.observe app owner))).support,
      ∃ opening, bounds.AllowsOpening opening ∧ response =
        ⟨some (.submit ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩)⟩ := by
    rw [frame.past, frame.observed]
    exact canonical
  have responseEq := retainedImplementation_binding_response runtime leaks bounds menu owner
    reference
    (players owner) memory (repaired.recall owner) (repaired.observe app owner) event payload
    outputEq codeEq node granted owned rightReady unsent serial actualSlot capacity default
      originalFresh
      coverage currentCanonical
  have resumeEq :
      (retainedImplementation runtime leaks menu owner reference (players owner)).resume
        owner players (some owner) repaired memory =
      (implementation runtime leaks owner reference (players owner)).resume
        owner players (some owner) repaired memory := by
    simp only [ReactiveApplication.Implementation.resume, ↓reduceIte]
    rw [responseEq]
  obtain ⟨coupling, first, second, related⟩ := frame.binding_response_coupling players scheduler
    reference started event payload outputEq codeEq node serial fresh ready timely vacant unused
    serials (fun response member => by
      obtain ⟨opening, _, equal⟩ := canonical response member
      exact ⟨opening, equal⟩)
  refine ⟨coupling, first, ?_, related⟩
  rw [resumeEq]
  exact second

end Vegas.EventGraphRuntime.BindingMemory.Frame
