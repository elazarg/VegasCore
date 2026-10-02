/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingSubmissionFrame
import Vegas.Pending.ReactiveBindingFrameRounds

/-! # Mixed private binding repair before inclusion

One mixed canonical commitment response couples with its successful-value
repair as soon as the packet is transmitted. The owner's original private
material and response remain in the implementation memory, and all opponents'
inputs and the scheduler's public input agree jointly. No calendar position,
reserved inclusion or inclusion deadline is assumed.

This is a submission step. A whole continuation comparison also needs frame
preservation for subsequent service commands, retained-menu admission and
consistent beliefs. No charge bound is asserted for private unusability.
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

/-- The original mixed response law and the actual private implementation are
the two marginals of one coupling before any scheduler command. Absent and
mistyped private material are allowed in the canonical response law. -/
theorem binding_submission_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
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
    (canonical : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      ∃ opening, response =
        ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩) :
    let app := runtime.reactiveApplication leaks
    let strategy := implementation runtime leaks owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length := by
  let app := runtime.reactiveApplication leaks
  let strategy := implementation runtime leaks owner reference (players owner)
  let law := players owner (original.recall owner) (original.observe app owner)
  let responsePair (response : app.Action) :=
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    (changed.1, (⟨changed.2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩ :
        BindingMemory runtime leaks))
  let coupling := law.map fun response =>
    (original.respond app owner response,
      repaired.respond app owner (responsePair response).1, (responsePair response).2)
  have responseLaw : strategy.respond memory (repaired.recall owner,
      repaired.observe app owner) = law.map responsePair := by
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed]
    simp only [responsePair, law, app, frame.observed]
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp, ReactiveApplication.invoke]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ = (strategy.respond memory
      (repaired.recall owner, repaired.observe app owner)).map _
    rw [responseLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, member, rfl⟩ := PMF.support_map .. ▸ supported
    obtain ⟨opening, rfl⟩ := canonical response member
    refine ⟨frame.binding_submission event payload outputEq codeEq node serial opening
      fresh ready, ?_⟩
    rw [app.respond_recall_length]
    omega

end Vegas.EventGraphRuntime.BindingMemory.Frame
