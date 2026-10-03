/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingResolveLaw
import Vegas.Pending.ReactiveRiskMenu

/-! # Retained withholding under private binding repair

A timely first FALSE decision remains available after binding repair without
using the changed certificate capability. Mixtures of waiting and this decision
have the same actual response law, including implementation memory. Inclusion,
expiry, and payoff comparisons are separate continuation obligations.
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

/-- A first timely FALSE decision belongs to the repaired risk menu even when
the remaining delivery window is unprotected. No certificate is requested. -/
theorem withholding_risk_retained
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.OwnTurn owner event)
    (actor : graph.actor? event = some owner)
    (timely : original.application.WithinDeadline runtime event)
    (unsent : runtime.eventRecorded leaks (original.recall owner) event = false) :
    (⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ : (runtime.reactiveApplication leaks).Action) ∈
      bounds.riskActions runtime leaks bound owner (repaired.recall owner)
        (repaired.observe (runtime.reactiveApplication leaks) owner) := by
  classical
  let app := runtime.reactiveApplication leaks
  have rightTurn : (repaired.observe app owner).application.publicView.ownTurn? owner =
      some event := by
    change repaired.application.publicView.ownTurn? owner = some event
    rw [← frame.publicView]
    exact original.application.publicView.ownTurn?_of_ownTurn owner event turn
  have rightReady : (repaired.observe app owner).application.publicView.EventReady event := by
    change repaired.application.publicView.EventReady event
    rw [← frame.publicView]
    exact turn.1
  have rightTimely :
      (repaired.observe app owner).application.publicView.WithinDeadline runtime event := by
    change repaired.application.publicView.WithinDeadline runtime event
    rw [← frame.publicView]
    exact timely
  have rightUnsent : runtime.eventRecorded leaks (repaired.recall owner) event = false :=
    (runtime.eventRecorded_congr leaks _ _ frame.submissions event).symm.trans unsent
  apply bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
  have chosen := bounds.canonical_resolution_retained runtime leaks owner (repaired.recall owner)
    (repaired.observe app owner) event owner payload binding checks outputEq codeEq node
      rightTurn actor rightReady rightTimely rightUnsent false (by
        simp only [reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true,
          ↓reduceIte, MessageBounds.AllowsPacket])
  rw [runtime.canonicalServiceDecision_resolution_false leaks owner (repaired.recall owner)
    (repaired.observe app owner) event owner payload binding checks outputEq codeEq node] at chosen
  exact chosen

/-- The legal private implementation copies an actual mixture of waiting and
first FALSE decisions. The coupling uses one policy on reconstructed own input,
and its retained-menu fallback is never used on this response support. -/
theorem withholding_risk_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (bound : graph.EventId → Nat)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (turn : original.application.publicView.OwnTurn owner event)
    (actor : graph.actor? event = some owner)
    (timely : original.application.WithinDeadline runtime event)
    (unsent : runtime.eventRecorded leaks (original.recall owner) event = false)
    (withholding : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
        response = ⟨none⟩ ∨ response = ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks (bounds.riskMenu runtime leaks bound)
      owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length := by
  classical
  let app := runtime.reactiveApplication leaks
  let law := players owner (original.recall owner) (original.observe app owner)
  let menu := bounds.riskMenu runtime leaks bound
  let updated (response : app.Action) := memory.record runtime leaks
    (memory.shadow.inputView runtime leaks (repaired.observe app owner)) response
  have unchanged (response : app.Action) (supported : response ∈ law.support) :
      memory.repairResponse runtime leaks owner (repaired.observe app owner) response =
        (response, memory.shadow) := by
    rcases withholding response supported with rfl | rfl <;> rfl
  have retained (response : app.Action) (supported : response ∈ law.support) :
      response ∈ menu.actions owner (repaired.recall owner) (repaired.observe app owner) := by
    rcases withholding response supported with rfl | rfl
    · exact bounds.canonicalActions_subset_risk runtime leaks bound owner _ _
        (bounds.silence_canonical runtime leaks owner _ _)
    · exact frame.withholding_risk_retained bounds bound event payload binding checks outputEq
        codeEq node turn actor timely unsent
  have responseLaw :
      (implementation runtime leaks owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) =
          law.map (fun response => (response, updated response)) := by
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed]
    apply map_congr_on_support _
    intro response supported
    rw [unchanged response supported]
    simp only [updated, record, app, frame.observed]
  have legalLaw :
      (retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) =
          law.map (fun response => (response, updated response)) := by
    rw [retainedImplementation_respond_eq runtime leaks menu owner reference (players owner)
      memory (repaired.recall owner, repaired.observe app owner) (by
        rw [responseLaw]
        intro result supported
        obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ supported
        exact retained response chosen), responseLaw]
  let coupling := law.map fun response =>
    (original.respond app owner response, repaired.respond app owner response, updated response)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simp only [coupling, PMF.map_comp]
    rfl
  · simp only [coupling, PMF.map_comp, ReactiveApplication.Implementation.resume, ↓reduceIte]
    change law.map _ =
      ((retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner)).map _
    rw [legalLaw, PMF.map_comp]
    rfl
  · intro next supported
    obtain ⟨response, member, rfl⟩ := PMF.support_map .. ▸ supported
    refine ⟨?_, ?_⟩
    · rcases withholding response member with rfl | rfl
      · apply frame.transport_response _
        simp
      · exact frame.withholding_response_frame event
    · rw [app.respond_recall_length]
      omega

end Vegas.EventGraphRuntime.BindingMemory.Frame
