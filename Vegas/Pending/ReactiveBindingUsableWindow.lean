/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveBindingUsableProvenance
import Vegas.Pending.ReactiveBindingInertWindow

/-! # Joint owner responses with later fresh usable bindings

One effective policy is sampled at reconstructed own input. Its noncommitment
responses and fresh typed registrations preserve the actual frame, completed
memory and commitment provenance. The private implementation has no fallback
on this support. This concerns the complete bounded effective menu, not admission
to the service risk menu or a whole-policy payoff comparison.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A fresh usable registration is described entirely by the owner's actual
input and selected response, including the typed private opening. -/
def FreshUsableBindingResponse (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (view : ReactivePlayerView graph)
    (response : (runtime.reactiveApplication leaks).Action) : Prop :=
  ∃ (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind owner payload)
    (serial : Nat) (raw : Raw L) (value : L.Val payload),
      nodeView graph event = .bind owner payload outputEq codeEq ∧
      view.publicView.EventReady event ∧ view.candidates (.prepared serial) = .fresh ∧
      raw.as? payload = some value ∧
      response = ⟨some ⟨⟨.commitment event (owner, .prepared serial), some raw⟩, .none⟩⟩

namespace BindingMemory.Frame

variable [Fintype Player]

variable {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

omit [Fintype Player] in
private theorem same_response_openable
    (frame : Frame runtime leaks memory owner original repaired)
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (response : (runtime.reactiveApplication leaks).Action) :
    let app := runtime.reactiveApplication leaks
    ∀ slot raw,
      (original.respond app owner response).application.candidates.lookup (owner, slot) =
        .openable raw →
      (repaired.respond app owner response).application.candidates.lookup (owner, slot) =
        .openable raw := by
  intro app slot raw available
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => exact preserved slot raw available
  | some material =>
      change (submitStep (material.call.register original.application owner) owner
        material.call.packet).candidates.lookup (owner, slot) = .openable raw at available
      change (submitStep (material.call.register repaired.application owner) owner
        material.call.packet).candidates.lookup (owner, slot) = .openable raw
      rw [material.call.candidateAfter_eq] at available ⊢
      exact material.call.candidateAfter_openable_mono owner _ _ frame.slots preserved slot raw
        available

/-- Actual selected owner responses preserve full private reconstruction and
the evolving completed-or-matching ledger. Certificate and effective-menu
transport are derived from the original normal form and actual capabilities. -/
theorem usable_response_resources
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsSettledOrMatching owner original repaired)
    (bounds : MessageBounds graph)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (response : (runtime.reactiveApplication leaks).Action)
    (effective : response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner))
    (usable : (∀ material, response.transmission = some material →
        ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
      FreshUsableBindingResponse runtime leaks owner
        (original.observe (runtime.reactiveApplication leaks) owner).application response) :
    let app := runtime.reactiveApplication leaks
    let changed := memory.repairResponse runtime leaks owner (repaired.observe app owner) response
    let updated : BindingMemory runtime leaks :=
      ⟨changed.2, memory.responses ++
        [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩
    let left := original.respond app owner response
    let right := repaired.respond app owner changed.1
    changed.1 = response ∧ Frame runtime leaks updated owner left right ∧
      updated.shadow.OwnBindings owner ∧ updated.shadow.CompletedAt left.application.config ∧
      OwnerCommitmentsSettledOrMatching owner left right ∧
      ∀ slot raw, left.application.candidates.lookup (owner, slot) = .openable raw →
        right.application.candidates.lookup (owner, slot) = .openable raw := by
  intro app changed updated left right
  have transported := runtime.effectiveResponse_openable_transport leaks bounds owner
    original repaired leftRecall rightRecall frame.network frame.publicView frame.slots
      preserved response effective
  rcases usable with noncommitment | freshUsable
  · have changedEq := memory.repairResponse_noncommitment runtime leaks owner
      (repaired.observe app owner) response noncommitment
    have same : changed.1 = response := congrArg Prod.fst changedEq
    have shadow : updated.shadow = memory.shadow := congrArg Prod.snd changedEq
    have inert (execution : app.Execution) :
        (execution.respond app owner response).application = execution.application := by
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => rfl
      | some material =>
          exact reactiveApplication_submit_noncommitment runtime leaks
            execution.application owner material (noncommitment material rfl)
    refine ⟨same, ?_, shadow.symm ▸ onlyBindings, ?_, ?_, ?_⟩
    · change Frame runtime leaks updated owner left (repaired.respond app owner changed.1)
      rw [same]
      rcases response with ⟨transmission⟩
      cases transmission with
      | none =>
          simpa only [updated, changed, changedEq, BindingMemory.record] using
            frame.transport_response (⟨none⟩ : app.Action) (by simp)
      | some material =>
          have leftInert := reactiveApplication_submit_noncommitment runtime leaks
            original.application owner material (noncommitment material rfl)
          have rightInert := reactiveApplication_submit_noncommitment runtime leaks
            repaired.application owner material (noncommitment material rfl)
          have packet := transported.2.2 material rfl
          rw [leftInert, rightInert] at packet
          simpa only [updated, changed, changedEq, BindingMemory.record] using
            frame.inert_submission material material leftInert rightInert packet
    · rw [shadow, inert original]
      exact past
    · change OwnerCommitmentsSettledOrMatching owner left
        (repaired.respond app owner changed.1)
      rw [same]
      exact provenance.respond_noncommitment owner response response (fun _ => noncommitment)
    · change ∀ slot raw, left.application.candidates.lookup (owner, slot) = .openable raw →
        (repaired.respond app owner changed.1).application.candidates.lookup (owner, slot) =
          .openable raw
      rw [same]
      exact frame.same_response_openable preserved response
  · obtain ⟨event, payload, outputEq, codeEq, serial, raw, value, node, ready, fresh,
      typed, rfl⟩ := freshUsable
    have actualReady := (original.application.publicView_eventReady event).mp ready
    have rightFresh := (frame.slots (.prepared serial)).mp fresh
    have ownFresh : (memory.shadow.inputView runtime leaks
        (repaired.observe app owner)).application.candidates (.prepared serial) = .fresh := by
      rw [frame.observed]
      exact fresh
    have changedEq := memory.repairResponse_usable runtime leaks owner
      (repaired.observe app owner) event payload outputEq codeEq node serial (some raw)
        ownFresh rightFresh value typed
    have same : changed.1 =
        (⟨some ⟨⟨.commitment event (owner, .prepared serial), some raw⟩, .none⟩⟩ : app.Action) :=
      congrArg Prod.fst changedEq
    have resources := frame.fresh_usable_submission_resources past event payload outputEq
      codeEq node serial raw value typed fresh actualReady
    refine ⟨same, resources.1, ?_, resources.2.1, ?_, ?_⟩
    · have shadow := congrArg Prod.snd changedEq
      change updated.shadow = _ at shadow
      rw [shadow]
      exact onlyBindings.rememberCandidate _ _
    · change OwnerCommitmentsSettledOrMatching owner left
        (repaired.respond app owner changed.1)
      rw [same]
      exact provenance.respond_fresh_binding event serial raw fresh rightFresh
    · change ∀ slot raw, left.application.candidates.lookup (owner, slot) = .openable raw →
        (repaired.respond app owner changed.1).application.candidates.lookup (owner, slot) =
          .openable raw
      rw [same]
      exact frame.same_response_openable preserved _

/-- A single effective owner law is used at the original reconstructed input
on every hidden history. Supported fresh usable calls add only candidate memory;
the exact joint law retains both evaluator marginals and the current resources. -/
theorem usable_effective_response_coupling
    (frame : Frame runtime leaks memory owner original repaired)
    (onlyBindings : memory.shadow.OwnBindings owner)
    (past : memory.shadow.CompletedAt original.application.config)
    (provenance : OwnerCommitmentsSettledOrMatching owner original repaired)
    (bounds : MessageBounds graph)
    (leftRecall : original.InputRecall (runtime.reactiveApplication leaks))
    (rightRecall : repaired.InputRecall (runtime.reactiveApplication leaks))
    (preserved : ∀ slot raw,
      original.application.candidates.lookup (owner, slot) = .openable raw →
        repaired.application.candidates.lookup (owner, slot) = .openable raw)
    (players : Player → (runtime.reactiveApplication leaks).Policy)
    (reference : List (runtime.reactiveApplication leaks).PlayerEntry)
    (started : reference.length ≤ (repaired.recall owner).length)
    (effective : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      response ∈ (bounds.menu runtime leaks).actions owner (original.recall owner)
        (original.observe (runtime.reactiveApplication leaks) owner))
    (usable : ∀ response ∈ (players owner (original.recall owner)
      (original.observe (runtime.reactiveApplication leaks) owner)).support,
      (∀ material, response.transmission = some material →
          ∀ event candidate, material.call.packet ≠ .commitment event candidate) ∨
        FreshUsableBindingResponse runtime leaks owner
          (original.observe (runtime.reactiveApplication leaks) owner).application response) :
    let app := runtime.reactiveApplication leaks
    let strategy := retainedImplementation runtime leaks (bounds.menu runtime leaks)
      owner reference (players owner)
    ∃ coupling : PMF (app.Execution × app.Execution × BindingMemory runtime leaks),
      coupling.map Prod.fst = app.invoke players owner original ∧
      coupling.map Prod.snd = strategy.resume owner players (some owner) repaired memory ∧
      ∀ next ∈ coupling.support,
        Frame runtime leaks next.2.2 owner next.1 next.2.1 ∧
          next.2.2.shadow.OwnBindings owner ∧
          next.2.2.shadow.CompletedAt next.1.application.config ∧
          OwnerCommitmentsSettledOrMatching owner next.1 next.2.1 ∧
          reference.length ≤ (next.2.1.recall owner).length ∧
          next.1.InputRecall app ∧ next.2.1.InputRecall app ∧
          ∀ slot raw, next.1.application.candidates.lookup (owner, slot) = .openable raw →
            next.2.1.application.candidates.lookup (owner, slot) = .openable raw := by
  classical
  let app := runtime.reactiveApplication leaks
  let law := players owner (original.recall owner) (original.observe app owner)
  let menu := bounds.menu runtime leaks
  let changed (response : app.Action) :=
    memory.repairResponse runtime leaks owner (repaired.observe app owner) response
  let updated (response : app.Action) : BindingMemory runtime leaks :=
    ⟨(changed response).2, memory.responses ++
      [(memory.shadow.inputView runtime leaks (repaired.observe app owner), response)]⟩
  have resources (response : app.Action) (supported : response ∈ law.support) :=
    frame.usable_response_resources onlyBindings past provenance bounds leftRecall rightRecall
      preserved response (effective response supported) (usable response supported)
  have transported (response : app.Action) (supported : response ∈ law.support) :=
    runtime.effectiveResponse_openable_transport leaks bounds owner original repaired
      leftRecall rightRecall frame.network frame.publicView frame.slots preserved response
        (effective response supported)
  have responseLaw :
      (implementation runtime leaks owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) =
          law.map (fun response => (response, updated response)) := by
    rw [implementation_respond runtime leaks owner reference (players owner) memory
      (repaired.recall owner) (repaired.observe app owner) started, frame.past, frame.observed]
    apply map_congr_on_support _
    intro response supported
    rw [← frame.observed]
    change ((changed response).1, updated response) = (response, updated response)
    rw [(resources response supported).1]
  have legalLaw :
      (retainedImplementation runtime leaks menu owner reference (players owner)).respond memory
        (repaired.recall owner, repaired.observe app owner) =
          law.map (fun response => (response, updated response)) := by
    rw [retainedImplementation_respond_eq runtime leaks menu owner reference (players owner)
      memory (repaired.recall owner, repaired.observe app owner) (by
        rw [responseLaw]
        intro result supported
        obtain ⟨response, chosen, rfl⟩ := PMF.support_map .. ▸ supported
        exact (transported response chosen).1), responseLaw]
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
    have held := (resources response member).2
    have same := (resources response member).1
    change (changed response).1 = response at same
    have frameAfter := held.1
    have ledgerAfter := held.2.2.2.1
    have openedAfter := held.2.2.2.2
    change Frame runtime leaks (updated response) owner
      (original.respond app owner response)
        (repaired.respond app owner (changed response).1) at frameAfter
    change OwnerCommitmentsSettledOrMatching owner (original.respond app owner response)
      (repaired.respond app owner (changed response).1) at ledgerAfter
    change ∀ slot raw,
      (original.respond app owner response).application.candidates.lookup (owner, slot) =
        .openable raw →
      (repaired.respond app owner (changed response).1).application.candidates.lookup
        (owner, slot) = .openable raw at openedAfter
    rw [same] at frameAfter ledgerAfter openedAfter
    refine ⟨frameAfter, held.2.1, held.2.2.1, ledgerAfter, ?_,
      app.respond_inputRecall original owner response leftRecall,
      app.respond_inputRecall repaired owner response rightRecall, openedAfter⟩
    rw [app.respond_recall_length]
    omega

end BindingMemory.Frame

end Vegas.EventGraphRuntime
