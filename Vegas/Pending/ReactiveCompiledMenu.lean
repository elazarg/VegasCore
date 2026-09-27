/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteCompiler

/-! # Finite retained responses for every event-code constructor

This is a response restriction of the existing reactive application. Its
binding domain is fixed before selecting an equilibrium and must cover every
source payload value. A ready binding opportunity requires a binding response;
silence and public replay are not silently identified with a value-only source
commitment. Detecting an omitted required binding needs a separate public
deadline obligation, not just an audit of emitted packets.

At a resolution, failed owner-local validation and withholding use silence.
Their eventual publication failure requires the existing protected expiry
service. This file supplies the local finite menu and coverage, not that whole
service or sequential-equilibrium correspondence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The existing prescribed decision, with withheld publications settled by
the service's expiry and private response aliases normalized. -/
def serviceDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (runtime.reactiveApplication leaks).Action :=
  let response := runtime.reactiveDecision leaks who event choice view.application
  match response.transmission with
  | some (.submit ⟨⟨.withhold _, _⟩, _⟩) => ⟨none⟩
  | _ => (runtime.reactiveNormalization leaks).action who past view response

theorem serviceDecision_binding (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (result : PublicationResult (L.Val payload)) :
    runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) result) =
      (runtime.reactiveNormalization leaks).action who past view
        (runtime.reactiveBinding leaks who event payload result serial) := by
  simp only [serviceDecision, reactiveDecision, node, fresh, Option.map_some,
    cast_cast, cast_eq]
  rfl

theorem reactiveBinding_normal_of_fresh (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (fresh : view.application.candidates (.prepared serial) = .fresh) :
    (runtime.reactiveNormalization leaks).action who past view
      (runtime.reactiveBinding leaks who event payload result serial) =
      runtime.reactiveBinding leaks who event payload result serial := by
  simp only [ReactiveApplication.SubmissionNormalization.action, reactiveBinding,
    reactiveNormalization, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive, openingEffective, fresh, and_self, ↓reduceIte,
    EvidenceRequest.normalize_none]

namespace MessageBounds

variable (bounds : MessageBounds graph)

def typedValues (payload : L.Ty) : Finset (L.Val payload) :=
  ((bounds.values.toList.filterMap fun raw => raw.as? payload)).toFinset

omit [DecidableEq Player] in
theorem typedValues_mem (payload : L.Ty) (value : L.Val payload) :
    value ∈ bounds.typedValues payload ↔
      ∃ raw ∈ bounds.values, raw.as? payload = some value := by
  classical
  simp only [typedValues, List.mem_toFinset, List.mem_filterMap, Finset.mem_toList]

def CoversBindingValues : Prop := ∀ event,
  match graph.outputLayout event with
  | .binding _ payload => ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values
  | .publicData _ | .privateInput _ _ | .publication _ => True

omit [DecidableEq Player] in
/-- This condition is genuinely finite source admission. It cannot hold for
an unbounded integer commitment type merely because the wire is bounded. -/
theorem finite_binding_values (covered : bounds.CoversBindingValues)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : graph.outputLayout event = .binding owner payload) : Finite (L.Val payload) := by
  have all := covered event
  rw [binding] at all
  apply Finite.of_surjective (fun value : { value // value ∈ bounds.typedValues payload } =>
    value.val)
  intro value
  exact ⟨⟨value, (bounds.typedValues_mem payload value).mpr
    ⟨⟨payload, value⟩, all value, Raw.as?_mk payload value⟩⟩, rfl⟩

variable [Fintype Player] (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

open Classical in
/-- All semantic choices at the granted node, before intersecting with the
explicit finite target bounds. Samples remain environment commands. -/
def decisionActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  match view.application.publicView.serviceGrant with
  | none => {⟨none⟩}
  | some event =>
      if graph.actor? event = some who ∧ view.application.publicView.EventReady event then
        match nodeView graph event with
        | .sample .. => {⟨none⟩}
        | .bind _ payload outputEq _ =>
            (bounds.typedValues payload).image fun value =>
              runtime.serviceDecision leaks who past view event
                (cast (congrArg EventField.Action outputEq.symm) (PublicationResult.success value))
        | .resolve _ _ _ _ outputEq _ =>
            Finset.univ.image fun disclose : Bool =>
              runtime.serviceDecision leaks who past view event
                (cast (congrArg EventField.Action outputEq.symm) disclose)
      else {⟨none⟩}

def bindingOpportunity (who : Player)
    (view : (runtime.reactiveApplication leaks).PlayerView) : Prop :=
  ∃ event, view.application.publicView.serviceGrant = some event ∧
    graph.actor? event = some who ∧ view.application.publicView.EventReady event ∧
    ∃ owner payload outputEq codeEq,
      nodeView graph event = .bind owner payload outputEq codeEq

open Classical in
def compiledCandidates (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  let decisions := bounds.decisionActions runtime leaks who past view
  let aliases := if bindingOpportunity runtime leaks who view then ∅ else
    (view.messages.ledger.map (fun message =>
      (⟨some (.replay message.id)⟩ : (runtime.reactiveApplication leaks).Action))).toFinset
  (decisions ∪ aliases) ∩ (bounds.menu runtime leaks).actions who past view

open Classical in
/-- The silent fallback totalizes inputs where no represented response fits the
declared bounds. Coverage must prove that this branch is absent at real bindings. -/
def compiledActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  let permitted := bounds.compiledCandidates runtime leaks who past view
  if permitted.Nonempty then permitted else {⟨none⟩}

theorem compiledActions_nonempty (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.compiledActions runtime leaks who past view).Nonempty := by
  classical
  unfold compiledActions
  dsimp only
  split
  · assumption
  · exact Finset.singleton_nonempty _

def compiledMenu :
    (runtime.reactiveApplication leaks).ResponseMenu where
  actions := bounds.compiledActions runtime leaks
  nonempty := bounds.compiledActions_nonempty runtime leaks

theorem compiledActions_effective (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.compiledActions runtime leaks who past view ⊆
      (bounds.menu runtime leaks).actions who past view := by
  classical
  unfold compiledActions
  dsimp only
  split
  · exact Finset.inter_subset_right
  · intro action member
    cases Finset.mem_singleton.mp member
    rw [bounds.menu_mem]
    exact ⟨trivial, rfl⟩

theorem decision_compiled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (decision : response ∈ bounds.decisionActions runtime leaks who past view)
    (available : response ∈ (bounds.menu runtime leaks).actions who past view) :
    response ∈ bounds.compiledActions runtime leaks who past view := by
  classical
  have member : response ∈ bounds.compiledCandidates runtime leaks who past view :=
    Finset.mem_inter.mpr ⟨Finset.mem_union_left _ decision, available⟩
  unfold compiledActions
  rw [ite_eq_left ⟨response, member⟩]
  exact member

theorem binding_normalized_available (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (capacity : serial < bounds.candidateCount)
    (value : ∀ chosen, result = .success chosen → (⟨payload, chosen⟩ : Raw L) ∈ bounds.values) :
    (runtime.reactiveNormalization leaks).action who past view
      (runtime.reactiveBinding leaks who event payload result serial) ∈
        (bounds.menu runtime leaks).actions who past view := by
  rw [menu, ReactiveApplication.SubmissionNormalization.menu_mem]
  refine ⟨_, ?_, rfl⟩
  rw [rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change _ ∈ bounds.submissions (ReactiveApplication.ResponseMenu.knownPackets past view)
  rw [submissions_mem]
  refine ⟨⟨capacity, ?_⟩, trivial⟩
  cases result with
  | failure => trivial
  | success chosen => exact value chosen rfl

/-- Every source value is present, independently of the equilibrium. The
grant/readiness and fresh-slot capacity are operational checkpoint conditions. -/
theorem binding_value_compiled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (value : L.Val payload) (included : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) (PublicationResult.success value)) ∈
        bounds.compiledActions runtime leaks who past view := by
  classical
  apply bounds.decision_compiled runtime leaks who past view
  · simp only [decisionActions, granted, owned, ready, and_self, ↓reduceIte, node]
    exact Finset.mem_image.mpr ⟨value, (bounds.typedValues_mem payload value).mpr
      ⟨⟨payload, value⟩, included, Raw.as?_mk payload value⟩, rfl⟩
  · rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
      node serial fresh]
    apply bounds.binding_normalized_available runtime leaks who past view event payload _
      serial capacity
    intro chosen same
    cases PublicationResult.success.inj same
    exact included

omit [IExpr.ResultTypes L] in
private theorem raw_eq_of_decoded (raw : Raw L) (payload : L.Ty)
    (value : L.Val payload) (decoded : raw.as? payload = some value) :
    raw = ⟨payload, value⟩ := by
  rcases raw with ⟨ty, supplied⟩
  unfold Raw.as? at decoded
  split at decoded
  · rename_i same
    change ty = payload at same
    subst ty
    simp only [cast_eq, Option.some.injEq] at decoded
    exact congrArg (Raw.mk payload) decoded
  · cases decoded

/-- Under the same public canonical commitment packet, every bounded private
opening is either a represented source value or unusable private material.
The latter case is repaired, not falsely claimed detectable by a public audit. -/
theorem canonical_binding_response_cases (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (opening : Option (Raw L)) (bounded : bounds.AllowsOpening opening) :
    (⟨some (.submit ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩)⟩ :
      (runtime.reactiveApplication leaks).Action) ∈
        bounds.compiledActions runtime leaks who past view ∨
      opening.bind (fun raw => raw.as? payload) = none := by
  cases opening with
  | none => exact Or.inr rfl
  | some raw =>
      cases decoded : raw.as? payload with
      | none => exact Or.inr decoded
      | some value =>
          have same := raw_eq_of_decoded raw payload value decoded
          subst raw
          have represented := bounds.binding_value_compiled runtime leaks who past view event
            payload outputEq codeEq node granted owned ready serial fresh capacity value bounded
          rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
            node serial fresh, runtime.reactiveBinding_normal_of_fresh leaks who past view event
              payload _ serial (reactiveFreshSlot_spec view.application serial fresh)]
            at represented
          exact Or.inl represented

/-- At an actual covered binding checkpoint the totalization fallback is
unreachable. Every retained action is a typed canonical binding; public replay
and silence cannot replace this required source decision. -/
theorem compiled_binding_cases (covered : bounds.CoversBindingValues)
    (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (granted : view.application.publicView.serviceGrant = some event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    ∃ value ∈ bounds.typedValues payload,
      response = (runtime.reactiveNormalization leaks).action who past view
        (runtime.reactiveBinding leaks who event payload (.success value) serial) := by
  classical
  have typed := covered event
  rw [outputEq] at typed
  have usable : (bounds.compiledCandidates runtime leaks who past view).Nonempty := by
    refine ⟨runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm)
        (PublicationResult.success (L.someValue payload))), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_union_left
      simp only [decisionActions, granted, owned, ready, and_self, ↓reduceIte, node]
      exact Finset.mem_image.mpr ⟨L.someValue payload,
        (bounds.typedValues_mem payload _).mpr
          ⟨⟨payload, L.someValue payload⟩, typed _, Raw.as?_mk payload _⟩, rfl⟩
    · rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
        node serial fresh]
      exact bounds.binding_normalized_available runtime leaks who past view event payload _ serial
        capacity (fun chosen _ => typed chosen)
  have opportunity : bindingOpportunity runtime leaks who view :=
    ⟨event, granted, owned, ready, who, payload, outputEq, codeEq, node⟩
  rw [compiledActions, ite_eq_left usable] at member
  have choices := (Finset.mem_inter.mp member).1
  simp only [opportunity, ↓reduceIte, Finset.union_empty] at choices
  simp only [decisionActions, granted, owned, ready, and_self, ↓reduceIte, node,
    Finset.mem_image] at choices
  obtain ⟨value, admitted, same⟩ := choices
  refine ⟨value, admitted, same.symm.trans ?_⟩
  exact runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
    node serial fresh (.success value)

end MessageBounds

end Vegas.EventGraphRuntime
