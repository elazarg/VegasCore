/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteCompiler
import Vegas.Pending.ReactiveSubmissionRecall
import Interaction.ReactiveMessageReadout

/-! # Finite retained responses for every event-code constructor

This is a response restriction of the existing reactive application. Its
binding domain is fixed before selecting an equilibrium and must cover every
source payload value. Ordinary opportunities permit waiting and the
first source decision for an event. The calendar service selects the required
set at the last unsent owned decision opportunity. Detecting an omitted
decision needs a public deadline obligation, not just an audit of emitted packets.

Fresh openings are permitted once per unique event, using existing own response
recall. Once submitted, a pending canonical opening remains available for inclusion.

At a resolution, failed owner-local validation and withholding send an explicit
withholding packet. Silence remains a separate deferred response.
This file supplies the local finite menu and coverage, not the whole
service or sequential-equilibrium correspondence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The existing prescribed decision with private response aliases normalized. -/
def serviceDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (runtime.reactiveApplication leaks).Action :=
  (runtime.reactiveNormalization leaks).action who past view
    (runtime.reactiveDecision leaks who event choice view.application)

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
/-- All semantic choices at the player's own turn, before intersecting with
the explicit finite target bounds. Samples remain environment commands. -/
def decisionActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  match view.application.publicView.ownTurn? who with
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

open Classical in
/-- Ordinary opportunities permit waiting. A
fresh source decision is available only before its event has been submitted. -/
def compiledActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  ((bounds.decisionActions runtime leaks who past view).filter
    (fun response => runtime.firstSubmission leaks past response) ∪
      {⟨none⟩}) ∩
        (bounds.menu runtime leaks).actions who past view

open Classical in
/-- The service uses this set only at the last unsent binding opportunity.
Coverage proves the fallback unreachable there; no source failure is added. -/
def requiredDecisionActions (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    Finset (runtime.reactiveApplication leaks).Action :=
  let choices := (bounds.decisionActions runtime leaks who past view).filter
    (fun response => runtime.firstSubmission leaks past response) ∩
      (bounds.menu runtime leaks).actions who past view
  if choices.Nonempty then choices else {⟨none⟩}

theorem silence_compiled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (⟨none⟩ : (runtime.reactiveApplication leaks).Action) ∈
      bounds.compiledActions runtime leaks who past view := by
  classical
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_union_right _ (Finset.mem_singleton_self _), ?_⟩
  rw [bounds.menu_mem]
  exact ⟨trivial, rfl⟩

/-- Silent responses are retained at every ordinary opportunity. -/
theorem silent_compiled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (supported : response ∈ ((runtime.reactiveApplication leaks).silentPolicy past view).support) :
    response ∈ bounds.compiledActions runtime leaks who past view := by
  cases (runtime.reactiveApplication leaks).silentPolicy_cases past view response supported
  exact bounds.silence_compiled runtime leaks who past view

theorem compiledActions_nonempty (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.compiledActions runtime leaks who past view).Nonempty :=
  ⟨⟨none⟩, bounds.silence_compiled runtime leaks who past view⟩

theorem requiredDecisionActions_nonempty (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.requiredDecisionActions runtime leaks who past view).Nonempty := by
  classical
  unfold requiredDecisionActions
  dsimp only
  split
  · assumption
  · exact Finset.singleton_nonempty _

def compiledMenu : (runtime.reactiveApplication leaks).ResponseMenu where
  actions := bounds.compiledActions runtime leaks
  nonempty := bounds.compiledActions_nonempty runtime leaks

theorem compiledActions_effective (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.compiledActions runtime leaks who past view ⊆
      (bounds.menu runtime leaks).actions who past view := by
  classical
  exact Finset.inter_subset_right

theorem requiredDecisionActions_subset_compiled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    bounds.requiredDecisionActions runtime leaks who past view ⊆
      bounds.compiledActions runtime leaks who past view := by
  classical
  intro response member
  unfold requiredDecisionActions at member
  dsimp only at member
  split at member
  · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_inter.mp member).1,
      (Finset.mem_inter.mp member).2⟩
  · cases Finset.mem_singleton.mp member
    exact bounds.silence_compiled runtime leaks who past view

/-- Waiting preserves the fresh-submission discipline. -/
theorem compiledActions_firstSubmission (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    runtime.firstSubmission leaks past response = true := by
  classical
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | replayed
  · exact (Finset.mem_filter.mp decision).2
  · cases Finset.mem_singleton.mp replayed
    rfl

theorem decision_compiled (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (decision : response ∈ bounds.decisionActions runtime leaks who past view)
    (first : runtime.firstSubmission leaks past response = true)
    (available : response ∈ (bounds.menu runtime leaks).actions who past view) :
    response ∈ bounds.compiledActions runtime leaks who past view := by
  classical
  exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _
    (Finset.mem_filter.mpr ⟨decision, first⟩), available⟩

theorem decision_required (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (response : (runtime.reactiveApplication leaks).Action)
    (decision : response ∈ bounds.decisionActions runtime leaks who past view)
    (first : runtime.firstSubmission leaks past response = true)
    (available : response ∈ (bounds.menu runtime leaks).actions who past view) :
    response ∈ bounds.requiredDecisionActions runtime leaks who past view := by
  classical
  have member : response ∈ (bounds.decisionActions runtime leaks who past view).filter
      (fun response => runtime.firstSubmission leaks past response) ∩
        (bounds.menu runtime leaks).actions who past view :=
    Finset.mem_inter.mpr ⟨Finset.mem_filter.mpr ⟨decision, first⟩, available⟩
  unfold requiredDecisionActions
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
readiness and fresh-slot capacity are operational checkpoint conditions. -/
theorem binding_value_required (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (value : L.Val payload) (included : (⟨payload, value⟩ : Raw L) ∈ bounds.values) :
    runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) (PublicationResult.success value)) ∈
        bounds.requiredDecisionActions runtime leaks who past view := by
  classical
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  apply bounds.decision_required runtime leaks who past view
  · simp only [decisionActions, turnSome, owned, ready, and_self, ↓reduceIte, node]
    exact Finset.mem_image.mpr ⟨value, (bounds.typedValues_mem payload value).mpr
      ⟨⟨payload, value⟩, included, Raw.as?_mk payload value⟩, rfl⟩
  · rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
      node serial fresh, runtime.firstSubmission_normalization]
    simp only [firstSubmission, submittedEvent?, reactiveBinding, Payload.event?, unsent,
      Bool.not_false]
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
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (opening : Option (Raw L)) (bounded : bounds.AllowsOpening opening) :
    (⟨some ⟨⟨.commitment event (who, .prepared serial), opening⟩, .none⟩⟩ :
      (runtime.reactiveApplication leaks).Action) ∈
        bounds.requiredDecisionActions runtime leaks who past view ∨
      opening.bind (fun raw => raw.as? payload) = none := by
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  cases opening with
  | none => exact Or.inr rfl
  | some raw =>
      cases decoded : raw.as? payload with
      | none => exact Or.inr decoded
      | some value =>
          have same := raw_eq_of_decoded raw payload value decoded
          subst raw
          have represented := bounds.binding_value_required runtime leaks who past view event
            payload outputEq codeEq node turn owned ready unsent serial fresh capacity
            value bounded
          rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
            node serial fresh, runtime.reactiveBinding_normal_of_fresh leaks who past view event
              payload _ serial (reactiveFreshSlot_spec view.application serial fresh)]
            at represented
          exact Or.inl represented

/-- At an actual covered binding checkpoint the totalization fallback is
unreachable. Every retained action is a typed canonical binding; public replay
and silence cannot replace this required source decision. -/
theorem required_binding_cases (covered : bounds.CoversBindingValues)
    (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (unsent : runtime.eventRecorded leaks past event = false)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (capacity : serial < bounds.candidateCount)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.requiredDecisionActions runtime leaks who past view) :
    ∃ value ∈ bounds.typedValues payload,
      response = (runtime.reactiveNormalization leaks).action who past view
        (runtime.reactiveBinding leaks who event payload (.success value) serial) := by
  classical
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  have typed := covered event
  rw [outputEq] at typed
  have usable : ((bounds.decisionActions runtime leaks who past view).filter
      (fun response => runtime.firstSubmission leaks past response) ∩
        (bounds.menu runtime leaks).actions who past view).Nonempty := by
    refine ⟨runtime.serviceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm)
        (PublicationResult.success (L.someValue payload))), Finset.mem_inter.mpr ⟨?_, ?_⟩⟩
    · apply Finset.mem_filter.mpr
      constructor
      · simp only [decisionActions, turnSome, owned, ready, and_self, ↓reduceIte, node]
        exact Finset.mem_image.mpr ⟨L.someValue payload,
          (bounds.typedValues_mem payload _).mpr
            ⟨⟨payload, L.someValue payload⟩, typed _, Raw.as?_mk payload _⟩, rfl⟩
      · rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
          node serial fresh, runtime.firstSubmission_normalization]
        simp only [firstSubmission, submittedEvent?, reactiveBinding, Payload.event?, unsent,
          Bool.not_false]
    · rw [runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
        node serial fresh]
      exact bounds.binding_normalized_available runtime leaks who past view event payload _ serial
        capacity (fun chosen _ => typed chosen)
  rw [requiredDecisionActions, ite_eq_left usable] at member
  have choices := (Finset.mem_inter.mp member).1
  have choices := (Finset.mem_filter.mp choices).1
  simp only [decisionActions, turnSome, owned, ready, and_self, ↓reduceIte, node,
    Finset.mem_image] at choices
  obtain ⟨value, admitted, same⟩ := choices
  refine ⟨value, admitted, same.symm.trans ?_⟩
  exact runtime.serviceDecision_binding leaks who past view event payload outputEq codeEq
    node serial fresh (.success value)

/-- Before the final opportunity, a binding phase allows either transport or
one typed binding. The first-submission test remains part of the conclusion. -/
theorem ordinary_binding_cases
    (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (serial : Nat) (fresh : reactiveFreshSlot view.application = some serial)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    response ∈ ((runtime.reactiveApplication leaks).silentPolicy past view).support ∨
      ∃ value ∈ bounds.typedValues payload,
        runtime.eventRecorded leaks past event = false ∧
        response = (runtime.reactiveNormalization leaks).action who past view
          (runtime.reactiveBinding leaks who event payload (.success value) serial) := by
  classical
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | transport
  · obtain ⟨chosen, first⟩ := Finset.mem_filter.mp decision
    simp only [decisionActions, turnSome, owned, ready, and_self, ↓reduceIte, node,
      Finset.mem_image] at chosen
    obtain ⟨value, admitted, same⟩ := chosen
    have action := runtime.serviceDecision_binding leaks who past view event payload outputEq
      codeEq node serial fresh (.success value)
    have shape := same.symm.trans action
    rw [shape, runtime.firstSubmission_normalization] at first
    simp only [firstSubmission, submittedEvent?, reactiveBinding, Payload.event?,
      Bool.not_eq_true_eq_eq_false] at first
    exact Or.inr ⟨value, admitted, first, shape⟩
  · exact Or.inl (by
      apply (runtime.reactiveApplication leaks).mem_silentPolicy_support.mpr
      exact Finset.mem_singleton.mp transport)

/-- A pending first binding does not permit another fresh binding during the
same phase, even though reserved inclusion has not settled the event yet. -/
theorem ordinary_binding_recorded
    (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (turn : view.application.publicView.OwnTurn who event)
    (owned : graph.actor? event = some who)
    (ready : view.application.publicView.EventReady event)
    (recorded : runtime.eventRecorded leaks past event = true)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    response ∈ ((runtime.reactiveApplication leaks).silentPolicy past view).support := by
  classical
  have turnSome := view.application.publicView.ownTurn?_of_ownTurn who event turn
  cases slot : reactiveFreshSlot view.application with
  | some serial =>
      rcases bounds.ordinary_binding_cases runtime leaks who past view event payload outputEq codeEq
        node turn owned ready serial slot response member with transport | ⟨_, _, unsent, _⟩
      · exact transport
      · simp only [recorded, Bool.true_eq_false] at unsent
  | none =>
      rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | transport
      · have chosen := (Finset.mem_filter.mp decision).1
        simp only [decisionActions, turnSome, owned, ready, and_self, ↓reduceIte, node,
          Finset.mem_image] at chosen
        obtain ⟨value, _, same⟩ := chosen
        have silent : runtime.serviceDecision leaks who past view event
            (cast (congrArg EventField.Action outputEq.symm)
              (PublicationResult.success value)) = ⟨none⟩ := by
          simp only [serviceDecision, reactiveDecision, node, slot, Option.map_none]
          rfl
        rw [← same, silent]
        exact (runtime.reactiveApplication leaks).silentPolicy_support past view
      · exact (runtime.reactiveApplication leaks).mem_silentPolicy_support.mpr
          (Finset.mem_singleton.mp transport)

/-- A player without a ready event of its own responds silently. -/
theorem compiled_foreign_transport
    (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (idle : view.application.publicView.ownTurn? who = none)
    (response : (runtime.reactiveApplication leaks).Action)
    (member : response ∈ bounds.compiledActions runtime leaks who past view) :
    response ∈ ((runtime.reactiveApplication leaks).silentPolicy past view).support := by
  classical
  rcases Finset.mem_union.mp (Finset.mem_inter.mp member).1 with decision | transport
  · have chosen := (Finset.mem_filter.mp decision).1
    simp only [decisionActions, idle, Finset.mem_singleton] at chosen
    cases chosen
    exact (runtime.reactiveApplication leaks).silentPolicy_support past view
  · exact (runtime.reactiveApplication leaks).mem_silentPolicy_support.mpr
          (Finset.mem_singleton.mp transport)

end MessageBounds

end Vegas.EventGraphRuntime
