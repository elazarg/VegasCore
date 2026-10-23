/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveFiniteCompiler
import Vegas.Pending.ReactiveSubmissionRecall
import Vegas.Pending.EventPublicState

/-! # Finite retained responses for every event-code constructor

This is a response restriction of the existing reactive application. Its
binding domain is fixed before selecting an equilibrium and must cover every
source payload value. Ordinary opportunities permit waiting and the
first source decision for an event. The service selects the required set only
at the last unsent binding opportunity. Detecting an omitted required binding
needs a public deadline obligation, not just an audit of emitted packets.

Fresh openings are permitted once per unique event, using existing own response
recall. Once submitted, a pending canonical opening remains available for inclusion.

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

/-- The existing prescribed decision with private response aliases
normalized. A withheld publication sends nothing and is settled by expiry. -/
def serviceDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (runtime.reactiveApplication leaks).Action :=
  (runtime.reactiveNormalization leaks).action who past view
    (runtime.reactiveDecision leaks who event choice view.application)

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
def requiredBindingActions (who : Player)
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

theorem compiledActions_nonempty (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.compiledActions runtime leaks who past view).Nonempty :=
  ⟨⟨none⟩, bounds.silence_compiled runtime leaks who past view⟩

theorem requiredBindingActions_nonempty (who : Player)
    (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView) :
    (bounds.requiredBindingActions runtime leaks who past view).Nonempty := by
  classical
  unfold requiredBindingActions
  dsimp only
  split
  · assumption
  · exact Finset.singleton_nonempty _

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

end MessageBounds

end Vegas.EventGraphRuntime
