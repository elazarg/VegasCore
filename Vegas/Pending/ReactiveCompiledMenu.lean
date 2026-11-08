/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ReactiveFiniteCompiler
import Vegas.Pending.ReactiveSubmissionRecall
import Vegas.Pending.EventPublicState

/-! # Finite retained responses for every event-code constructor

This is a response restriction of the existing reactive application. Its
binding domain is fixed before selecting an equilibrium and must cover every
source payload value. Ordinary opportunities permit waiting and the
first source decision for an event. Binding omission is a silent source choice
at every opportunity, including the final visit before deadline expiry.

Fresh openings are permitted once per unique event, using existing own response
recall. Once submitted, a pending canonical opening remains available for inclusion.

At a resolution, an unavailable authentic opening and withholding use silence.
Guard rejection is evaluated by the handler after authentic transmission.
This file supplies the local finite menu and coverage, not that whole
service or sequential-equilibrium correspondence.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}


namespace MessageBounds

variable (bounds : MessageBounds graph)

def typedValues (payload : L.Ty) : Finset (L.Val payload) :=
  ((bounds.values.toList.filterMap fun raw => raw.as? payload)).toFinset

open Classical in
/-- Binding decisions include omission, opaque admission, and covered typed values. -/
def bindingChoices (payload : L.Ty) : Finset (Option (PublicationResult (L.Val payload))) :=
  {none, some .failure} ∪ (bounds.typedValues payload).image (fun value => some (.success value))

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

variable [Fintype Player] (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

open Classical in
/-- All semantic choices at the player's own turn, before intersecting with
the explicit finite target bounds. Samples remain environment commands. -/
def decisionActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  match view.application.publicView.ownTurn? who with
  | none => {⟨none⟩}
  | some event =>
      if graph.actor? event = some who ∧ view.application.publicView.EventReady event then
        match nodeView graph event with
        | .sample .. => {⟨none⟩}
        | .bind _ payload outputEq _ =>
            (bounds.bindingChoices payload).image fun choice =>
              (serviceDecision timeouts) leaks who past view event
                (cast (congrArg EventField.Action outputEq.symm) choice)
        | .resolve _ _ _ _ outputEq _ =>
            Finset.univ.image fun disclose : Bool =>
              (serviceDecision timeouts) leaks who past view event
                (cast (congrArg EventField.Action outputEq.symm) disclose)
      else {⟨none⟩}

omit [Fintype Player] in
/-- Omission or withholding gives silence at every strategic opportunity. -/
theorem silence_decisionActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (⟨none⟩ : ((reactiveApplication timeouts) leaks).Action) ∈
      bounds.decisionActions timeouts leaks who past view := by
  classical
  unfold decisionActions
  split
  · exact Finset.mem_singleton_self _
  · split
    · cases kind : nodeView graph _ with
      | sample => exact Finset.mem_singleton_self _
      | bind owner payload outputEq codeEq =>
          refine Finset.mem_image.mpr ⟨none, ?_, ?_⟩
          · simp [bindingChoices]
          · simp [serviceDecision, reactiveDecision, kind,
              ReactiveApplication.SubmissionNormalization.action]
      | resolve owner payload binding checks outputEq codeEq =>
          refine Finset.mem_image.mpr ⟨false, Finset.mem_univ _, ?_⟩
          simp [serviceDecision, reactiveDecision, kind, reactiveResolutionPacket,
            ReactiveApplication.SubmissionNormalization.action]
    · exact Finset.mem_singleton_self _

open Classical in
/-- Ordinary opportunities permit waiting. A
fresh source decision is available only before its event has been submitted. -/
def compiledActions (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    Finset ((reactiveApplication timeouts) leaks).Action :=
  (bounds.decisionActions timeouts leaks who past view).filter
    (fun response => (firstSubmission timeouts) leaks past response) ∩
      (bounds.menu timeouts leaks).actions who past view

theorem silence_compiled (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (⟨none⟩ : ((reactiveApplication timeouts) leaks).Action) ∈
      bounds.compiledActions timeouts leaks who past view := by
  classical
  apply Finset.mem_inter.mpr
  refine ⟨Finset.mem_filter.mpr
    ⟨bounds.silence_decisionActions timeouts leaks who past view, rfl⟩, ?_⟩
  rw [bounds.menu_mem]
  exact ⟨trivial, rfl⟩

theorem compiledActions_nonempty (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView) :
    (bounds.compiledActions timeouts leaks who past view).Nonempty :=
  ⟨⟨none⟩, bounds.silence_compiled timeouts leaks who past view⟩

theorem binding_normalized_available (who : Player)
    (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (serial : Nat) (capacity : serial < bounds.candidateCount)
    (value : ∀ chosen, result = .success chosen → (⟨payload, chosen⟩ : Raw L) ∈ bounds.values) :
    ((reactiveNormalization timeouts) leaks).action who past view
      ((reactiveBinding timeouts) leaks who event payload result serial) ∈
        (bounds.menu timeouts leaks).actions who past view := by
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
