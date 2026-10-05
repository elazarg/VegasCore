/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveCompiledMenu
import Vegas.Pending.ReactiveBindingAllocation

/-! # Prescribed decisions at the audit's canonical slot

The public conformance rule (`freshServiceEnvelope`) expects a commitment of
`who` at the prepared slot numbered by `who`'s completed bindings
(`Vegas.EventGraphRuntime.PublicView.bindingCount`). The least fresh slot
(`reactiveFreshSlot`) differs from it once a binding of `who` has expired
without a submission. The canonical decision submits at the counted slot when
it is fresh, and otherwise falls back to the least fresh slot, so a deviating
owner still prepares a fresh candidate.
Samples and resolutions are decided as by `reactiveDecision`.

The inclusion window `PublicView.InclusionFitsDeadline` is the public condition
under which a fresh call, included within `bound event` slots, is included
strictly before the event's deadline.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

open Classical in
/-- The audit's canonical prepared slot of `who` when it is fresh, and the
least fresh prepared slot otherwise. -/
def canonicalFreshSlot (who : Player) (view : ReactivePlayerView graph) : Option Nat :=
  if view.candidates (.prepared (view.publicView.bindingCount who)) = .fresh then
    some (view.publicView.bindingCount who) else reactiveFreshSlot view

theorem canonicalFreshSlot_spec (who : Player) (view : ReactivePlayerView graph) (serial : Nat)
    (selected : canonicalFreshSlot who view = some serial) :
    view.candidates (.prepared serial) = .fresh := by
  classical
  unfold canonicalFreshSlot at selected
  split at selected
  · rename_i fresh
    cases Option.some.inj selected
    exact fresh
  · exact reactiveFreshSlot_spec view serial selected

theorem canonicalFreshSlot_canonical (who : Player) (view : ReactivePlayerView graph)
    (fresh : view.candidates (.prepared (view.publicView.bindingCount who)) = .fresh) :
    canonicalFreshSlot who view = some (view.publicView.bindingCount who) := by
  classical
  unfold canonicalFreshSlot
  simp only [fresh, ↓reduceIte]

/-- Some slot is chosen whenever a fresh slot exists. -/
theorem canonicalFreshSlot_isSome (who : Player) (view : ReactivePlayerView graph)
    (serial : Nat) (selected : reactiveFreshSlot view = some serial) :
    ∃ chosen, canonicalFreshSlot who view = some chosen := by
  classical
  unfold canonicalFreshSlot
  split
  · exact ⟨_, rfl⟩
  · exact ⟨serial, selected⟩

/-- `reactiveDecision` with a binding submitted at `canonicalFreshSlot`. -/
def canonicalReactiveDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (action : graph.Action event) (view : ReactivePlayerView graph) :
    (runtime.reactiveApplication leaks).Action where
  transmission := match nodeView graph event with
    | .sample .. => none
    | .bind _owner payload outputEq _codeEq =>
        (canonicalFreshSlot who view).map fun serial =>
          ⟨⟨.commitment event (who, .prepared serial),
            match (cast (congrArg EventField.Action outputEq) action :
                PublicationResult (L.Val payload)) with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩, .none⟩
    | .resolve _owner payload binding checks outputEq _codeEq =>
        some ((disclosureSubmission (reactiveResolutionPacket who event payload
          binding checks outputEq action view)).normalizeReactive who view [])

/-- `serviceDecision` over `canonicalReactiveDecision`, with private response
aliases normalized. -/
def canonicalServiceDecision (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    (runtime.reactiveApplication leaks).Action :=
  (runtime.reactiveNormalization leaks).action who past view
    (runtime.canonicalReactiveDecision leaks who event choice view.application)

/-- Away from bindings the canonical decision is the existing decision. -/
theorem canonicalReactiveDecision_eq_of_not_bind (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (action : graph.Action event)
    (view : ReactivePlayerView graph)
    (notBind : ∀ owner payload outputEq codeEq,
      nodeView graph event ≠ .bind owner payload outputEq codeEq) :
    runtime.canonicalReactiveDecision leaks who event action view =
      runtime.reactiveDecision leaks who event action view := by
  unfold canonicalReactiveDecision reactiveDecision
  congr 1
  cases node : nodeView graph event with
  | sample => rfl
  | bind owner payload outputEq codeEq => exact (notBind owner payload outputEq codeEq node).elim
  | resolve => rfl

theorem canonicalServiceDecision_eq_of_not_bind (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (notBind : ∀ owner payload outputEq codeEq,
      nodeView graph event ≠ .bind owner payload outputEq codeEq) :
    runtime.canonicalServiceDecision leaks who past view event choice =
      runtime.serviceDecision leaks who past view event choice := by
  unfold canonicalServiceDecision serviceDecision
  rw [runtime.canonicalReactiveDecision_eq_of_not_bind leaks who event choice view.application
    notBind]

/-- A binding decision submits the canonical binding at the selected slot. -/
theorem canonicalServiceDecision_binding (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (serial : Nat) (selected : canonicalFreshSlot who view.application = some serial)
    (result : PublicationResult (L.Val payload)) :
    runtime.canonicalServiceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) result) =
      runtime.reactiveBinding leaks who event payload result serial := by
  have fresh := canonicalFreshSlot_spec who view.application serial selected
  have normalized : runtime.canonicalServiceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) result) =
      (runtime.reactiveNormalization leaks).action who past view
        (runtime.reactiveBinding leaks who event payload result serial) := by
    simp only [canonicalServiceDecision, canonicalReactiveDecision, node, selected,
      Option.map_some, cast_cast, cast_eq]
    rfl
  rw [normalized]
  exact runtime.reactiveBinding_normal_of_fresh leaks who past view event payload result serial
    fresh

/-- The source decision to withhold emits an evidence-free decision packet. -/
theorem canonicalServiceDecision_resolution_false (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List (runtime.reactiveApplication leaks).PlayerEntry)
    (view : (runtime.reactiveApplication leaks).PlayerView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq) :
    runtime.canonicalServiceDecision leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) false) =
      ⟨some ⟨⟨.withhold event, none⟩, .none⟩⟩ := by
  simp only [canonicalServiceDecision, canonicalReactiveDecision, node,
    reactiveResolutionPacket, cast_cast, cast_eq, Bool.false_eq_true, ↓reduceIte,
    disclosureSubmission_normalize_withhold]
  simp only [ReactiveApplication.SubmissionNormalization.action, reactiveNormalization,
    disclosureSubmission, WitnessedSubmission.normalizeReactive,
    Submission.normalizeReactive_none, EvidenceRequest.normalize_none]

/-- The public deadline still admits inclusion of a packet for `event`. -/
def PublicView.WithinDeadline (runtime : EventGraphRuntime graph) (view : PublicView graph)
    (event : graph.EventId) : Prop :=
  match view.activatedAt event with
  | none => False
  | some entered => view.clock - entered < runtime.deadline event

/-- A fresh call emitted now and included within `bound event` slots is
included strictly before `event`'s deadline. -/
def PublicView.InclusionFitsDeadline (runtime : EventGraphRuntime graph)
    (bound : graph.EventId → Nat) (view : PublicView graph) (event : graph.EventId) : Prop :=
  match view.activatedAt event with
  | none => False
  | some entered => view.clock - entered + bound event < runtime.deadline event

instance (runtime : EventGraphRuntime graph) (bound : graph.EventId → Nat)
    (view : PublicView graph) (event : graph.EventId) :
    Decidable (view.InclusionFitsDeadline runtime bound event) := by
  unfold PublicView.InclusionFitsDeadline
  split <;> infer_instance

omit [DecidableEq Player] in
theorem PublicView.InclusionFitsDeadline.exists {runtime : EventGraphRuntime graph}
    {bound : graph.EventId → Nat} {view : PublicView graph} {event : graph.EventId}
    (fits : view.InclusionFitsDeadline runtime bound event) :
    ∃ entered, view.activatedAt event = some entered ∧
      view.clock - entered + bound event < runtime.deadline event := by
  unfold PublicView.InclusionFitsDeadline at fits
  cases activated : view.activatedAt event with
  | none => rw [activated] at fits; exact fits.elim
  | some entered =>
      rw [activated] at fits
      exact ⟨entered, rfl, fits⟩

omit [DecidableEq Player] in
theorem PublicView.InclusionFitsDeadline.withinDeadline {runtime : EventGraphRuntime graph}
    {bound : graph.EventId → Nat} {view : PublicView graph} {event : graph.EventId}
    (fits : view.InclusionFitsDeadline runtime bound event) :
    view.WithinDeadline runtime event := by
  unfold PublicView.InclusionFitsDeadline at fits
  unfold PublicView.WithinDeadline
  cases activated : view.activatedAt event with
  | none => rw [activated] at fits; exact fits
  | some entered =>
      rw [activated] at fits
      change view.clock - entered < runtime.deadline event
      omega

end Vegas.EventGraphRuntime
