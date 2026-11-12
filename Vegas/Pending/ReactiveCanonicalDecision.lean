module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactivePolicyFacts
public import Vegas.Pending.EventPublicState

@[expose] public section

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
def canonicalFreshSlot (who : Player) (view : PlayerView graph) : Option Nat :=
  if view.candidates (.prepared (view.publicView.bindingCount who)) = .fresh then
    some (view.publicView.bindingCount who) else reactiveFreshSlot view

theorem canonicalFreshSlot_spec (who : Player) (view : PlayerView graph) (serial : Nat)
    (selected : canonicalFreshSlot who view = some serial) :
    view.candidates (.prepared serial) = .fresh := by
  classical
  unfold canonicalFreshSlot at selected
  split at selected
  · rename_i fresh
    cases Option.some.inj selected
    exact fresh
  · exact reactiveFreshSlot_spec view serial selected

theorem canonicalFreshSlot_canonical (who : Player) (view : PlayerView graph)
    (fresh : view.candidates (.prepared (view.publicView.bindingCount who)) = .fresh) :
    canonicalFreshSlot who view = some (view.publicView.bindingCount who) := by
  classical
  unfold canonicalFreshSlot
  simp only [fresh, ↓reduceIte]

/-- Some slot is chosen whenever a fresh slot exists. -/
theorem canonicalFreshSlot_isSome (who : Player) (view : PlayerView graph)
    (serial : Nat) (selected : reactiveFreshSlot view = some serial) :
    ∃ chosen, canonicalFreshSlot who view = some chosen := by
  classical
  unfold canonicalFreshSlot
  split
  · exact ⟨_, rfl⟩
  · exact ⟨serial, selected⟩

/-- `reactiveDecision` with a binding submitted at `canonicalFreshSlot`. -/
def canonicalReactiveDecision (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId)
    (action : graph.Action event) (view : PlayerView graph) :
    ((reactiveApplication timeouts) leaks).Action where
  transmission := if who ∈ view.publicView.observation.defaulted then none else
    match nodeView graph event with
    | .sample .. => none
    | .bind _owner payload outputEq _codeEq =>
        (cast (congrArg EventField.Action outputEq) action :
          Option (PublicationResult (L.Val payload))).bind fun result =>
          (canonicalFreshSlot who view).map fun serial =>
            ⟨⟨.commitment event (who, .prepared serial),
              match result with
              | .failure => none
              | .success value => some ⟨payload, value⟩⟩, .none⟩
    | .resolve _owner payload binding checks outputEq _codeEq =>
        (reactiveResolutionPacket who event payload binding checks outputEq action view).map
          fun packet => (disclosureSubmission packet).normalizeReactive who view []

/-- `serviceDecision` over `canonicalReactiveDecision`: withheld publications
stay silent until expiry and private response aliases are normalized. -/
def canonicalServiceDecision (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event) :
    ((reactiveApplication timeouts) leaks).Action :=
  ((reactiveNormalization timeouts) leaks).action who past view
    ((canonicalReactiveDecision timeouts) leaks who event choice view.application)

/-- Away from bindings the canonical decision agrees with the uncounted decision. -/
theorem canonicalReactiveDecision_eq_of_not_bind (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (event : graph.EventId) (action : graph.Action event)
    (view : PlayerView graph)
    (notBind : ∀ owner payload outputEq codeEq,
      nodeView graph event ≠ .bind owner payload outputEq codeEq) :
    (canonicalReactiveDecision timeouts) leaks who event action view =
      (reactiveDecision timeouts) leaks who event action view := by
  unfold canonicalReactiveDecision reactiveDecision
  congr 1
  cases node : nodeView graph event with
  | sample => rfl
  | bind owner payload outputEq codeEq => exact (notBind owner payload outputEq codeEq node).elim
  | resolve => rfl

/-- A canonical client sends no traffic after its public default. -/
theorem canonicalServiceDecision_defaulted (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (inactive : who ∈ view.application.publicView.observation.defaulted) :
    (canonicalServiceDecision timeouts) leaks who past view event choice = ⟨none⟩ := by
  simp only [canonicalServiceDecision, canonicalReactiveDecision, ite_eq_left inactive]
  rfl

/-- A transmitted canonical decision belongs to an owner who has not publicly defaulted. -/
theorem canonicalServiceDecision_active (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (material : ((reactiveApplication timeouts) leaks).Submission)
    (submits : ((canonicalServiceDecision timeouts) leaks who past view event choice).transmission =
      some material) :
    who ∉ view.application.publicView.observation.defaulted := by
  intro inactive
  rw [(canonicalServiceDecision_defaulted timeouts) leaks who past view event choice inactive]
    at submits
  cases submits

theorem canonicalServiceDecision_eq_of_not_bind (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (choice : graph.Action event)
    (notBind : ∀ owner payload outputEq codeEq,
      nodeView graph event ≠ .bind owner payload outputEq codeEq) :
    (canonicalServiceDecision timeouts) leaks who past view event choice =
      (serviceDecision timeouts) leaks who past view event choice := by
  unfold canonicalServiceDecision serviceDecision
  rw [(canonicalReactiveDecision_eq_of_not_bind timeouts) leaks who event choice view.application
    notBind]

/-- An admitted binding submits the canonical binding at the selected slot. -/
theorem canonicalServiceDecision_binding (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding who payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .bind who payload)
    (node : nodeView graph event = .bind who payload outputEq codeEq)
    (active : who ∉ view.application.publicView.observation.defaulted)
    (serial : Nat) (selected : canonicalFreshSlot who view.application = some serial)
    (result : PublicationResult (L.Val payload)) :
    (canonicalServiceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) (some result)) =
      (reactiveBinding timeouts) leaks who event payload result serial := by
  have fresh := canonicalFreshSlot_spec who view.application serial selected
  have normalized : (canonicalServiceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) (some result)) =
      ((reactiveNormalization timeouts) leaks).action who past view
        ((reactiveBinding timeouts) leaks who event payload result serial) := by
    simp only [canonicalServiceDecision, canonicalReactiveDecision, ite_eq_right active,
      node, selected, Option.map_some, cast_cast, cast_eq, Option.bind_some]
    rfl
  rw [normalized]
  exact (reactiveBinding_normal_of_fresh timeouts) leaks who past view event payload result serial
    fresh

/-- A selected binding omission stays silent, including when candidate slots are available. -/
theorem canonicalServiceDecision_binding_none (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq) :
    (canonicalServiceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm)
        (none : Option (PublicationResult (L.Val payload)))) = ⟨none⟩ := by
  simp only [canonicalServiceDecision, canonicalReactiveDecision, node, cast_cast, cast_eq,
    Option.bind_none, ite_self]
  rfl

/-- An authentic opening transmits without predicting its public guard result. -/
theorem canonicalServiceDecision_openable (timeouts : EventTimeouts graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (who : Player) (past : List ((reactiveApplication timeouts) leaks).PlayerEntry)
    (view : ((reactiveApplication timeouts) leaks).PlayerView)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (active : who ∉ view.application.publicView.observation.defaulted)
    (value : L.Val payload)
    (stored : binding.get? view.application.observation.store = some (.success value))
    (candidate : Handle graph)
    (accepted : view.application.publicView.accepted binding.field = some candidate)
    (owned : candidate.1 = who) :
    ((canonicalServiceDecision timeouts) leaks who past view event
      (cast (congrArg EventField.Action outputEq.symm) true)).transmission ≠ none := by
  simp only [canonicalServiceDecision, canonicalReactiveDecision, ite_eq_right active, node,
    reactiveResolutionPacket_openable who event payload binding checks outputEq view.application
      active value stored candidate accepted owned,
    Option.map_some, ReactiveApplication.SubmissionNormalization.action, ne_eq,
    reduceCtorEq, not_false_eq_true]

/-- The public deadline still admits inclusion of a packet for `event`. -/
def PublicView.WithinDeadline (timeouts : EventTimeouts graph) (view : PublicView graph)
    (event : graph.EventId) : Prop :=
  match view.activatedAt event with
  | none => False
  | some entered => view.clock - entered < timeouts.duration event

/-- A fresh call emitted now and included within `bound event` slots is
included strictly before `event`'s deadline. -/
def PublicView.InclusionFitsDeadline (timeouts : EventTimeouts graph)
    (bound : graph.EventId → Nat) (view : PublicView graph) (event : graph.EventId) : Prop :=
  match view.activatedAt event with
  | none => False
  | some entered => view.clock - entered + bound event < timeouts.duration event

instance (timeouts : EventTimeouts graph) (bound : graph.EventId → Nat)
    (view : PublicView graph) (event : graph.EventId) :
    Decidable (view.InclusionFitsDeadline timeouts bound event) := by
  unfold PublicView.InclusionFitsDeadline
  split <;> infer_instance

omit [DecidableEq Player] in
theorem PublicView.InclusionFitsDeadline.exists {timeouts : EventTimeouts graph}
    {bound : graph.EventId → Nat} {view : PublicView graph} {event : graph.EventId}
    (fits : view.InclusionFitsDeadline timeouts bound event) :
    ∃ entered, view.activatedAt event = some entered ∧
      view.clock - entered + bound event < timeouts.duration event := by
  unfold PublicView.InclusionFitsDeadline at fits
  cases activated : view.activatedAt event with
  | none => rw [activated] at fits; exact fits.elim
  | some entered =>
      rw [activated] at fits
      exact ⟨entered, rfl, fits⟩

omit [DecidableEq Player] in
theorem PublicView.InclusionFitsDeadline.withinDeadline {timeouts : EventTimeouts graph}
    {bound : graph.EventId → Nat} {view : PublicView graph} {event : graph.EventId}
    (fits : view.InclusionFitsDeadline timeouts bound event) :
    view.WithinDeadline timeouts event := by
  unfold PublicView.InclusionFitsDeadline at fits
  unfold PublicView.WithinDeadline
  cases activated : view.activatedAt event with
  | none => rw [activated] at fits; exact fits
  | some entered =>
      rw [activated] at fits
      change view.clock - entered < timeouts.duration event
      omega

end Vegas.EventGraphRuntime
