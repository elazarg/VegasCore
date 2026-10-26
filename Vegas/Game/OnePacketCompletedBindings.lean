/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketOwnerSettled

/-! # Accepted handles for completed bindings at debt-free forced inputs

The public record excludes missed foreign bindings. A debt-free focal owner
has successful private binding fields, whose runtime provenance supplies their
accepted handles.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

/-- Every completed binding has an accepted handle when the public record
excludes missed foreign bindings and the focal owner owes no failure. -/
theorem completedBinding_accepted_of_publicRecord
    {who : Player} {control : (application setup runtime leaks).Control}
    (trace : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control))
    (record : PublicRecord setup runtime who control)
    (debtFree : ∀ point, nativeDecodedState setup runtime leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (layoutEq : (graph setup).outputLayout event = .binding owner payload)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    control.execution.application.accepted (.inr event) ≠ none := by
  by_cases mine : owner = who
  · subst owner
    have present := (control.execution.application.config.output_available event).mpr completed
    obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp present
    have notFailed := noFailure_of_debtFree (runtime := runtime) trace debtFree (.inr event)
      (privateTo_of_binding layoutEq) value stored
    let ref : EventGraph.FieldRef (graph setup).layout (.binding who payload) :=
      ⟨.inr event, layoutEq⟩
    have read : ref.get? control.execution.application.config.store =
        some (cast (congrArg EventGraph.EventField.Value layoutEq) value) := by
      change cast (congrArg (fun kind => Option kind.Value) layoutEq)
        (control.execution.application.config.outputs event) = _
      rw [stored]
      have castSome {A B : Type} (same : A = B) (entry : A) :
          cast (congrArg Option same) (some entry) = some (cast same entry) := by
        cases same
        rfl
      exact castSome (congrArg EventGraph.EventField.Value layoutEq) value
    have general : ∀ (kind : EventGraph.EventField Player L)
        (same : kind = .binding who payload) (current : kind.Value),
        ¬ kind.IsFailure current → ∃ bound,
          cast (congrArg EventGraph.EventField.Value same) current = .success bound := by
      rintro _ rfl current notFailure
      cases current with
      | failure => exact (notFailure rfl).elim
      | success bound => exact ⟨bound, rfl⟩
    obtain ⟨bound, success⟩ := general _ layoutEq value notFailed
    rw [success] at read
    have rawTrace := (bounds.onePacketMenu runtime leaks).toRawTrace
      (initialLaw setup) horizon scheduler trace
    have valid : control.execution.application.BindingInvariant :=
      (runtime.reactiveBindingInvariant leaks).history (initialLaw setup) horizon
        scheduler (fun state member => by
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
          exact State.initial_bindingInvariant _) rawTrace
    obtain ⟨handle, accepted, _, _⟩ := valid.success_provenance ref bound read
    rw [accepted]
    exact Option.some_ne_none handle
  · exact record.1 event owner payload layoutEq mine completed

end Vegas
