/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForcedRegular
import Vegas.Game.OnePacketFailureBridge

/-! # Accepted handles for completed debt-free bindings

Foreign owners remain active in the public record. A failed completed binding
would leave its focal owner owing a failure; debt freedom therefore gives a
successful stored value, whose native provenance supplies an accepted handle.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}

/-- Every completed binding has an accepted handle if foreign owners remain
active and the focal owner owes no failure at the actual decoded prefix. -/
theorem completedBinding_accepted_of_publicRecord
    {who : Player} {control : (application setup timeouts leaks).Control}
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control))
    (record : PublicRecord setup timeouts who control)
    (debtFree : ∀ point, nativeDecodedState setup timeouts leaks (some control) = some point →
      ¬ ProtocolState.OwesFailure who setup.program point)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (layoutEq : (graph setup).outputLayout event = .binding owner payload)
    (completed : event ∈ control.execution.application.config.cut.completed) :
    control.execution.application.accepted (.inr event) ≠ none := by
  by_cases mine : owner = who
  · subst owner
    let ref : EventGraph.FieldRef (graph setup).layout (.binding who payload) :=
      ⟨.inr event, layoutEq⟩
    have present := (control.execution.application.config.output_available event).mpr completed
    obtain ⟨result, read⟩ := Option.isSome_iff_exists.mp
      (ref.get?_isSome control.execution.application.config.store present)
    have rawTrace := (bounds.onePacketMenu timeouts leaks).toRawTrace
      (initialLaw setup) horizon scheduler trace
    cases result with
    | failure =>
        obtain ⟨rank, ⟨residual⟩, failures⟩ := failedBindingRecord_history (timeouts := timeouts)
          (failureProfile setup.program) horizon scheduler rawTrace
        exact (debtFree _ (decodedPoint_eq residual)
          (failures event completed who payload layoutEq read _ residual.decode)).elim
    | success value =>
        have valid : control.execution.application.BindingInvariant :=
          ((reactiveBindingInvariant timeouts) leaks).history (initialLaw setup) horizon
            scheduler (fun state member => by
              obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ member
              exact State.initial_bindingInvariant _) rawTrace
        obtain ⟨handle, accepted, _, _⟩ := valid.success_provenance ref value read
        rw [accepted]
        exact Option.some_ne_none handle
  · exact record.bindingAccepted trace event owner payload layoutEq mine completed

end Vegas
