/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView
import Vegas.Game.ServiceInformation
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.Game.CommitRecoveryRestriction
import Vegas.Pending.PhasePreparedOnePacket
import Vegas.Compile.EventGraphBacktranslation

/-! # Actual phased binding components of source recovery assessments

The original source assessment is evaluated at the complete clear information of the
decoded source view. Accepted unusable bindings emit an actual packet, whereas
the distinct source omission flag emits silence. No source history, posterior
identity or future physical service law is assumed here.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Decode the addressed source result and its separate physical omission
flag. Ill-addressed actions are totalized, never used by the legality theorem. -/
def phaseRecoveryBindingData (event : (serviceGraph setup mode).EventId)
    (owner : Player) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (move : Option (CommitRecoveryMove Player L)) : PublicationResult (L.Val payload) × Bool :=
  if move.elim false (·.missing) then (.failure, true) else
    (((move.bind fun action => encodeEventAction? setup.program event action.action).map
      (cast (congrArg EventField.Action outputEq))).getD .failure, false)

/-- Source binding omission waits. A received failed typed binding still emits
its fresh handle, so it is not silently converted into a public omission. -/
def phaseRecoveryBindingResponse (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat) (move : Option (CommitRecoveryMove Player L)) :
    (phaseApplication runtime leaks).Action :=
  let data := phaseRecoveryBindingData setup mode event who payload outputEq move
  if data.2 then ⟨none⟩ else phaseBindingResponse runtime leaks who event payload data.1 serial

/-- One genuine response realizes the original typed result and omission flag
jointly in its actual catalogue and actual transmission decision. -/
theorem phaseRecoveryBindingResponse_result
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (outputEq : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (serial : Nat)
    (fresh : execution.application.current.native.candidates.lookup (who, .prepared serial) =
      .fresh) (move : Option (CommitRecoveryMove Player L)) :
    let response := phaseRecoveryBindingResponse setup mode runtime leaks who event payload
      outputEq serial move
    let after := execution.respond (phaseApplication runtime leaks) who response
    (after.application.current.native.bindingResult (who, .prepared serial) payload,
      response.transmission.isNone) =
      phaseRecoveryBindingData setup mode event who payload outputEq move := by
  cases move with
  | none =>
      change (_, false) = (_, false)
      exact congrArg (fun result => (result, false))
        (phaseBindingResponse_result runtime leaks execution who event payload .failure
          serial fresh)
  | some move =>
      cases missing : move.missing with
      | false =>
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, Option.elim_some,
            missing, Bool.false_eq_true, ↓reduceIte]
          exact congrArg (fun result => (result, false))
            (phaseBindingResponse_result runtime leaks execution who event payload _ serial fresh)
      | true =>
          simp only [phaseRecoveryBindingResponse, phaseRecoveryBindingData, Option.elim_some,
            missing, ↓reduceIte]
          change (execution.application.current.native.bindingResult
            (who, .prepared serial) payload, true) = _
          simp only [State.bindingResult, fresh]

section FiniteMenu

variable [Fintype Player] (bounds : MessageBounds (serviceGraph setup mode))

end FiniteMenu
end Vegas
