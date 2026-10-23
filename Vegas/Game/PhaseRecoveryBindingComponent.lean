/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceView
import Vegas.Game.ServiceInformation
import Vegas.Compile.EventGraphBacktranslation
import Vegas.Compile.EventGraphObservationEncoding
import Vegas.Game.CommitRecoveryRestriction
import Vegas.Pending.PhasePreparedOnePacket

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
end Vegas
