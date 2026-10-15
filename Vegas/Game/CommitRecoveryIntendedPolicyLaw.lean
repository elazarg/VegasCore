/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CommitRecoveryIntendedInformation
import Vegas.Game.CommitRecoveryCompiledPolicy

/-! # Compiled policy laws at actual intended recovery checkpoints -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

/-- An actual initialized semantically intended checkpoint derives the original
decision witness needed by the full compiler action-law diagram. -/
theorem commitRecovery_compiled_policy_raw_law_of_intended (wellFormed : setup.WellFormed)
    (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
    (target : ∀ who, setup.commitRecoveryModel.BehavioralPolicy who)
    (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source target)
    (current : CommitRecoveryState setup.program)
    (trace : setup.commitRecoveryProtocol.Trace (some current))
    (clear : current.excluded = ∅)
    (intended : ProtocolState.Intended setup.program current.point)
    (who : Player) (actor : ProtocolState.actor setup.program current.point = some who)
    (event : (toEventGraph setup.program).EventId)
    (eventActor : (toEventGraph setup.program).actor? event = some who)
    (observation : (toEventGraph setup.program).PlayerObservation who)
    (decoded : decodeEventView? setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
        who event observation.store (decodeCompletions setup.program observation.ownActions) =
          some (ProtocolState.observe who setup.program current.point)) :
    let profile := setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.openingExtension source)
    (target who (setup.commitRecoveryClearInformation wellFormed who
      (setup.commitRecoveryPrivate who (some current)))).map Subtype.val =
      ((compileEventPolicy setup.program who (profile who)) event eventActor observation).map
        (fun action => CommitRecoveryMove.lift (decodeEventAction setup.program event action)) := by
  obtain ⟨site, original, _, currentView, _⟩ :=
    setup.commitRecovery_intendedInformation wellFormed current trace clear intended who actor
  exact setup.commitRecovery_compiled_policy_raw_law wellFormed source target copies who site
    original (ProtocolState.observe who setup.program current.point) currentView
    event eventActor observation decoded

end Vegas.SourceProgram.Setup
