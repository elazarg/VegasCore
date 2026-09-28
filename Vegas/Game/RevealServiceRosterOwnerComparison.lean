/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterBayes
import Vegas.Game.RevealServiceRosterWindowValue
import Vegas.Game.SourceLocalContinuation

/-! # Original source choices at actual owner roster sites

The source choice used by the concrete phase policy is the original source
behavioral choice at its recovered information site. Private timing and replay
recall do not select a different source continuation policy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_owner_choice_at_history
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (profile : Profile (setup.informationModel admission).behavioralSignature)
    (who : Player) (control : (application setup leaks).Control)
    (trace : ((rosterMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some control)) (active : control.actor = some who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (grant : control.execution.application.serviceGrant = some event)
    (sourceSite : (setup.informationModel admission).InformationSite who)
    (sourceView : sourceSite.1 = setup.protocolObserve who
      (sourcePrefix? setup event.val control.execution.application.config)) :
    sourceChoiceLaw setup leaks (setup.decodeBehavioralProfile admission profile) who
      (control.execution.observe (application setup leaks) who) =
        (profile who sourceSite.1).map (fun choice => OwnAction.disclosure choice.1) := by
  obtain ⟨actual, _, granted, _, _, initial, state, _, initialSupport, related,
      sourceSupport, grantedAt, _, _, _, _, _, unchanged, _position⟩ :=
    roster_decision_phase setup leaks bounds rosters network reveals openable
      who control trace active
  have same : actual = event := by
    rw [unchanged, grantedAt] at grant
    exact Option.some.inj grant
  subst actual
  obtain ⟨site, observed, choiceLaw, _candidate⟩ :=
    roster_owner_choice_data setup leaks bounds reveals admission profile who event owned
      initial initialSupport state granted related sourceSupport grantedAt
  have decoded := PublicPrefixCheckpoint.decode setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputRef setup.program) 0 event.val state granted related
  change sourcePrefix? setup event.val granted.application.config = some state at decoded
  have sourceSame : site = sourceSite := by
    apply Subtype.ext
    rw [observed, sourceView, unchanged, decoded]
  rw [sourceChoiceLaw_application_eq setup leaks
    (setup.decodeBehavioralProfile admission profile) who _ _ unchanged, choiceLaw, sourceSame]

end Vegas
