/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceMenu
import Vegas.Game.SourceServicePolicy
import Vegas.Game.ServiceRoster
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ScheduledOpening

/-! # Shared timing of full-source decisions

One ordinary behavioral policy realizes a common timing lottery at each
source event. The source decision is drawn at the selected owner visit.
All other visits retain the real silent policy. Every family checks actual
own recall before emitting, including at off-path inputs of the mixture.
The latent slot is proof data of behavioral realization, not runtime state.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The existing source decision with silent choices realized by the full
silent policy. Recorded prior emissions stop every timing branch. -/
def sourceServiceOpportunity
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId) :
    (application setup leaks).Policy := fun past view =>
  if (runtime setup).eventRecorded leaks past event then
    (application setup leaks).silentPolicy past view
  else (sourceServicePolicy setup leaks profile who past view).bind fun response =>
    if response.transmission = none then (application setup leaks).silentPolicy past view
    else PMF.pure response

def sourceServiceTimedFamily
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program) (who : Player) (event : (graph setup).EventId)
    (slot : Fin ((rosters event).count who)) : (application setup leaks).Policy :=
  (application setup leaks).scheduledPolicy (rosterOffset setup rosters who event) (some slot)
    (sourceServiceOpportunity setup leaks profile who event)
    (application setup leaks).silentPolicy

def sourceServiceTimedPolicy
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (application setup leaks).silentPolicy past view
  | some event =>
      if owned : (graph setup).actor? event = some who then
        ((application setup leaks).policyMixture (timing event who owned)
          (sourceServiceTimedFamily setup leaks rosters profile who event)).policy past view
      else (application setup leaks).silentPolicy past view

end Vegas
