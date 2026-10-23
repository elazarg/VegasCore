/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPolicy
import Vegas.Pending.ReactiveCompiledMenu

/-! # Deferred binding opportunities in the source service

The retained menu uses the player's turn and its own response
count to identify the last owner visit of a fixed finite roster. Before that
visit, a binding may wait. At the last visit an unsent binding must
submit a typed value. Once submitted, no second fresh call of the event is
permitted. Resolution keeps the ordinary guarded-opening menu.

This is an information-local restriction of the unchanged bounded raw runtime.
The actual-history count lemma below identifies its last-visit test; covered
binding checkpoints make the total fallback unreachable. Source correspondence
and deadline evidence remain separate obligations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The only compulsory response is an unsent binding at its last owner visit.
Every ingredient is already present in the local input or the static roster. -/
def bindingRequired (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Prop :=
  ∃ event payload,
    view.application.publicView.ownTurn? who = some event ∧
    (graph setup).outputLayout event = .binding who payload ∧
    (graph setup).actor? event = some who ∧
    view.application.publicView.EventReady event ∧
    (runtime setup).eventRecorded leaks past event = false ∧
    past.length + 1 = rosterOffset setup rosters who event + (rosters event).count who

variable [Fintype Player]

open Classical in
def sourceServiceActions (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Finset (application setup leaks).Action :=
  if bindingRequired setup leaks rosters who past view then
    bounds.requiredBindingActions (runtime setup) leaks who past view
  else bounds.compiledActions (runtime setup) leaks who past view

def sourceServiceMenu (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player) :
    (application setup leaks).ResponseMenu where
  actions := sourceServiceActions setup leaks bounds rosters
  nonempty who past view := by
    classical
    unfold sourceServiceActions
    split
    · exact bounds.requiredBindingActions_nonempty (runtime setup) leaks who past view
    · exact bounds.compiledActions_nonempty (runtime setup) leaks who past view

end Vegas
