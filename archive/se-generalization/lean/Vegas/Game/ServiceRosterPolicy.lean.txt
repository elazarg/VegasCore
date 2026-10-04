/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRuntime
import Vegas.Pending.ReactiveDecisionWindow

/-! # Local data for finite source service rosters
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def rosterOffset (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (event : (graph setup).EventId) : Nat :=
  (((List.finRange (graph setup).order.eventCount).take event.val).flatMap rosters).count who

/-- A timing law: for each event with an owner, a distribution over the owner's
visits in that event's roster. -/
abbrev TimingLaw (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : Type :=
  ∀ event who, (graph setup).actor? event = some who → PMF (Fin ((rosters event).count who))

/-- The immutable local opening data, before choosing an evidence-request
representation. It reads only the owner's current application observation. -/
def rosterOpening? (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    (view : (application setup leaks).PlayerView) : Option (Handle (graph setup) × Raw L) :=
  match nodeView (graph setup) event with
  | .sample .. | .bind .. => none
  | .resolve _ payload binding checks _ _ =>
      match EventGraph.EventCode.resolveOutput? binding checks true
          view.application.observation.store with
      | none | some .failure => none
      | some (.success value) => do
          let candidate ← view.application.publicView.accepted binding.field
          if candidate.1 ≠ who then none else some (candidate, ⟨payload, value⟩)

theorem rosterOpening?_application_eq (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (who : Player) (event : (graph setup).EventId)
    (left right : (application setup leaks).Execution)
    (same : left.application = right.application) :
    rosterOpening? setup leaks who event (left.observe (application setup leaks) who) =
      rosterOpening? setup leaks who event (right.observe (application setup leaks) who) := by
  rcases left with ⟨leftState, leftNetwork, leftReceipts, leftRecall, leftEnvironment⟩
  rcases right with ⟨rightState, rightNetwork, rightReceipts, rightRecall, rightEnvironment⟩
  change leftState = rightState at same
  cases same
  rfl

end Vegas
