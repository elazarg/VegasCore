/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import GameTheoryExtensions.Math.Probability.ActionSplitting
import Vegas.Game.ServiceInformation
import Vegas.Pending.ReactiveOpeningWindow

/-! # One source policy over all visits of a revelation roster

These are policies on the existing native input: actual own recall and current
view. The source disclosure law and authentic opening are recovered from that
view. A fixed public roster supplies response-count offsets. Conditional timing
is a proof parameter for fully mixed approximants, not private runtime state.

The limiting policy explicitly stops after an opening. It does not evaluate a
zero-probability latent-mixture fallback at an off-path early opening. Coverage,
all-site consistency and sequential optimality remain separate obligations.
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

def rosterSelection {slots : Nat} (choice : PMF Bool) (timing : PMF (Fin slots)) :
    PMF (Option (Fin slots)) :=
  choice.bind fun disclose => if disclose then timing.map some else PMF.pure none

theorem rosterSelection_projects {slots : Nat} (choice : PMF Bool)
    (timing : PMF (Fin slots)) :
    (rosterSelection choice timing).map Option.isSome = choice := by
  rw [rosterSelection, PMF.map_bind]
  conv_rhs => rw [← PMF.bind_pure choice]
  apply bind_congr_on_support _
  intro disclose _
  cases disclose
  · simp only [Bool.false_eq_true, ↓reduceIte, PMF.pure_map, Option.isSome_none]
  · simp only [↓reduceIte, PMF.map_comp, Function.comp_def, Option.isSome_some]
    exact PMF.map_const _ _

theorem rosterSelection_fullSupport {slots : Nat} (choice : PMF Bool)
    (timing : PMF (Fin slots)) (choiceFull : FullSupport choice)
    (timingFull : FullSupport timing) : FullSupport (rosterSelection choice timing) := by
  intro selected
  simp only [rosterSelection, PMF.support_bind, Set.mem_iUnion]
  cases selected with
  | none => exact ⟨false, choiceFull false, by simp⟩
  | some slot =>
      refine ⟨true, choiceFull true, ?_⟩
      simp only [↓reduceIte, PMF.support_map]
      exact ⟨slot, timingFull slot, rfl⟩

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
