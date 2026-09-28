/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import GameTheoryExtensions.Math.Probability.ActionSplitting

/-! # Source choices and published replay aliases

At a covered revelation opportunity, the actual ordinary menu projects to the
source Boolean choice: its sole submission opens the commitment, while silence
and replays of published envelopes withhold it. Finite action splitting gives
exact projected laws and full support. These local facts do not assert a
history correspondence or sequential equilibrium preservation.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Normalizing the requested certificate preserves the submission constructor. -/
theorem opening_is_submission (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some response) :
    ∃ submission, response = ⟨some (.submit submission)⟩ := by
  unfold opening? at selected
  obtain ⟨event, _granted, selected⟩ := Option.bind_eq_some_iff.mp selected
  split at selected
  · cases selected
  · cases node : nodeView (graph setup) event with
    | sample => simp only [node] at selected; cases selected
    | bind => simp only [node] at selected; cases selected
    | resolve owner payload binding checks outputEq codeEq =>
        simp only [node] at selected
        cases resolved : EventGraph.EventCode.resolveOutput? binding checks true
            view.application.observation.store with
        | none => simp only [resolved] at selected; cases selected
        | some publication =>
            cases publication with
            | failure => simp only [resolved] at selected; cases selected
            | success value =>
                simp only [resolved] at selected
                obtain ⟨candidate, _accepted, selected⟩ := Option.bind_eq_some_iff.mp selected
                split at selected
                · cases selected
                · have same := Option.some.inj selected
                  refine ⟨_, same.symm⟩

/-- The decoder keeps the distinction between publication and refusal, while
every private name for refusal has the same source choice. -/
def sourceChoice (response : (application setup leaks).Action) : Bool :=
  match response.transmission with
  | some (.submit _) => true
  | none | some (.replay _) => false

theorem sourceChoice_opening (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some response) :
    sourceChoice setup leaks response = true := by
  obtain ⟨submission, rfl⟩ := opening_is_submission setup leaks who past view response selected
  rfl

theorem opening_ne_silence (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some response) : response ≠ ⟨none⟩ := by
  intro same
  have choice := sourceChoice_opening setup leaks who past view response selected
  rw [same] at choice
  cases choice

theorem opening_ne_replay (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some response) (id : MessageId Player) :
    response ≠ ⟨some (.replay id)⟩ := by
  intro same
  have choice := sourceChoice_opening setup leaks who past view response selected
  rw [same] at choice
  cases choice

variable [Fintype Player] (bounds : MessageBounds (graph setup))

/-- Decoding a false choice does not discard the requirement that every replay
identifier came from the current ledger. -/
theorem ordinary_false_iff (who : Player)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds who past view) :
    sourceChoice setup leaks response = false ↔ response = ⟨none⟩ ∨
      ∃ message ∈ view.messages.ledger, response = ⟨some (.replay message.id)⟩ := by
  constructor
  · intro refuses
    rcases ordinary_response_cases setup leaks bounds who past view response member with
      silent | opening | replay
    · exact Or.inl silent
    · rw [sourceChoice_opening setup leaks who past view response opening] at refuses
      cases refuses
    · exact Or.inr replay
  · rintro (rfl | ⟨message, _published, rfl⟩) <;> rfl

variable (who : Player) (past : List (application setup leaks).PlayerEntry)
  (view : (application setup leaks).PlayerView) (opening : (application setup leaks).Action)
  (selected : opening? setup leaks who past view = some opening)
  (covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view)

include selected in
theorem ordinary_true_iff (response : (application setup leaks).Action)
    (member : response ∈ ordinaryActions setup leaks bounds who past view) :
    sourceChoice setup leaks response = true ↔ response = opening := by
  constructor
  · intro discloses
    rcases ordinary_response_cases setup leaks bounds who past view response member with
      silent | opened | replay
    · rw [silent] at discloses
      cases discloses
    · exact Option.some.inj (opened.symm.trans selected)
    · obtain ⟨message, _published, rfl⟩ := replay
      cases discloses
  · intro same
    rw [same]
    exact sourceChoice_opening setup leaks who past view opening selected

def canonicalOrdinaryChoice (disclose : Bool) :
    {response // response ∈ ordinaryActions setup leaks bounds who past view} :=
  if disclose then ⟨opening, opening_ordinary setup leaks bounds who past view opening
    selected covered⟩ else ⟨⟨none⟩, silence_ordinary setup leaks bounds who past view⟩

theorem sourceChoice_canonical (disclose : Bool) :
    sourceChoice setup leaks
      (canonicalOrdinaryChoice setup leaks bounds who past view opening selected covered
        disclose).1 = disclose := by
  cases disclose
  · rfl
  · exact sourceChoice_opening setup leaks who past view opening selected

def splitChoiceLaw (law : FinDist Bool) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    FinDist {response // response ∈ ordinaryActions setup leaks bounds who past view} :=
  law.bind (FinDist.splitKernel (fun response => sourceChoice setup leaks response.1)
    (canonicalOrdinaryChoice setup leaks bounds who past view opening selected covered)
    (sourceChoice_canonical setup leaks bounds who past view opening selected covered)
    weight nonnegative atMostOne)

theorem splitChoiceLaw_project (law : FinDist Bool) (weight : ℝ)
    (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    (splitChoiceLaw setup leaks bounds who past view opening selected covered
      law weight nonnegative atMostOne).map (fun response => sourceChoice setup leaks response.1) =
        law :=
  FinDist.split_project _ _ _ law weight nonnegative atMostOne

theorem splitChoiceLaw_fullSupport (law : FinDist Bool) (mixed : law.FullSupport)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (positive : 0 < weight) :
    (splitChoiceLaw setup leaks bounds who past view opening selected covered
      law weight nonnegative atMostOne).FullSupport :=
  FinDist.split_fullSupport _ _ _ law mixed weight nonnegative atMostOne positive

end Vegas
