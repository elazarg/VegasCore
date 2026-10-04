/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePolicy

/-! # Selecting one player's recorded response aliases

The selected policy changes only which physical name implements a source
Boolean choice. At a compatible recorded input it chooses the recorded response
for that response's Boolean branch. Its Boolean law is unchanged at every
input, including incompatible inputs. The global checkpoint argument must still
establish compatibility along histories sharing the selected source view.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))

open Classical in
/-- This is an ordinary native policy. The reference is fixed when selecting
the information site, and only the focal player's actual local input is read. -/
def focalPolicy (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (reference : List (application setup leaks).PlayerEntry) :
    (application setup leaks).Policy := fun past view =>
  let baseline := ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne
    who past view
  match reference[past.length]? with
  | none => baseline
  | some entry =>
      if past = reference.take past.length ∧ entry.beforeView = view ∧
          entry.action ∈ ordinaryActions setup leaks bounds who past view then
        baseline.map (fun response =>
          if sourceChoice setup leaks response = sourceChoice setup leaks entry.action
          then entry.action else response)
      else baseline

/-- The selector cannot change the probability of either source choice. -/
theorem focalPolicy_projects (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (reference past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (focalPolicy setup leaks bounds profile weight nonnegative atMostOne who reference
        past view).map (sourceChoice setup leaks) =
      (ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne
        who past view).map (sourceChoice setup leaks) := by
  classical
  unfold focalPolicy
  split
  · rfl
  · split
    · rw [PMF.map_comp]
      congr 1
      funext response
      dsimp only [Function.comp_def]
      split
      · rename_i same
        exact same.symm
      · rfl
    · rfl

theorem focalPolicy_covered (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (reference past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (supported : response ∈ (focalPolicy setup leaks bounds profile weight nonnegative
      atMostOne who reference past view).support) :
    response ∈ ordinaryActions setup leaks bounds who past view := by
  classical
  unfold focalPolicy at supported
  split at supported
  · exact ordinaryPolicy_covered setup leaks bounds profile weight nonnegative atMostOne
      who past view response supported
  · split at supported
    · rename_i compatible
      obtain ⟨original, present, rfl⟩ := PMF.support_map .. ▸ supported
      dsimp only
      split
      · exact compatible.2.2
      · exact ordinaryPolicy_covered setup leaks bounds profile weight nonnegative atMostOne
          who past view original present
    · exact ordinaryPolicy_covered setup leaks bounds profile weight nonnegative atMostOne
        who past view response supported

/-- On the recorded Boolean branch, every supported selected response is the
recorded physical response. This holds even if that alias has zero limiting
probability under the original policy. -/
theorem focalPolicy_selects (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (reference past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (entry : (application setup leaks).PlayerEntry)
    (recorded : reference[past.length]? = some entry)
    (earlier : past = reference.take past.length) (observed : entry.beforeView = view)
    (allowed : entry.action ∈ ordinaryActions setup leaks bounds who past view)
    (response : (application setup leaks).Action)
    (supported : response ∈ (focalPolicy setup leaks bounds profile weight nonnegative
      atMostOne who reference past view).support)
    (sameChoice : sourceChoice setup leaks response = sourceChoice setup leaks entry.action) :
    response = entry.action := by
  classical
  unfold focalPolicy at supported
  rw [recorded] at supported
  dsimp only at supported
  rw [ite_eq_left ⟨earlier, observed, allowed⟩] at supported
  obtain ⟨original, _present, same⟩ := PMF.support_map .. ▸ supported
  dsimp only at same
  split at same
  · exact same.symm
  · rename_i different
    subst response
    exact False.elim (different sameChoice)

/-- The selected policy is available in the same finite native game. The
watcher stays fixed, and this construction changes only the focal player. -/
def focalProfile (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player)
    (reference : List (application setup leaks).PlayerEntry) :
    GameTheory.Profile (information setup leaks bounds watcher).behavioralSignature :=
  (compiledProfile setup leaks bounds watcher profile weight nonnegative atMostOne).update who
    ((menu setup leaks bounds watcher).restrictPolicy (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) who
      (focalPolicy setup leaks bounds profile weight nonnegative atMostOne who reference))

theorem focalProfile_other (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player)
    (reference : List (application setup leaks).PlayerEntry)
    (other : Player) (different : other ≠ who) :
    focalProfile setup leaks bounds watcher profile weight nonnegative atMostOne who
        reference other =
      compiledProfile setup leaks bounds watcher profile weight nonnegative atMostOne other := by
  simp only [focalProfile, GameTheory.Profile.update_of_ne _ _ different]

/-- Decoding the chosen player's actual behavioral policy gives the selected
physical policy at all inputs, including those outside initialized support. -/
theorem focalProfile_decode (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (ordinary : who ≠ watcher)
    (reference : List (application setup leaks).PlayerEntry) :
    (application setup leaks).decodePolicy
        ((menu setup leaks bounds watcher).embedPolicy (initialLaw setup) (horizon setup watcher)
          (scheduler setup leaks watcher) who
          (focalProfile setup leaks bounds watcher profile weight nonnegative atMostOne
            who reference who)) =
      focalPolicy setup leaks bounds profile weight nonnegative atMostOne who reference := by
  simp only [focalProfile, GameTheory.Profile.update_same]
  apply (menu setup leaks bounds watcher).decode_restrictPolicy_of_covered
  intro past view response supported
  change response ∈ (if who = watcher then _ else _)
  rw [ite_eq_right ordinary]
  exact focalPolicy_covered setup leaks bounds profile weight nonnegative atMostOne
    who reference past view response supported

end Vegas
