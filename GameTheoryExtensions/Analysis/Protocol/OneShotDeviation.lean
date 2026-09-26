/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.LocalDeviation

/-! # One deviating step followed by the original continuation

The hybrid laws used in a finite deviation decomposition are ordinary
behavioral runs composed by binding finite probability laws. Perfect recall identifies one
deviating step with installing the same behavioral law at its information
site: the site cannot be revisited later in that continuation.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)

theorem one_step_then_baseline_eq_local_law (recall : M.PerfectRecall)
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    [DecidableEq (M.InfoState who)] (alternative : M.BehavioralPolicy who)
    (history : E.History) (active : E.active history.state who) (fuel : Nat) :
    (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
      profile who alternative) 1 history).bind (M.runBehavioralFrom profile fuel) =
    M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature) profile who
      ((profile who).withLaw (M.infoOf who history.trace)
        (alternative (M.infoOf who history.trace)))) (fuel + 1) history := by
  let updated := Profile.update (sig := M.behavioralSignature) profile who alternative
  let localProfile := Profile.update (sig := M.behavioralSignature) profile who
    ((profile who).withLaw (M.infoOf who history.trace)
      (alternative (M.infoOf who history.trace)))
  by_cases terminal : E.terminal history.state
  · rw [M.runBehavioralFrom_of_terminal _ _ terminal,
      FinDist.pure_bind, M.runBehavioralFrom_of_terminal _ _ terminal,
      M.runBehavioralFrom_of_terminal _ _ terminal]
  · have current : M.behavioralJoint updated history.trace terminal =
        M.behavioralJoint localProfile history.trace terminal := by
      apply M.behavioralJoint_congr
      intro player
      by_cases same : player = who
      · subst player
        simp [updated, localProfile]
      · simp [updated, localProfile, Profile.update_of_ne _ _ same]
    rw [M.runBehavioralFrom_succ_of_not_terminal _ 0 terminal,
      M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal, current, FinDist.bind_bind]
    apply FinDist.bind_congr
    intro draw _
    rw [FinDist.bind_bindOnSupport]
    apply FinDist.bindOnSupport_congr
    intro target realized
    change (FinDist.pure _).bind _ = _
    rw [FinDist.pure_bind]
    apply M.runBehavioralFrom_congr
    intro later reached _ player
    by_cases same : player = who
    · subst player
      have different := M.infoOf_ne_of_perfectRecall_after_step recall who draw.2
        realized active reached
      rw [Profile.update_same]
      exact (BehavioralPolicy.withLaw_of_ne _ _ _ different).symm
    · rw [Profile.update_of_ne _ _ same]

/-- When the player does not act, changing its whole policy has no effect on
this one step. Later play in both branches is explicitly the same baseline. -/
theorem one_step_then_baseline_eq_of_inactive
    (profile : ∀ player, M.BehavioralPolicy player) (who : Player)
    (alternative : M.BehavioralPolicy who) (history : E.History)
    (inactive : ¬ E.active history.state who) (fuel : Nat) :
    (M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
      profile who alternative) 1 history).bind (M.runBehavioralFrom profile fuel) =
      M.runBehavioralFrom profile (fuel + 1) history := by
  have first : M.runBehavioralFrom (Profile.update (sig := M.behavioralSignature)
      profile who alternative) 1 history = M.runBehavioralFrom profile 1 history := by
    apply M.runBehavioralFrom_congr_before
    intro later reached _ before player
    have sameHistory : later = history := by
      cases reached with
      | refl => rfl
      | step joint legal realized rest =>
          have after := rest.trace_length_le
          simp only [History.extend, Trace.length] at after
          omega
    subst later
    by_cases same : player = who
    · subst player
      exact M.behavioral_eq_of_not_active _ _ history.trace inactive
    · rw [Profile.update_of_ne _ _ same]
  rw [first, ← M.runBehavioralFrom_add]
  congr 1
  omega

end GameTheory.Protocol.InformationModel
