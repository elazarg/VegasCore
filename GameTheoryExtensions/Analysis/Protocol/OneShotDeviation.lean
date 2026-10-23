/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Math.Probability.Support
import GameTheory.Analysis.Protocol.CounterfactualDecomposition
import GameTheory.Protocol.DecisionRecall

/-! # One deviating step followed by the original continuation

The hybrid laws used in a finite deviation decomposition are ordinary
behavioral runs composed by binding finite probability laws. A decision
information antichain identifies one deviating step with installing the same
behavioral law at its information site: that site cannot be revisited later.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol

variable {Player : Type} [Fintype Player] [DecidableEq Player]
  {E : ExecutionProtocol Player} (M : InformationModel E)

theorem one_step_then_baseline_eq_local_law (antichain : M.DecisionInformationAntichain)
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
      PMF.pure_bind, M.runBehavioralFrom_of_terminal _ _ terminal,
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
      M.runBehavioralFrom_succ_of_not_terminal _ fuel terminal, current, PMF.bind_bind]
    apply bind_congr_on_support _
    intro draw _
    rw [bindOnSupport_bind]
    apply bindOnSupport_congr _
    intro target realized
    change (PMF.pure _).bind _ = _
    rw [PMF.pure_bind]
    apply M.runBehavioralFrom_congr
    intro later reached _ player
    by_cases same : player = who
    · subst player
      have different : M.infoOf who later.trace ≠ M.infoOf who history.trace := by
        intro sameInfo
        obtain ⟨site, same⟩ := M.exists_informationSite_of_active who history draw.2.1 active
        exact antichain who site ⟨history, same.symm⟩ ⟨later, sameInfo.trans same.symm⟩
          draw.1 draw.2 _ realized _ reached
      rw [Profile.update_same]
      exact (BehavioralPolicy.withLaw_of_ne _ _ _ different).symm
    · rw [Profile.update_of_ne _ _ same]

end GameTheory.Protocol.InformationModel
