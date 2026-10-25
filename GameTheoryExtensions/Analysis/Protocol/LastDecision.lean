/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Analysis.Protocol.CounterfactualRegret
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Optimal behavior at a player's last decision

If a player has no later decision, its full continuation behavior factors
through the one current choice. Finite maximization then chooses an optimal
response at each information site. If changing this player's policy leaves
every decision-history reach probability unchanged and the other players are
indifferent, a common fully mixed perturbation supplies a sequential
equilibrium. The maximization constructs an equilibrium; it is not a strategy
compiler and may depend on the utility.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability ExecutionProtocol Filter

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ExecutionProtocol ι} {M : InformationModel E}

/-- A structural property of legal continuations, independent of strategies. -/
def LastDecision (who : ι) : Prop :=
  ∀ (history : E.History), E.active history.state who →
    ∀ (joint : ∀ player, Option (E.Action player)) (legal : E.Legal history.state joint)
      (target : E.State) (realized : target ∈ (E.step history.state ⟨joint, legal⟩).support)
      (fuel : Nat) (later : E.History),
      E.ReachesWithin fuel (history.extend legal realized) later →
        ¬ E.active later.state who

section Consistency

/-- When one player's policy cannot affect any decision-history reach
weight, replacing it preserves the reference Bayes beliefs. One common
fully mixed sequence witnesses consistency of the replaced profile. -/
theorem consistent_update_of_reach_invariant
    (reference : M.BehavioralAssessment) (mixed : reference.IsFullyMixed)
    (antichain : M.DecisionInformationAntichain) (who : ι)
    (reach : ∀ (alternative : M.BehavioralPolicy who) (player : ι)
      (site : M.InformationSite player) (history : M.InformationHistory player site.1),
      M.historyReachWeight
        (Profile.update (sig := M.behavioralSignature) reference.strategy who alternative)
          history.1 = M.historyReachWeight reference.strategy history.1)
    (policy : M.BehavioralPolicy who) :
    (⟨Profile.update (sig := M.behavioralSignature) reference.strategy who policy,
      (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief⟩ :
        M.BehavioralAssessment).IsSequentiallyConsistent antichain := by
  classical
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp [weight]; positivity
  have atMostOne (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let response (n : Nat) : M.BehavioralPolicy who := fun info =>
    mix (weight n) (positive n).le (atMostOne n)
      (reference.strategy who info) (policy info)
  let sequence (n : Nat) : M.BehavioralAssessment :=
    ⟨Profile.update (sig := M.behavioralSignature) reference.strategy who (response n),
      (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief⟩
  refine ⟨sequence, ?_, ?_⟩
  · intro n
    constructor
    · intro player site choice
      by_cases own : player = who
      · subst player
        change choice ∈ (Profile.update (sig := M.behavioralSignature)
          reference.strategy who (response n) who site.1).support
        rw [Profile.update_same]
        exact mem_support_mix_left _ _ _ (positive n) (mixed who site choice)
      · change choice ∈ (Profile.update (sig := M.behavioralSignature)
          reference.strategy who (response n) player site.1).support
        rw [Profile.update_of_ne _ _ own]
        exact mixed player site choice
    · intro player site _ history
      have mass : M.informationMass (sequence n).strategy player site =
          M.informationMass reference.strategy player site := by
        unfold informationMass
        exact tsum_congr fun next => reach (response n) player site next
      change (InformationModel.bayesAssessment _ reference.strategy mixed antichain).belief
        player site history = _
      rw [InformationModel.bayesAssessment, bayesBelief_apply, mass]
      exact congrArg (fun value => value / M.informationMass reference.strategy player site)
        (reach (response n) player site history).symm
  · constructor
    · intro player site
      by_cases own : player = who
      · subst player
        change PMFConvergesPointwise
          (fun n => Profile.update (sig := M.behavioralSignature)
            reference.strategy who (response n) who site.1)
          (Profile.update (sig := M.behavioralSignature)
            reference.strategy who policy who site.1)
        simpa only [Profile.update_same] using
          pmfConvergesPointwise_mix_zero weight (fun n => (positive n).le) atMostOne
            vanishes (reference.strategy who site.1) (policy site.1)
      · change PMFConvergesPointwise
          (fun n => Profile.update (sig := M.behavioralSignature)
            reference.strategy who (response n) player site.1)
          (Profile.update (sig := M.behavioralSignature)
            reference.strategy who policy player site.1)
        simp only [Profile.update_of_ne _ _ own]
        exact pmfConvergesPointwise_const _
    · intro player site
      exact pmfConvergesPointwise_const _

end Consistency

end GameTheory.Protocol.InformationModel
