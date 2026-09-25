/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.DisclosureEnforcementInformation

/-! # Reach probabilities and unique consistent beliefs in the source

Before that decision there is only the private prior draw. Its history law
therefore does not depend on any source strategy. Consistency consequently
forces the receiver posterior to be the prior.
-/

noncomputable section

namespace GameTheory.Protocol.DisclosureEnforcement

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Filter
open GameTheory.Protocol.ExecutionProtocol

variable {Secret Decision : Type} [Nonempty Decision]
variable (prior : FinDist Secret) (full : ∀ secret, secret ∈ prior.support)

theorem source_reach_receiver
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature)
    (secret : Secret) :
    (model prior false).historyReachProbability profile
      (receiverHistory prior full false secret false) = prior.prob secret := by
  classical
  change ((model prior false).runBehavioralFrom profile 2 (arena prior false).initHistory).prob
    (receiverHistory prior full false secret false) = _
  rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
    (model prior false) (single prior false),
    ← FinDist.prob_map_of_injective History.state (state_injective prior full false), run_states]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply,
    FinDist.pure_bind, initHistory, kernel, FinDist.bind_map, Bool.false_and,
    FinDist.map_const]
  change (prior.map (fun secret => State.receiver (Decision := Decision) secret false)).prob
    (.receiver secret false) = _
  exact FinDist.prob_map_of_injective _ (fun _ _ same => (State.receiver.inj same).1) _ _

variable [Finite Decision]

theorem source_mass_receiver
    (profile : Profile (model (Decision := Decision) prior false).behavioralSignature) :
    (model prior false).informationMass profile true (receiverSilentSite prior full false) = 1 := by
  classical
  let : Fintype Secret := Fintype.ofEquiv
    ((model (Decision := Decision) prior false).InformationHistory true
      (receiverSilentSite prior full false).1) (silentHistories prior full false).symm
  unfold InformationModel.informationMass
  rw [← (silentHistories (Decision := Decision) prior full false).sum_comp]
  change (∑ secret, (model prior false).historyReachProbability profile
    (receiverHistory prior full false secret false)) = _
  simp only [source_reach_receiver, FinDist.sum_prob]

theorem source_consistent_belief
    (assessment : (model (Decision := Decision) prior false).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent (antichain prior false)) :
    assessment.belief true (receiverSilentSite prior full false) =
      prior.map (silentHistory prior full false) := by
  classical
  obtain ⟨sequence, approximates, converges⟩ := consistent
  apply FinDist.ext_of_prob
  intro history
  obtain ⟨secret, same⟩ := history_at_silent prior full false history
  have historyEq : history = silentHistory prior full false secret := Subtype.ext same
  subst history
  have each (n : Nat) :
      ((sequence n).belief true (receiverSilentSite prior full false)).prob
        (silentHistory prior full false secret) = prior.prob secret := by
    rw [(approximates n).2 true (receiverSilentSite prior full false) (by
      rw [source_mass_receiver prior full]
      norm_num)]
    change (model prior false).historyReachProbability (sequence n).strategy
      (receiverHistory prior full false secret false) /
        (model prior false).informationMass (sequence n).strategy true
          (receiverSilentSite prior full false) = _
    rw [source_reach_receiver, source_mass_receiver, div_one]
  rw [FinDist.prob_map_of_injective _ (silentHistory_injective prior full false)]
  have limit := converges.2 true (receiverSilentSite prior full false)
    (silentHistory prior full false secret)
  simp_rw [each] at limit
  exact tendsto_nhds_unique limit tendsto_const_nhds

end GameTheory.Protocol.DisclosureEnforcement
