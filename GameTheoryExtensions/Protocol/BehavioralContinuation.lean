/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.BehavioralContinuation
import GameTheoryExtensions.Math.Probability.Expectation

/-! # Root lotteries of single-mover behavioral subgames

A target continuation may be a lottery over proper source continuations.
Upstream's continuation transfer handles one matched source root; this module
allows the matched root itself to be random.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

universe uι us ua up uq uk us' ua' up' uq' uk' uv

variable {ι : Type uι} [DecidableEq ι]
  {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)
  (single : ∀ (state : E.State) {first second : ι},
    E.active state first → E.active state second → first = second)
  {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)
  (targetSingle : ∀ (state : T.State) {first second : ι},
    T.active state first → T.active state second → first = second)

/-- A target continuation may be a lottery over proper source continuations.
The root lottery is fixed before the deviator and its replacement are chosen.
Each branch uses the original source opponents and a whole information-local
replacement; branch-specific replacements do not receive future chance draws.
As in upstream's transfer, every target deviation must have a finite expected
utility; every finitely supported instance satisfies that premise.

This accommodates unresolved inclusion of already binding candidates. It does
not assert that any particular scheduler supplies the required laws. -/
theorem isSingleMoverBehavioralSubgamePerfect_of_root_mixture_laws
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.BehavioralPolicy who → N.BehavioralPolicy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation) (profile : Profile M.behavioralSignature)
    (coverage : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∃ roots : PMF {root : E.History // M.IsSubgameRoot root},
        (N.runSingleMoverBehavioralFrom targetSingle
          (Profile.map (target := N.behavioralSignature) compile profile)
          targetBound targetRoot).map targetObserve =
          roots.bind (fun root =>
            (M.runSingleMoverBehavioralFrom single profile sourceBound root.val).map
              sourceObserve) ∧
        ∀ who (alternative : N.BehavioralPolicy who),
          ∃ replacements : {root : E.History // M.IsSubgameRoot root} →
              PMF (M.BehavioralPolicy who),
          (N.runSingleMoverBehavioralFrom targetSingle (Profile.update
            (Profile.map (target := N.behavioralSignature) compile profile) who alternative)
            targetBound targetRoot).map targetObserve =
          roots.bind fun root => (replacements root).bind fun replacement =>
            (M.runSingleMoverBehavioralFrom single (Profile.update profile who replacement)
              sourceBound root.val).map sourceObserve)
    (utility : Observation → ι → ℝ)
    (integrable : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∀ who (alternative : N.BehavioralPolicy who), UtilityIntegrable
        (fun history player => utility (targetObserve history) player) who
        (N.runSingleMoverBehavioralFrom targetSingle (Profile.update
          (Profile.map (target := N.behavioralSignature) compile profile) who alternative)
          targetBound targetRoot))
    (perfect : M.IsSingleMoverBehavioralSubgamePerfect single sourceBounded profile
      (fun history who => utility (sourceObserve history) who)) :
    N.IsSingleMoverBehavioralSubgamePerfect targetSingle targetBounded
      (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who) := by
  rw [M.isSingleMoverBehavioralSubgamePerfect_iff single sourceBounded] at perfect
  rw [N.isSingleMoverBehavioralSubgamePerfect_iff targetSingle targetBounded]
  intro targetRoot proper who alternative
  have honestIntegrable := integrable targetRoot proper who
    (Profile.map (target := N.behavioralSignature) compile profile who)
  rw [Profile.update_eq_self] at honestIntegrable
  refine ⟨honestIntegrable, integrable targetRoot proper who alternative, ?_⟩
  obtain ⟨roots, honest, deviations⟩ := coverage targetRoot proper
  obtain ⟨replacements, deviated⟩ := deviations who alternative
  have deviatedIntegrable := integrable targetRoot proper who alternative
  simp only [UtilityIntegrable] at honestIntegrable deviatedIntegrable
  rw [← Function.comp_def (fun observation => utility observation who) targetObserve,
    ← payoffIntegrable_map_iff] at honestIntegrable deviatedIntegrable
  rw [honest] at honestIntegrable
  rw [deviated] at deviatedIntegrable
  simp only [expectedUtility]
  rw [← Function.comp_def (fun observation => utility observation who) targetObserve,
    ← expect_map, ← expect_map, honest, deviated,
    expect_bind_tower _ _ _ honestIntegrable, expect_bind_tower _ _ _ deviatedIntegrable]
  apply expect_mono _ (payoffIntegrable_bind_conditionalExpectation _ _ _ deviatedIntegrable)
    (payoffIntegrable_bind_conditionalExpectation _ _ _ honestIntegrable)
  intro root supported
  have branch := payoffIntegrable_bind_conditional_on_support _ _ _ deviatedIntegrable root
    supported
  rw [expect_bind_tower _ _ _ branch]
  apply expect_le_const _ _ (payoffIntegrable_bind_conditionalExpectation _ _ _ branch)
  intro replacement _
  have optimal := (perfect root.val root.property who replacement).2.2
  simp only [expectedUtility] at optimal
  rw [expect_map, expect_map]
  exact optimal

end GameTheory.Protocol.InformationModel
