/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Protocol.SingleMover
import GameTheoryExtensions.Protocol.Continuation

/-! # Behavioral subgame perfection in bounded single-mover protocols

Subgame roots are the canonical information-set-closed histories. Optimality
quantifies over whole behavioral replacements, using the existing randomized
runner. A certified horizon supplies evaluation fuel; increasing that bound
does not change the predicate or restart an operational deadline.
-/

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua up uq uk us' ua' up' uq' uk' uv

variable {ι : Type uι} [DecidableEq ι]

namespace ExecutionProtocol

variable {E : ExecutionProtocol.{uι, us, ua} ι}

omit [DecidableEq ι] in
theorem runRandomizedFor_eq_of_bound {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (chooser : E.RandomizedChooser) (history : E.History) (fuel : ℕ) (enough : bound ≤ fuel) :
    E.runRandomizedFor chooser fuel history = E.runRandomizedFor chooser bound history := by
  obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le enough
  rw [E.runRandomizedFor_add]
  calc
    _ = (E.runRandomizedFor chooser bound history).bind FinDist.pure := by
      apply FinDist.bind_congr
      intro final reached
      apply E.runRandomizedFor_of_terminal
      rcases E.runRandomizedFor_terminal_or_length _ _ _ _ reached with stopped | consumed
      · exact stopped
      · exact bounded final.state final.trace (by omega)
    _ = _ := FinDist.bind_pure _

end ExecutionProtocol

namespace InformationModel

variable {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)
  (single : ∀ (state : E.State) {first second : ι},
    E.active state first → E.active state second → first = second)

@[reducible] def toBehavioralContinuationGameForm (fuel : ℕ) (history : E.History) :
    GameForm ι where
  sig := M.behavioralSignature
  play profile := M.runSingleMoverBehavioralFrom single profile fuel history

/-- Nash optimality in every proper continuation game, including off-path
roots. The horizon must bound every legal history, not just prescribed play. -/
def IsBehavioralSubgamePerfect {bound : ℕ} (_bounded : E.BoundedHorizon bound)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) : Prop :=
  ∀ history, M.IsSubgameRoot history →
    IsNash (M.toBehavioralContinuationGameForm single bound history) (euPreference utility) profile

theorem isBehavioralSubgamePerfect_iff {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) :
    M.IsBehavioralSubgamePerfect single bounded profile utility ↔
      ∀ history, M.IsSubgameRoot history → ∀ who (alternative : M.BehavioralPolicy who),
        (M.runSingleMoverBehavioralFrom single (Profile.update profile who alternative)
          bound history).expect (utility · who) ≤
        (M.runSingleMoverBehavioralFrom single profile bound history).expect (utility · who) := by
  simp only [IsBehavioralSubgamePerfect, isNash_iff]
  rfl

/-- The certified evaluation horizon is not a semantic parameter. -/
theorem isBehavioralSubgamePerfect_bound_iff {first second : ℕ}
    (firstBound : E.BoundedHorizon first) (secondBound : E.BoundedHorizon second)
    (profile : Profile M.behavioralSignature) (utility : E.History → ι → ℝ) :
    M.IsBehavioralSubgamePerfect single firstBound profile utility ↔
      M.IsBehavioralSubgamePerfect single secondBound profile utility := by
  have law (policies : Profile M.behavioralSignature) (history : E.History) :
      M.runSingleMoverBehavioralFrom single policies first history =
        M.runSingleMoverBehavioralFrom single policies second history := by
    unfold runSingleMoverBehavioralFrom
    exact (ExecutionProtocol.runRandomizedFor_eq_of_bound firstBound _ history
      (max first second) (Nat.le_max_left _ _)).symm.trans
        (ExecutionProtocol.runRandomizedFor_eq_of_bound secondBound _ history
          (max first second) (Nat.le_max_right _ _))
  simp only [isBehavioralSubgamePerfect_iff, law]

/-- Behavioral optimality of a point-mass profile includes all pure deviations.
The converse requires a separate behavioral-deviation argument. -/
theorem isSubgamePerfect_of_behavioral {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (certificate : E.WellFoundedPlay) (profile : Profile M.strategicSignature)
    (utility : E.History → ι → ℝ)
    (perfect : M.IsBehavioralSubgamePerfect single bounded
      (Profile.map (target := M.behavioralSignature)
        (fun who (policy : M.Policy who) => policy.toBehavioral) profile) utility) :
    M.IsSubgamePerfect certificate profile utility := by
  rw [M.isSubgamePerfect_iff_isNash_continuation certificate bounded]
  rw [M.isBehavioralSubgamePerfect_iff single bounded] at perfect
  intro history proper
  rw [isNash_iff]
  intro who alternative
  have bound := perfect history proper who alternative.toBehavioral
  rw [← Profile.map_update] at bound
  change (M.runSingleMoverBehavioralFrom single
      (fun player => (Profile.update profile who alternative player).toBehavioral)
      _ history).expect (utility · who) ≤
    (M.runSingleMoverBehavioralFrom single (fun player => (profile player).toBehavioral)
      _ history).expect (utility · who) at bound
  rw [M.runSingleMoverBehavioralFrom_toBehavioral,
    M.runSingleMoverBehavioralFrom_toBehavioral] at bound
  exact bound

variable {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)
  (targetSingle : ∀ (state : T.State) {first second : ι},
    T.active state first → T.active state second → first = second)

/-- A target continuation may be a lottery over proper source continuations.
The root lottery is fixed before the deviator and its replacement are chosen.
Each branch uses the original source opponents and a whole information-local
replacement; branch-specific replacements do not receive future chance draws.

This accommodates unresolved inclusion of already binding candidates. It does
not assert that any particular scheduler supplies the required laws. -/
theorem isBehavioralSubgamePerfect_of_root_mixture_laws
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.BehavioralPolicy who → N.BehavioralPolicy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation) (profile : Profile M.behavioralSignature)
    (coverage : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∃ roots : FinDist {root : E.History // M.IsSubgameRoot root},
        (N.runSingleMoverBehavioralFrom targetSingle
          (Profile.map (target := N.behavioralSignature) compile profile)
          targetBound targetRoot).map targetObserve =
          roots.bind (fun root =>
            (M.runSingleMoverBehavioralFrom single profile sourceBound root.val).map
              sourceObserve) ∧
        ∀ who (alternative : N.BehavioralPolicy who),
          ∃ replacements : {root : E.History // M.IsSubgameRoot root} →
              FinDist (M.BehavioralPolicy who),
          (N.runSingleMoverBehavioralFrom targetSingle (Profile.update
            (Profile.map (target := N.behavioralSignature) compile profile) who alternative)
            targetBound targetRoot).map targetObserve =
          roots.bind fun root => (replacements root).bind fun replacement =>
            (M.runSingleMoverBehavioralFrom single (Profile.update profile who replacement)
              sourceBound root.val).map sourceObserve)
    (utility : Observation → ι → ℝ)
    (perfect : M.IsBehavioralSubgamePerfect single sourceBounded profile
      (fun history who => utility (sourceObserve history) who)) :
    N.IsBehavioralSubgamePerfect targetSingle targetBounded (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who) := by
  rw [M.isBehavioralSubgamePerfect_iff single sourceBounded] at perfect
  rw [N.isBehavioralSubgamePerfect_iff targetSingle targetBounded]
  intro targetRoot proper who alternative
  obtain ⟨roots, honest, deviations⟩ := coverage targetRoot proper
  obtain ⟨replacements, deviated⟩ := deviations who alternative
  have honestValue := congrArg (fun law => law.expect (utility · who)) honest
  have deviatedValue := congrArg (fun law => law.expect (utility · who)) deviated
  simp only [FinDist.expect_map, FinDist.expect_bind] at honestValue deviatedValue
  rw [deviatedValue, honestValue]
  apply FinDist.expect_mono
  intro root _
  apply FinDist.expect_le_of_forall
  intro replacement _
  exact perfect root.val root.property who replacement

/-- One compiler preserves behavioral SPE when every proper target root has
a proper source match and covers all target deviations there. Root matching
precedes selection of the deviator and its alternative policy. -/
theorem isBehavioralSubgamePerfect_of_continuation_laws
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.BehavioralPolicy who → N.BehavioralPolicy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation) (profile : Profile M.behavioralSignature)
    (coverage : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∃ sourceRoot, M.IsSubgameRoot sourceRoot ∧
        (N.runSingleMoverBehavioralFrom targetSingle
          (Profile.map (target := N.behavioralSignature) compile profile)
          targetBound targetRoot).map targetObserve =
          (M.runSingleMoverBehavioralFrom single profile sourceBound sourceRoot).map sourceObserve ∧
        ∀ who (alternative : N.BehavioralPolicy who),
          ∃ mixture : FinDist (M.BehavioralPolicy who),
          (N.runSingleMoverBehavioralFrom targetSingle (Profile.update
            (Profile.map (target := N.behavioralSignature) compile profile) who alternative)
            targetBound targetRoot).map targetObserve =
          mixture.bind fun replacement =>
            (M.runSingleMoverBehavioralFrom single (Profile.update profile who replacement)
              sourceBound sourceRoot).map sourceObserve)
    (utility : Observation → ι → ℝ)
    (perfect : M.IsBehavioralSubgamePerfect single sourceBounded profile
      (fun history who => utility (sourceObserve history) who)) :
    N.IsBehavioralSubgamePerfect targetSingle targetBounded (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who) := by
  apply M.isBehavioralSubgamePerfect_of_root_mixture_laws single N targetSingle
    sourceBounded targetBounded compile sourceObserve targetObserve profile ?_ utility perfect
  intro targetRoot proper
  obtain ⟨sourceRoot, sourceProper, honest, deviations⟩ := coverage targetRoot proper
  refine ⟨FinDist.pure ⟨sourceRoot, sourceProper⟩, ?_, ?_⟩
  · simpa only [FinDist.pure_bind] using honest
  · intro who alternative
    obtain ⟨mixture, deviated⟩ := deviations who alternative
    exact ⟨fun _ => mixture, by simpa only [FinDist.pure_bind] using deviated⟩

/-- Reflection covers source roots. Agreement for every source profile at a
matching target root realizes each compiled source deviation there. -/
theorem isBehavioralSubgamePerfect_of_compiled_of_continuation_laws
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.BehavioralPolicy who → N.BehavioralPolicy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation)
    (coverage : ∀ sourceRoot, M.IsSubgameRoot sourceRoot →
      ∃ targetRoot, N.IsSubgameRoot targetRoot ∧
        ∀ profile : Profile M.behavioralSignature,
          (N.runSingleMoverBehavioralFrom targetSingle
            (Profile.map (target := N.behavioralSignature) compile profile)
            targetBound targetRoot).map targetObserve =
          (M.runSingleMoverBehavioralFrom single profile sourceBound sourceRoot).map sourceObserve)
    (profile : Profile M.behavioralSignature) (utility : Observation → ι → ℝ)
    (perfect : N.IsBehavioralSubgamePerfect targetSingle targetBounded (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who)) :
    M.IsBehavioralSubgamePerfect single sourceBounded profile
      (fun history who => utility (sourceObserve history) who) := by
  rw [N.isBehavioralSubgamePerfect_iff targetSingle targetBounded] at perfect
  rw [M.isBehavioralSubgamePerfect_iff single sourceBounded]
  intro sourceRoot proper who alternative
  obtain ⟨targetRoot, targetProper, laws⟩ := coverage sourceRoot proper
  have honest := congrArg (fun law => law.expect (utility · who)) (laws profile)
  have deviated := congrArg (fun law => law.expect (utility · who))
    (laws (Profile.update profile who alternative))
  simp only [FinDist.expect_map] at honest deviated
  have optimal := perfect targetRoot targetProper who (compile who alternative)
  rw [← Profile.map_update, deviated, honest] at optimal
  exact optimal

end InformationModel
end GameTheory.Protocol
