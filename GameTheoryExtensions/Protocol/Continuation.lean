/-
# Continuation games and subgame-perfect transfer

The game at a history uses the existing information-local policy carrier and
history runner. A certified horizon makes its expected utility agree with
well-founded continuation value. Thus pure subgame perfection is ordinary
Nash in each proper continuation game.

Transfer fixes one playerwise compiler. Each proper target root must match a
proper source root before a deviation is selected. Initial outcome laws alone
do not supply that coverage. No new equilibrium predicate or evaluator is used.
-/

import GameTheory.Protocol.Strategic
import GameTheory.Protocol.SubgamePerfect
import GameTheory.Core.Equilibrium

noncomputable section

namespace GameTheory.Protocol

open GameTheory.Math.Probability

universe uι us ua up uq uk us' ua' up' uq' uk' uv

variable {ι : Type uι}

namespace ExecutionProtocol

variable {E : ExecutionProtocol.{uι, us, ua} ι}

/-- A bound on total history length also bounds play from any legal prefix.
This is evaluation fuel, not a restart of an operational clock. -/
theorem stopsHistoryWithin_of_bound {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (chooser : E.HistoryChooser) (history : E.History) :
    E.StopsHistoryWithin chooser bound history := by
  intro final reached
  have randomized := reached
  rw [← E.runRandomizedFor_toRandomized] at randomized
  rcases E.runRandomizedFor_terminal_or_length _ _ _ _ randomized with stopped | consumed
  · exact stopped
  · exact bounded final.state final.trace (by omega)

end ExecutionProtocol

namespace InformationModel

variable {E : ExecutionProtocol.{uι, us, ua} ι}
  (M : InformationModel.{uι, us, ua, up, uq, uk} E)

/-- Ordinary strategic form at a retained history. Strategies are whole
information-local policies; the prefix is supplied and is never replayed. -/
@[reducible] def toContinuationGameForm (fuel : ℕ) (history : E.History) : GameForm ι where
  sig := M.strategicSignature
  play profile := M.runFrom profile fuel history

theorem historyBackwardValue_eq_expect_runFrom_of_bound
    (certificate : E.WellFoundedPlay) {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.strategicSignature) (payoff : E.History → ℝ) (history : E.History) :
    E.historyBackwardValue certificate (M.historyChooser profile) payoff history =
      (M.runFrom profile bound history).expect payoff :=
  E.historyBackwardValue_eq_expect_runHistoryFor
    (ExecutionProtocol.stopsHistoryWithin_of_bound bounded _ _)

theorem isSubgamePerfect_iff_isNash_continuation [DecidableEq ι]
    (certificate : E.WellFoundedPlay) {bound : ℕ} (bounded : E.BoundedHorizon bound)
    (profile : Profile M.strategicSignature) (utility : E.History → ι → ℝ) :
    M.IsSubgamePerfect certificate profile utility ↔
      ∀ history, M.IsSubgameRoot history →
        IsNash (M.toContinuationGameForm bound history) (euPreference utility) profile := by
  constructor
  · intro perfect history proper
    rw [isNash_iff]
    intro who alternative
    change (M.runFrom (Profile.update profile who alternative) bound history).expect
        (utility · who) ≤ (M.runFrom profile bound history).expect (utility · who)
    rw [← M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded,
      ← M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded]
    exact perfect history proper who alternative
  · intro optimal history proper who alternative
    rw [M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded,
      M.historyBackwardValue_eq_expect_runFrom_of_bound certificate bounded]
    have bound := optimal history proper
    rw [isNash_iff] at bound
    exact bound who alternative

variable {T : ExecutionProtocol.{uι, us', ua'} ι}
  (N : InformationModel.{uι, us', ua', up', uq', uk'} T)

/-- Exact continuation laws and unilateral mixture coverage preserve pure
SPE. The matching source root is chosen once per proper target root, before
the deviator or replacement. Every target root is covered, including roots
outside the prescribed profile's support. No finiteness of players or action
carriers, nor an equilibrium-existence premise, is required. -/
theorem isSubgamePerfect_of_continuation_laws [DecidableEq ι]
    (sourceTerminates : E.WellFoundedPlay) (targetTerminates : T.WellFoundedPlay)
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.Policy who → N.Policy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation) (profile : Profile M.strategicSignature)
    (coverage : ∀ targetRoot, N.IsSubgameRoot targetRoot →
      ∃ sourceRoot, M.IsSubgameRoot sourceRoot ∧
        (N.runFrom (Profile.map (target := N.strategicSignature) compile profile)
          targetBound targetRoot).map targetObserve =
          (M.runFrom profile sourceBound sourceRoot).map sourceObserve ∧
        ∀ who (alternative : N.Policy who), ∃ mixture : FinDist (M.Policy who),
          (N.runFrom (Profile.update
            (Profile.map (target := N.strategicSignature) compile profile) who alternative)
            targetBound targetRoot).map targetObserve =
          mixture.bind fun replacement =>
            (M.runFrom (Profile.update profile who replacement) sourceBound sourceRoot).map
              sourceObserve)
    (utility : Observation → ι → ℝ)
    (perfect : M.IsSubgamePerfect sourceTerminates profile
      (fun history who => utility (sourceObserve history) who)) :
    N.IsSubgamePerfect targetTerminates (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who) := by
  intro targetRoot proper who alternative
  obtain ⟨sourceRoot, sourceProper, honest, deviations⟩ := coverage targetRoot proper
  obtain ⟨mixture, deviated⟩ := deviations who alternative
  have honestValue := congrArg (fun law => law.expect (utility · who)) honest
  have deviatedValue := congrArg (fun law => law.expect (utility · who)) deviated
  simp only [FinDist.expect_map, FinDist.expect_bind] at honestValue deviatedValue
  rw [N.historyBackwardValue_eq_expect_runFrom_of_bound targetTerminates targetBounded,
    N.historyBackwardValue_eq_expect_runFrom_of_bound targetTerminates targetBounded,
    deviatedValue, honestValue]
  apply FinDist.expect_le_of_forall
  intro replacement _
  have bound := perfect sourceRoot sourceProper who replacement
  rwa [M.historyBackwardValue_eq_expect_runFrom_of_bound sourceTerminates sourceBounded,
    M.historyBackwardValue_eq_expect_runFrom_of_bound sourceTerminates sourceBounded] at bound

/-- Reflection needs coverage of proper source roots. At a matching proper
target root, honest laws for all source profiles also realize every compiled
source replacement. No simulation of arbitrary target deviations is needed
for this direction. -/
theorem isSubgamePerfect_of_compiled_of_continuation_laws [DecidableEq ι]
    (sourceTerminates : E.WellFoundedPlay) (targetTerminates : T.WellFoundedPlay)
    {sourceBound targetBound : ℕ} (sourceBounded : E.BoundedHorizon sourceBound)
    (targetBounded : T.BoundedHorizon targetBound)
    (compile : ∀ who, M.Policy who → N.Policy who)
    {Observation : Type uv} (sourceObserve : E.History → Observation)
    (targetObserve : T.History → Observation)
    (coverage : ∀ sourceRoot, M.IsSubgameRoot sourceRoot →
      ∃ targetRoot, N.IsSubgameRoot targetRoot ∧
        ∀ profile : Profile M.strategicSignature,
          (N.runFrom (Profile.map (target := N.strategicSignature) compile profile)
            targetBound targetRoot).map targetObserve =
          (M.runFrom profile sourceBound sourceRoot).map sourceObserve)
    (profile : Profile M.strategicSignature) (utility : Observation → ι → ℝ)
    (perfect : N.IsSubgamePerfect targetTerminates (Profile.map compile profile)
      (fun history who => utility (targetObserve history) who)) :
    M.IsSubgamePerfect sourceTerminates profile
      (fun history who => utility (sourceObserve history) who) := by
  intro sourceRoot proper who alternative
  obtain ⟨targetRoot, targetProper, laws⟩ := coverage sourceRoot proper
  have honest := congrArg (fun law => law.expect (utility · who)) (laws profile)
  have deviated := congrArg (fun law => law.expect (utility · who))
    (laws (Profile.update profile who alternative))
  simp only [FinDist.expect_map, Profile.map_update] at honest deviated
  have bound := perfect targetRoot targetProper who (compile who alternative)
  rw [N.historyBackwardValue_eq_expect_runFrom_of_bound targetTerminates targetBounded,
    N.historyBackwardValue_eq_expect_runFrom_of_bound targetTerminates targetBounded,
    honest, deviated] at bound
  rwa [M.historyBackwardValue_eq_expect_runFrom_of_bound sourceTerminates sourceBounded,
    M.historyBackwardValue_eq_expect_runFrom_of_bound sourceTerminates sourceBounded]

end InformationModel
end GameTheory.Protocol
