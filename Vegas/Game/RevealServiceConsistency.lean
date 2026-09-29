/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceBayes
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion
import GameTheoryExtensions.Math.Probability.Support

/-! # One consistent assessment for all native replay fibers

Compile a single source consistency sequence, using vanishing positive alias
weights. A common subsequence of the actual native Bayes beliefs yields a
consistent assessment with the canonical compiled strategy. Every ordinary
information site's source-state marginal remains the prescribed source belief,
including sites that have zero probability in the limiting strategy.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (watcher : Player)
  (reveals : setup.program.RevealOnly)
  (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
  (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
  (admission : CommitmentInterface setup.program)
  [Finite (setup.executionProtocol admission).History]
  [∀ who (site : (setup.informationModel admission).InformationSite who),
    Fintype ((setup.informationModel admission).InformationHistory who site.1)]

include reveals observer openable in
/-- Sequential consistency and every retained state posterior are transported
jointly, without choosing a separate limiting sequence for each alias site. -/
theorem exists_compiled_consistent
    (source : (setup.informationModel admission).BehavioralAssessment)
    (consistent : source.IsSequentiallyConsistent (setup.decision_antichain admission)) :
    let extended := bounds.withInitialValues (initialLaw setup)
    let model := information setup leaks extended watcher
    let responses := menu setup leaks extended watcher
    let antichain := (responses.decisionRecall (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).decisionInformationAntichain
    ∃ target : model.BehavioralAssessment,
      target.strategy = compiledProfile setup leaks extended watcher
        (setup.decodeBehavioralProfile admission source.strategy) 0 le_rfl (by norm_num) ∧
      target.IsSequentiallyConsistent antichain ∧
      ∀ (who : Player) (site : model.InformationSite who)
        (reference : Profile model.behavioralSignature)
        (event : (graph setup).EventId) (_owned : (graph setup).actor? event = some who)
        (history : model.InformationHistory who site.1),
        history.1 ∈ (model.runBehavioral reference
          (blockOffset event.val + 2 * event.val + 3)).support →
        history.1.trace.length = blockOffset event.val + 2 * event.val + 3 →
        ∀ sourceSite : (setup.informationModel admission).InformationSite who,
          sourceSite.1 = setup.protocolObserve who
            (prefixReadout setup leaks event.val history.1.state) →
          (target.belief who site).map
              (fun current => prefixReadout setup leaks event.val current.1.state) =
            (source.belief who sourceSite).map (fun current => current.1.state) := by
  classical
  intro extended model responses antichain
  obtain ⟨sourceSequence, approximates, converges⟩ := consistent
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp [weight]; positivity
  have small (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let original (n : Nat) : model.BehavioralAssessment :=
    .ofStrategy (compiledProfile setup leaks extended watcher
      (setup.decodeBehavioralProfile admission (sourceSequence n).strategy)
      (weight n) (positive n).le (small n))
  have mixed (n : Nat) : (original n).IsFullyMixed :=
    compiledProfile_fullyMixed setup leaks bounds watcher reveals observer openable admission
      (sourceSequence n) (approximates n).1 (weight n) (positive n).le (small n) (positive n)
  let sequence (n : Nat) := InformationModel.bayesAssessment _ (original n).strategy
      (mixed n) antichain
  let compiled := compiledProfile setup leaks extended watcher
    (setup.decodeBehavioralProfile admission source.strategy) 0 le_rfl (by norm_num)
  have strategies (who : Player) (site : model.InformationSite who) :
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1)
        (compiled who site.1) :=
    compiledProfile_converges setup leaks bounds watcher reveals observer openable admission
      (fun n => (sourceSequence n).strategy) source.strategy converges.strategy weight
      (fun n => (positive n).le) small vanishes who site
  obtain ⟨target, profile, index, increasing, targetConverges, targetConsistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence antichain
      compiled sequence (fun n => (original n).bayes_isFullyMixed (mixed n) antichain)
      (fun n => InformationModel.bayesAssessment_isBayesConsistent _ (original n).strategy
          (mixed n) antichain) strategies
  refine ⟨target, profile, targetConsistent, ?_⟩
  intro who site reference event owned history supported length sourceSite sourceView
  have law (n : Nat) :
      ((sequence n).belief who site).map
          (fun current => prefixReadout setup leaks event.val current.1.state) =
        ((sourceSequence n).belief who sourceSite).map (fun current => current.1.state) := by
    have result := owner_bayes_state setup leaks bounds watcher reveals observer openable admission
      (sourceSequence n) (approximates n).1 (weight n) (positive n).le (small n) (positive n)
      who site reference event owned history supported length sourceSite sourceView
    have belief : (InformationModel.bayesAssessment _ (sourceSequence n).strategy (approximates n).1
        (setup.decision_antichain admission)).belief who sourceSite =
          (sourceSequence n).belief who sourceSite := by
      apply pmf_ext_toReal
      intro current
      rw [InformationModel.bayesAssessment,
        (setup.informationModel admission).bayesBelief_apply]
      exact ((approximates n).2 who sourceSite
        ((approximates n).1.informationMass_pos who sourceSite) current).symm
    rw [belief] at result
    exact result
  have sourceLimit := ((converges.belief who sourceSite).map
    (fun current => current.1.state)).subsequence increasing
  have nativeLimit := (targetConverges.belief who site).map
    (fun current => prefixReadout setup leaks event.val current.1.state)
  have sameSequence : (fun n => ((sequence (index n)).belief who site).map
      (fun current => prefixReadout setup leaks event.val current.1.state)) =
      (fun n => ((sourceSequence (index n)).belief who sourceSite).map
        (fun current => current.1.state)) := funext fun n => law (index n)
  rw [sameSequence] at nativeLimit
  exact nativeLimit.unique sourceLimit

end Vegas
