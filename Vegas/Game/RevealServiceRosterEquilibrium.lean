/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterOwnerIncentives
import Vegas.Game.RevealServiceRosterOwnerSite
import Vegas.Game.RevealServiceRosterHarmlessComparison
import Vegas.Game.RevealServiceRosterInitialized
import Vegas.Game.RevealServiceRosterConvergence
import Vegas.Game.RevealServiceRosterTiming
import GameTheoryExtensions.Analysis.Protocol.LocalSimulationLimit

/-! # Source sequential equilibrium under arbitrary finite revelation rosters

Every event owner must have a response opportunity. All players may have further
activations and passive observations. The fixed compiled profile waits until
the final owner opportunity and stops after any earlier opening. One common
fully mixed sequence establishes standard sequential equilibrium at every
native information set, with the original joint terminal source-state law.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem roster_source_sequential_equilibrium_preserved
    (setup : Setup (Player := Player) (L := L)) [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport]
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (coverage : ActorOpportunities setup rosters)
    (network : (runtime setup).NetworkPolicy leaks) [network.FiniteSupport]
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (source : (setup.informationModel admission).BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor (setup.decision_antichain admission)
      (fun who site => source.continuationContext site
        (fun final => (setup.protocolReadout final.state).elim 0 (fun state => utility state who))
        (instructionCount setup.program + 1))) :
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let horizon := (rosterPlan setup rosters).length
    let model := menu.information (initialLaw setup) horizon scheduler
    let antichain := menu.decisionInformationAntichain (initialLaw setup) horizon scheduler
    ∃ target : model.BehavioralAssessment,
      target.strategy = rosterCompiledProfile setup leaks bounds rosters network
        (setup.decodeBehavioralProfile admission source.strategy) ∧
      target.IsSequentialEquilibriumFor antichain (fun who site =>
        target.continuationContext site
          (fun final => (sourceReadout setup leaks final.state).elim 0
            (fun state => utility state who))
          (2 * horizon + 1)) ∧
      (model.runBehavioral target.strategy (2 * horizon + 1)).map
          (fun final => sourceReadout setup leaks final.state) =
        ((setup.informationModel admission).runBehavioral source.strategy
          (instructionCount setup.program + 1)).map
            (fun final => setup.protocolReadout final.state) := by
  classical
  intro menu scheduler horizon model antichain
  let _ := setup.reveal_finite_history reveals admission
  obtain ⟨sourceSequence, approximates, converges⟩ := equilibrium.2
  obtain ⟨range, rangeNonnegative, sourceRange⟩ :=
    setup.reveal_boolean_value_range admission reveals utility
  let weight (n : Nat) : ℝ := 1 / ((n : ℝ) + 1)
  have positive (n : Nat) : 0 < weight n := by dsimp only [weight]; positivity
  have small (n : Nat) : weight n ≤ 1 := by
    apply (div_le_one (by positivity : 0 < (n : ℝ) + 1)).mpr
    have := Nat.cast_nonneg (α := ℝ) n
    linarith
  have vanishes : Tendsto weight atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  let timing (n : Nat) := rosterTiming setup rosters coverage
    (weight n) (positive n).le (small n)
  have timingFull (n : Nat) (event : (graph setup).EventId) (who : Player)
      (owned : (graph setup).actor? event = some who) : FullSupport (timing n event who owned) :=
    rosterTiming_fullSupport setup rosters coverage (weight n) (positive n).le (small n)
      (positive n) event who owned
  have timingConverges (event : (graph setup).EventId) (who : Player)
      (owned : (graph setup).actor? event = some who) :
      ∃ last : Fin ((rosters event).count who), last.val + 1 = (rosters event).count who ∧
        PMFConvergesPointwise (fun n => timing n event who owned) (PMF.pure last) :=
    ⟨rosterLastSlot setup rosters coverage event who owned,
      rosterLastSlot_final setup rosters coverage event who owned,
      rosterTiming_converges setup rosters coverage (fun n => (positive n).le) small
        vanishes event who owned⟩
  let original (n : Nat) : model.BehavioralAssessment := .ofStrategy
    (rosterPerturbedProfile setup leaks bounds rosters network admission
      (sourceSequence n) (timing n))
  have mixed (n : Nat) : (original n).IsFullyMixed :=
    rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable admission
      (sourceSequence n) (approximates n).1 (timing n) (timingFull n)
  let sequence (n : Nat) := InformationModel.bayesAssessment _ (original n).strategy
      (mixed n) antichain
  let compiled := rosterCompiledProfile setup leaks bounds rosters network
    (setup.decodeBehavioralProfile admission source.strategy)
  have strategies (who : Player) (site : model.InformationSite who) :
      PMFConvergesPointwise (fun n => (sequence n).strategy who site.1)
        (compiled who site.1) :=
    rosterPerturbedProfile_converges setup leaks bounds rosters network reveals openable admission
      sourceSequence (fun n => (approximates n).1) source.strategy converges.strategy
      timing timingFull timingConverges who site
  obtain ⟨target, strategy, index, increasing, targetConverges, consistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence antichain
      compiled sequence (fun n => mixed n)
      (fun n => InformationModel.bayesAssessment_isBayesConsistent _ (original n).strategy
          (mixed n) antichain) strategies
  let sourceObserve := fun history : (setup.executionProtocol admission).History =>
    setup.protocolReadout history.state
  let targetObserve := fun history : (menu.protocol (initialLaw setup) horizon scheduler).History =>
    sourceReadout setup leaks history.state
  let payoff := fun output : Option (State L setup.program.terminalCtx) =>
    fun who => output.elim 0 (fun state => utility state who)
  have localComparisons (n : Nat) (who : Player) (site : model.InformationSite who)
      (law : PMF (model.Choice who site.1)) :
      let comparison := model.assessmentComparison targetObserve (2 * horizon + 1)
        (sequence n) who (site, ((sequence n).strategy who).withLaw site.1 law)
      expect comparison.alternative (payoff · who) -
          expect comparison.prescribed (payoff · who) ≤ weight n * range ∨
        ∃ mixture : PMF ((setup.informationModel admission).AssessmentDeviation who),
          expect comparison.alternative (payoff · who) -
              expect comparison.prescribed (payoff · who) ≤
            expect mixture (fun deviation =>
              let originalComparison := (setup.informationModel admission).assessmentComparison
                sourceObserve (instructionCount setup.program + 1) (sourceSequence n) who deviation
              expect originalComparison.alternative (payoff · who) -
                expect originalComparison.prescribed (payoff · who)) + weight n * range := by
    intro comparison
    obtain ⟨past, view, observed⟩ : ∃ past view, site.1 = some (past, view) := by
      obtain ⟨history, _, _⟩ := site.2
      have active := InformationModel.InformationSite.active model site history
      have info := (menu.info (initialLaw setup) horizon scheduler who history.1.trace).symm.trans
        history.2
      cases current : history.1.state with
      | none => rw [current] at active; cases active
      | some control =>
          rw [current] at active info
          change control.actor = some who at active
          simp only [ReactiveApplication.observe, active, ↓reduceIte] at info
          exact ⟨control.execution.recall who,
            control.execution.observe (application setup leaks) who, info.symm⟩
    cases fresh : rosterFresh? setup leaks rosters who past view with
    | none =>
        left
        have harmless := roster_harmless_comparison_gain setup leaks bounds rosters network reveals
          openable admission (sourceSequence n) (approximates n).1 (timing n) (timingFull n)
          (sequence n) rfl who site past view observed fresh law (payoff · who)
        change expect comparison.alternative (payoff · who) -
          expect comparison.prescribed (payoff · who) = 0 at harmless
        rw [harmless]
        exact mul_nonneg (positive n).le rangeNonnegative
    | some packet =>
        right
        obtain ⟨event, owned, candidate, raw, sourceSite, grant, opening, packetEq, unopened,
            inside, choiceLaw, posterior⟩ :=
          roster_owner_site setup leaks bounds rosters network reveals openable admission
            (sourceSequence n) (approximates n).1 (approximates n).2 (timing n) (timingFull n)
            who site past view packet observed fresh
        rw [packetEq] at fresh
        obtain ⟨deviation, bound⟩ := roster_owner_comparison_of_posterior setup leaks bounds rosters
          network reveals openable admission (sourceSequence n) (approximates n).1
          (timing n) (timingFull n) (sequence n) rfl who site past view observed event owned grant
          candidate raw opening fresh unopened inside sourceSite choiceLaw posterior law
          (fun state => utility state who) range (weight n) rangeNonnegative
          (rosterTiming_prefix_le setup rosters coverage (weight n) (positive n).le (small n)
            event who owned _ inside)
          (sourceRange (sourceSequence n) who sourceSite
            (fun disclose _ => some (.reveal who 0 disclose)) (fun _ => rfl))
        exact ⟨PMF.pure deviation, by simpa only [expect_pure] using bound⟩
  have result := ContinuationSimulation.sequentialEquilibrium_of_local_comparisons_limit
    sourceObserve targetObserve (instructionCount setup.program + 1) (2 * horizon + 1)
    (menu.bounded (initialLaw setup) horizon scheduler)
    (menu.decisionRecall (initialLaw setup) horizon scheduler)
    (roster_menu_common_depth setup leaks rosters network menu) payoff source sourceSequence
    converges equilibrium.1 sequence
    (fun n => weight n * range) (by simpa only [zero_mul] using vanishes.mul_const range)
    localComparisons (fun n => rosterPerturbedProfile_readout_law setup leaks bounds rosters network
      reveals openable admission (sourceSequence n) (approximates n).1 (timing n) (timingFull n))
    target index increasing targetConverges consistent
  exact ⟨target, strategy, result.1, result.2⟩

end Vegas
