/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterBayes
import Vegas.Game.RevealServiceRosterConvergence
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # A common consistent assessment for every roster information site

The same source consistency sequence and timing perturbation is used at all
sites. One common subsequence preserves every owner's source-state posterior,
including early-opening histories of zero limiting probability. Sequential
rationality remains a separate continuation-value obligation.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem exists_roster_consistent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (openable : ∀ initial ∈ setup.initialLaw.support, initial.BindingsOpenable)
    (admission : CommitmentInterface setup.program)
    [∀ who (site : (setup.informationModel admission).InformationSite who),
      Fintype ((setup.informationModel admission).InformationHistory who site.1)]
    (source : (setup.informationModel admission).BehavioralAssessment)
    (consistent : source.IsSequentiallyConsistent (setup.decision_antichain admission))
    (timing : Nat → ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (timingFull : ∀ n event who owned, (timing n event who owned).FullSupport)
    (timingConverges : ∀ event who owned, ∃ last : Fin ((rosters event).count who),
      last.val + 1 = (rosters event).count who ∧
      FinDistConvergesPointwise (fun n => timing n event who owned) (FinDist.pure last)) :
    let menu := rosterMenu setup leaks (bounds.withInitialValues (initialLaw setup)) rosters
    let scheduler := rosterScheduler setup leaks rosters network
    let horizon := (rosterPlan setup rosters).length
    let model := menu.information (initialLaw setup) horizon scheduler
    let antichain := menu.decisionInformationAntichain (initialLaw setup) horizon scheduler
    ∃ target : model.BehavioralAssessment,
      target.strategy = rosterCompiledProfile setup leaks bounds rosters network
        (setup.decodeBehavioralProfile admission source.strategy) ∧
      target.IsSequentiallyConsistent antichain ∧
      ∀ (event : (graph setup).EventId) (owner : Player)
        (_owned : (graph setup).actor? event = some owner) (visits : List Player) (count : Nat),
        (rosterPlan setup rosters)[count]? = some (.player owner) →
        (rosterPlan setup rosters).take count =
          rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
            visits.map ServiceInstruction.player →
        ∀ (site : model.InformationSite owner) (history : model.InformationHistory owner site.1)
          (control : (application setup leaks).Control),
          history.1.state = some control →
          control.execution.environmentRecall.length = count + 1 →
          ∀ sourceSite : (setup.informationModel admission).InformationSite owner,
            sourceSite.1 = setup.protocolObserve owner
              (sourcePrefix? setup event.val control.execution.application.config) →
            setup.decisionDepth owner sourceSite.1 = event.val + 1 →
            (target.stateBelief owner site).map (fun state => state.bind fun current =>
              sourcePrefix? setup event.val current.execution.application.config) =
                source.stateBelief owner sourceSite := by
  classical
  intro menu scheduler horizon model antichain
  obtain ⟨sourceSequence, approximates, converges⟩ := consistent
  let original (n : Nat) : model.BehavioralAssessment := .ofStrategy
    (rosterPerturbedProfile setup leaks bounds rosters network admission
      (sourceSequence n) (timing n))
  have mixed (n : Nat) : (original n).IsFullyMixed :=
    rosterPerturbedProfile_fullyMixed setup leaks bounds rosters network reveals openable admission
      (sourceSequence n) (approximates n).1 (timing n) (timingFull n)
  let sequence (n : Nat) := (original n).bayes (mixed n) antichain
  let compiled := rosterCompiledProfile setup leaks bounds rosters network
    (setup.decodeBehavioralProfile admission source.strategy)
  have strategies (who : Player) (site : model.InformationSite who) :
      FinDistConvergesPointwise (fun n => (sequence n).strategy who site.1)
        (compiled who site.1) :=
    rosterPerturbedProfile_converges setup leaks bounds rosters network reveals openable admission
      sourceSequence (fun n => (approximates n).1) source.strategy converges.strategy
      timing timingFull timingConverges who site
  obtain ⟨target, profile, index, increasing, targetConverges, targetConsistent⟩ :=
    InformationModel.BehavioralAssessment.exists_consistent_completion_subsequence antichain
      compiled sequence (fun n => (original n).bayes_isFullyMixed (mixed n) antichain)
      (fun n => (original n).bayes_isBayesConsistent (mixed n) antichain) strategies
  refine ⟨target, profile, targetConsistent, ?_⟩
  intro event owner owned visits count selected before site history control current position
    sourceSite sourceView sourceDepth
  let read := fun state : (application setup leaks).ProtocolState => state.bind fun execution =>
    sourcePrefix? setup event.val execution.execution.application.config
  have law (n : Nat) :
      ((sequence n).stateBelief owner site).map read =
        (sourceSequence n).stateBelief owner sourceSite :=
    roster_owner_bayes_source_state setup leaks bounds rosters network reveals openable admission
      (sourceSequence n) (approximates n).1 (approximates n).2 (timing n) (timingFull n)
      event owner owned visits count selected before site history control current position
      sourceSite sourceView sourceDepth
  have sourceLimit := ((converges.belief owner sourceSite).map
    (fun current => current.1.state)).subsequence increasing
  have nativeLimit := (targetConverges.belief owner site).map
    (fun current => read current.1.state)
  have sameSequence :
      (fun n => ((sequence (index n)).belief owner site).map
        (fun current => read current.1.state)) =
      (fun n => ((sourceSequence (index n)).belief owner sourceSite).map
        (fun current => current.1.state)) := by
    funext n
    simpa only [InformationModel.BehavioralAssessment.stateBelief, FinDist.map_comp,
      Function.comp_def] using law (index n)
  rw [sameSequence] at nativeLimit
  simpa only [InformationModel.BehavioralAssessment.stateBelief, FinDist.map_comp,
    Function.comp_def] using nativeLimit.unique sourceLimit

end Vegas.SourceProgram.RevealService
