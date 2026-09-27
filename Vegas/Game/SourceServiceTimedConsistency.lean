/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedMixing
import Vegas.Game.SourceInformation
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # One consistent limit for full-source timed play

A single completed original source sequence drives all native timing
perturbations. Each native profile is fully mixed and uses its actual Bayes
beliefs. Compactness selects one common subsequence of strategies and beliefs
at every native site. Rationality is supplied separately by the concrete
source/native conditional continuation comparisons.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual timed compiler supplies a common fully mixed Bayes sequence and
one consistent native assessment limit, from any original consistent source
assessment. The timing sequence may be chosen independently of that assessment.
No equilibrium or continuity of normalized intermediate source profiles is
assumed. -/
theorem exists_sourceService_timed_consistent
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : ∀ event owner payload,
      (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
    (network : (runtime setup).NetworkPolicy leaks)
    (source : (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralAssessment)
    [∀ who (site : (setup.informationModel
      (CommitmentInterface.values setup.program)).InformationSite who),
      Fintype ((setup.informationModel
        (CommitmentInterface.values setup.program)).InformationHistory who site.1)]
    (consistent : source.IsSequentiallyConsistent
      (setup.decision_antichain (CommitmentInterface.values setup.program)))
    (timing : Nat → ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (timingFull : ∀ n event who owned, (timing n event who owned).FullSupport) :
    let model := (sourceServiceMenu setup leaks bounds rosters).information
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
    let antichain := (sourceServiceMenu setup leaks bounds rosters).decisionInformationAntichain
      (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
    ∃ sourceSequence : Nat → (setup.informationModel
        (CommitmentInterface.values setup.program)).BehavioralAssessment,
      (∀ n who info, ((sourceSequence n).strategy who info).FullSupport) ∧
      (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent
        (setup.informationModel (CommitmentInterface.values setup.program))
        (sourceSequence n) (setup.decision_antichain (CommitmentInterface.values setup.program))) ∧
      InformationModel.BehavioralAssessmentConvergesPointwise sourceSequence source ∧
      ∃ sequence : Nat → model.BehavioralAssessment,
        (∀ n, (sequence n).strategy =
          sourceServiceTimedProfile setup leaks bounds rosters network (timing n)
            (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
              (sourceSequence n).strategy)) ∧
        (∀ n, (sequence n).IsFullyMixed) ∧
        (∀ n, InformationModel.BehavioralAssessment.IsBayesConsistent model
          (sequence n) antichain) ∧
        ∃ target : model.BehavioralAssessment, ∃ index : Nat → Nat,
          StrictMono index ∧
          InformationModel.BehavioralAssessmentConvergesPointwise
            (fun n => sequence (index n)) target ∧
          target.IsSequentiallyConsistent antichain := by
  classical
  intro model antichain
  obtain ⟨sourceSequence, sourceFull, sourceBayes, sourceConverges, _⟩ :=
    sourceService_consistent_supported_sequence setup bounds values source
      (setup.decision_antichain (CommitmentInterface.values setup.program)) consistent
  let native (n : Nat) : model.BehavioralAssessment := .ofStrategy
    (sourceServiceTimedProfile setup leaks bounds rosters network (timing n)
      (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
        (sourceSequence n).strategy))
  have mixed (n : Nat) : (native n).IsFullyMixed :=
    sourceServiceTimedProfile_fullyMixed setup leaks bounds values initialValues capacity rosters
      opportunities network (timing n) (timingFull n) (sourceSequence n).strategy (sourceFull n)
  let sequence (n : Nat) := (native n).bayes (mixed n) antichain
  have sequenceMixed (n : Nat) : (sequence n).IsFullyMixed :=
    (native n).bayes_isFullyMixed (mixed n) antichain
  have sequenceBayes (n : Nat) : InformationModel.BehavioralAssessment.IsBayesConsistent
      model (sequence n) antichain :=
    (native n).bayes_isBayesConsistent (mixed n) antichain
  obtain ⟨target, index, increasing, converges, targetConsistent⟩ :=
    InformationModel.BehavioralAssessment.exists_sequentiallyConsistent_subsequence
      antichain sequence sequenceMixed sequenceBayes
  exact ⟨sourceSequence, sourceFull, sourceBayes, sourceConverges, sequence, fun _ => rfl,
    sequenceMixed, sequenceBayes, target, index, increasing, converges, targetConsistent⟩

end Vegas.SourceProgram.RevealService
