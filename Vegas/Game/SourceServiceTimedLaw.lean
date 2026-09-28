/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefixFactorization
import Vegas.Game.SourceServiceLaw
import Vegas.Game.RevealServiceRosterInitialized

/-! # Initialized law of every full-source timing approximant

The actual finite-menu timed compiler preserves the original source profile's
whole typed terminal-state distribution. Private-intention normalization and
all supported timing choices are included in the proof.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every positive shared timing law preserves the original admitted source
profile's initialized typed outcome law in the actual finite native game. -/
theorem sourceServiceTimedProfile_readout_law [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (original : BehavioralProfile setup.program)
    (permitted : ∀ who, (original who).Admitted setup.program
      (CommitmentInterface.values setup.program))
    : (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).runBehavioral
      (sourceServiceTimedProfile setup leaks bounds rosters network timing original)
      (2 * (rosterPlan setup rosters).length + 1)).map
        (fun final => sourceReadout setup leaks final.state) = (setup.run original).map some := by
  classical
  cases isEmpty_or_nonempty Player with
  | inl empty =>
      let := empty
      have profiles : sourceServiceTimedProfile setup leaks bounds rosters network timing original =
          sourceServiceCompiledProfile setup leaks bounds rosters network original := by
        funext who
        exact isEmptyElim who
      rw [profiles]
      exact sourceServiceCompiledProfile_readout_law setup leaks bounds values initialValues
        capacity rosters (fun _ who _ => isEmptyElim who) network original permitted
  | inr inhabited =>
      let := inhabited
      let focal := Classical.choice inhabited
      let normalized := normalizeDisclosureProfile setup.program []
        (Revelations.initial setup.context) original
      let admitted := normalized_sourceService_admitted setup original permitted
      let players := sourceServiceTimedPolicy setup leaks rosters timing normalized
      have physical := roster_restrict_complete_state setup leaks rosters network
        (sourceServiceMenu setup leaks bounds rosters) players
        (sourceServiceTimedPolicy_admissible setup leaks bounds values initialValues capacity
          rosters opportunities network timing full normalized admitted)
      have observed := congrArg (FinDist.map (sourceReadout setup leaks)) physical
      simp only [FinDist.map_comp, Function.comp_def] at observed
      refine observed.trans ?_
      obtain ⟨noise, joint⟩ := sourceServiceTimedProfile_prefix_factorization setup leaks bounds
        values initialValues capacity rosters opportunities timing full network original
        permitted focal (eventCount setup.program) le_rfl
      have projected := congrArg (FinDist.map (fun pair => setup.protocolReadout pair.1)) joint
      simp only [FinDist.map_comp, Function.comp_def, FinDist.map_bind, FinDist.map_const,
        ← FinDist.map_eq_bind] at projected
      have completed : rosterPlanPrefix setup rosters (eventCount setup.program) =
          rosterPlan setup rosters := by
        unfold rosterPlanPrefix rosterPlan
        rw [List.take_of_length_le (by rw [List.length_finRange]; exact le_rfl)]
      simp only [completed, sourceServicePrefix?_terminal_readout] at projected
      have sourceLaw := setup.protocol_runBehavioral_eq (CommitmentInterface.values setup.program)
        normalized admitted
      rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom] at sourceLaw
      have terminal := projected.trans (by
        simpa only [eventCount_eq_instructionCount, InformationModel.runBehavioral] using sourceLaw)
      have same : setup.run normalized = setup.run original := by
        unfold Setup.run
        apply FinDist.bind_congr
        intro initial _
        exact normalizeDisclosureProfile_runFrom setup.program original
          (setup.initialConfig initial)
      rw [same] at terminal
      simpa only [sourceReadout_eq_decode, FinDist.map_bind] using terminal

/-- The timed native approximant and its original finite source strategy
have identical initialized typed readouts. This is the initialized-law premise
used with their common consistent assessment sequence. -/
theorem sourceServiceTimedProfile_protocol_law [Fintype Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
    (initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (rosters : (graph setup).EventId → List Player)
    (opportunities : BindingOpportunities setup rosters)
    (timing : TimingLaw setup rosters)
    (full : ∀ event who owned, (timing event who owned).FullSupport)
    (network : (runtime setup).NetworkPolicy leaks)
    (source : ∀ who, (setup.informationModel
      (CommitmentInterface.values setup.program)).BehavioralPolicy who) :
    (((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).runBehavioral
      (sourceServiceTimedProfile setup leaks bounds rosters network timing
        (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program) source))
      (2 * (rosterPlan setup rosters).length + 1)).map
        (fun final => sourceReadout setup leaks final.state) =
      ((setup.informationModel (CommitmentInterface.values setup.program)).runBehavioral source
        (instructionCount setup.program + 1)).map
          (fun final => setup.protocolReadout final.state) := by
  let admission := CommitmentInterface.values setup.program
  have permitted (who : Player) :
      (setup.decodeBehavioralProfile admission source who).Admitted setup.program admission :=
    ((setup.behavioralPolicyEquiv admission who).symm (source who)).2
  exact (sourceServiceTimedProfile_readout_law setup leaks bounds values initialValues capacity
    rosters opportunities timing full network (setup.decodeBehavioralProfile admission source)
      permitted).trans
    (setup.runBehavioralFrom_readout admission source (instructionCount setup.program + 1)
      (setup.executionProtocol admission).initHistory (Nat.le_refl _)).symm

end Vegas
