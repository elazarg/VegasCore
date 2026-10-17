/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingIncentives
import Interaction.ReactiveLocalContinuation

/-! # Actual whole continuations at Bob's initial quiet callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

theorem bobQuiet_context_state_law (assessment : rawModel.BehavioralAssessment)
    (alternative : rawModel.BehavioralPolicy bob) :
    ((assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).outcome alternative).map History.state =
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler
            (Profile.update (sig := rawModel.behavioralSignature)
              assessment.strategy bob alternative))
          (some ⟨62, some bob, bobFirst ⟨none⟩⟩) := by
  classical
  change ((assessment.belief bob bobQuietSite).bind fun history =>
    rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature)
        assessment.strategy bob alternative) history.1).map History.state = _
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief bob bobQuietSite).bind (fun _ =>
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler
            (Profile.update (sig := rawModel.behavioralSignature)
              assessment.strategy bob alternative))
          (some ⟨62, some bob, bobFirst ⟨none⟩⟩)) := by
      apply bind_congr_on_support
      intro history _
      rw [raw_terminal_state_law, bobQuiet_information_state]
    _ = _ := PMF.bind_const _ _

theorem bobQuiet_context_value_eq_finish (assessment : rawModel.BehavioralAssessment)
    (alternative : rawModel.BehavioralPolicy bob) :
    (assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).value alternative =
        expect (app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler
            (Profile.update (sig := rawModel.behavioralSignature)
              assessment.strategy bob alternative))
          (some ⟨62, some bob, bobFirst ⟨none⟩⟩))
          (fun state => netPayoff state bob) := by
  classical
  rw [← bobQuiet_context_state_law assessment alternative, expect_map]
  rfl

open Classical in
theorem bobQuiet_history_local_law (assessment : rawModel.BehavioralAssessment)
    (history : rawModel.InformationHistory bob bobQuietSite.1)
    (law : PMF (rawModel.Choice bob bobQuietSite.1)) :
    (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy bob
        ((assessment.strategy bob).withLaw bobQuietSite.1 law)) history.1).map
          History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          (some ⟨62, none, (bobFirst ⟨none⟩).respond app bob response⟩) := by
  classical
  rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    canonicalCertificate (rawMenu.bounded initial horizon scheduler)]
  exact rawMenu.run_local_law_finish_of_information initial horizon scheduler
    assessment.strategy history.1 bob 62 (bobFirst ⟨none⟩)
    (bobQuiet_information_state history) bobQuietSite.1 history.2 law (2 * horizon)
    (by rw [bobQuiet_information_state history]; change 125 ≤ 129; decide)

open Classical in
theorem bobQuiet_context_local_law (assessment : rawModel.BehavioralAssessment)
    (law : PMF (rawModel.Choice bob bobQuietSite.1)) :
    ((assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).outcome
        ((assessment.strategy bob).withLaw bobQuietSite.1 law)).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          (some ⟨62, none, (bobFirst ⟨none⟩).respond app bob response⟩) := by
  classical
  change ((assessment.belief bob bobQuietSite).bind fun history =>
    rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) assessment.strategy bob
        ((assessment.strategy bob).withLaw bobQuietSite.1 law)) history.1).map
          History.state = _
  rw [PMF.map_bind]
  calc
    _ = (assessment.belief bob bobQuietSite).bind (fun _ =>
        (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
          app.finish initial horizon scheduler
            (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
            (some ⟨62, none, (bobFirst ⟨none⟩).respond app bob response⟩)) := by
      apply bind_congr_on_support
      intro history _
      exact bobQuiet_history_local_law assessment history law
    _ = _ := PMF.bind_const _ _

open Classical in
theorem bobQuiet_context_committed_value (assessment : rawModel.BehavioralAssessment)
    (choice : rawModel.Choice bob bobQuietSite.1) (response : app.Action)
    (selected : choice.1 = some response) :
    (assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).value ((assessment.strategy bob).commit bobQuietSite.1 choice) =
        expect (app.finish initial horizon scheduler
          (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          (some ⟨62, none, (bobFirst ⟨none⟩).respond app bob response⟩))
          (fun state => netPayoff state bob) := by
  classical
  have law := bobQuiet_context_local_law assessment (PMF.pure choice)
  simp only [PMF.pure_map, PMF.pure_bind, selected, Option.getD_some] at law
  change ((assessment.continuationContext canonicalCertificate bobQuietSite
    (rawPayoff bob)).outcome
      ((assessment.strategy bob).commit bobQuietSite.1 choice)).map History.state = _ at law
  rw [← law, expect_map]
  rfl

end Vegas.Examples.CommitSeedSignalling
