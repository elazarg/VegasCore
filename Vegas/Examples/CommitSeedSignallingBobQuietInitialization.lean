/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingQuietContinuation
import Vegas.Examples.CommitSeedSignallingTimingIncentives
import Vegas.Examples.CommitSeedSignallingBobIncentives

/-! # The initialized law of a whole deviation at Bob's quiet callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob)

/-- The counted runner retains the actual assessed opponents after the quiet
callback, including when that callback was not reached by the assessment. -/
theorem bobQuiet_counted_finish_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (policy : app.Policy)
    (covered : ∀ past view response, response ∈ (policy past view).support →
      response ∈ countedMenu.actions bob past view) :
    app.finish initial horizon scheduler
        (countedMenu.decodeProfile initial horizon scheduler
          (Function.update (countedAssessmentProfile assessment) bob
            (countedMenu.restrictPolicy initial horizon scheduler bob policy)))
        (some ⟨62, some bob, bobFirst ⟨none⟩⟩) =
      app.finish initial horizon scheduler
        (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          bob policy) (some ⟨62, some bob, bobFirst ⟨none⟩⟩) := by
  obtain ⟨trace⟩ := counted_bobQuiet_trace
  let history : countedProtocol.History := ⟨_, trace⟩
  have enough : app.rank horizon history.state ≤ 2 * horizon + 1 := by
    change 125 ≤ 129
    decide
  have source := countedMenu.run_eq_finish initial horizon scheduler
    (Function.update (countedAssessmentProfile assessment) bob
      (countedMenu.restrictPolicy initial horizon scheduler bob policy))
    (2 * horizon + 1) history enough
  have target := countedInRaw.runFrom_restrictPolicy_finish initial horizon scheduler
    (countedAssessmentProfile assessment) assessment.strategy
    (raw_equilibrium_extends_counted assessment equilibrium) bob policy covered
    (2 * horizon + 1) history enough
  exact source.symm.trans target

theorem finish_bobQuiet_of_wait (players : Player → app.Policy)
    (waits : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩) :
    app.finish initial horizon scheduler players (some ⟨62, some bob, bobFirst ⟨none⟩⟩) =
      (app.runRounds scheduler players 62 quietAfterTwo).map app.finished := by
  simp only [ReactiveApplication.finish, ReactiveApplication.resume,
    ReactiveApplication.invoke, bobFirst_recall, waits, PMF.pure_map,
    PMF.pure_bind]
  rfl

/-- A harmless first-response override initializes the same off-path physical
continuation. It does not replace Alice's later strategy or transport beliefs. -/
theorem bobQuiet_fixedLate_context_initialized_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    ((assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).outcome (fixedLateContinuation bob)).map History.state =
      (app.runRounds scheduler
        (countedMenu.decodeProfile initial horizon scheduler
          (quietAliceCountedProfile
            (Function.update (countedAssessmentProfile assessment) bob
              (countedMenu.restrictPolicy initial horizon scheduler bob (fixedLatePolicy bob)))))
        horizon initialExecution).map app.finished := by
  rw [bobQuiet_context_state_law, rawMenu.decodeProfile_update,
    decode_fixedLateContinuation]
  rw [← bobQuiet_counted_finish_law assessment equilibrium (fixedLatePolicy bob)
    (fixedLatePolicy_counted bob)]
  let profile := Function.update (countedAssessmentProfile assessment) bob
    (countedMenu.restrictPolicy initial horizon scheduler bob (fixedLatePolicy bob))
  let players := countedMenu.decodeProfile initial horizon scheduler profile
  have selected : players bob = fixedLatePolicy bob := by
    change app.decodePolicy (countedMenu.embedPolicy initial horizon scheduler bob
      ((Function.update (countedAssessmentProfile assessment) bob
        (countedMenu.restrictPolicy initial horizon scheduler bob (fixedLatePolicy bob))) bob)) = _
    rw [Function.update_self]
    exact countedMenu.decode_restrictPolicy_of_covered initial horizon scheduler bob _
      (fixedLatePolicy_counted bob)
  have waits : players bob [] ((bobFirst ⟨none⟩).observe app bob) = PMF.pure ⟨none⟩ := by
    rw [selected]
    exact fixedLatePolicy_bobQuiet
  change app.finish initial horizon scheduler players _ = _
  rw [finish_bobQuiet_of_wait players waits, decode_quietAliceCountedProfile]
  have initialized := initialized_quietAlice_tail players waits 62
  change app.runRounds scheduler (quietAlicePlayers players) horizon initialExecution =
    app.runRounds scheduler players 62 quietAfterTwo at initialized
  rw [initialized]

theorem bobQuiet_fixedLate_context_initialized_value
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff) :
    (assessment.continuationContext canonicalCertificate bobQuietSite
      (rawPayoff bob)).value (fixedLateContinuation bob) =
      expect (app.runRounds scheduler
        (countedMenu.decodeProfile initial horizon scheduler
          (quietAliceCountedProfile
            (Function.update (countedAssessmentProfile assessment) bob
              (countedMenu.restrictPolicy initial horizon scheduler bob (fixedLatePolicy bob)))))
        horizon initialExecution) (fun final => netPayoff (app.finished final) bob) := by
  rw [bobQuiet_context_value_eq_finish]
  have law := bobQuiet_fixedLate_context_initialized_law assessment equilibrium
  rw [bobQuiet_context_state_law] at law
  rw [law, expect_map]
  rfl

end Vegas.Examples.CommitSeedSignalling
