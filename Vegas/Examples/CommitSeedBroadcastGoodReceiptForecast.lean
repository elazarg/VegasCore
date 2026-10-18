/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastGoodAdmissionRecords
import Vegas.Examples.CommitSeedBroadcastFirstLateForeignRecords

/-! # Foreign good-owner receipt forecasts under arbitrary current preparations -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Changing the focal clock-two preparation cannot change this forecast:
a foreign good owner is admitted exactly when its late slot is still ahead
or one of its retained original responses already transmitted. Earlier good
omissions are retained, rather than assumed to have zero off-path belief. -/
theorem foreign_good_original_receipt_forecast
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (seed : Seeds) (supportedSeed : seed ∈ nativeSeedLaw.support)
    (remaining : Nat) (execution : app.Execution) (focal : Player)
    (trace : (countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some focal, execution⟩))
    (request : execution.application.SeedRequest focal (originalCoordinate focal))
    (clock : execution.application.current.native.clock = 2) (empty : execution.receipts = [])
    (action : app.Action)
    (offered : action ∈ countedMenu.actions focal (execution.recall focal)
      (execution.observe app focal))
    (tail : app.Policy)
    (tailCovered : ∀ past view response, response ∈ (tail past view).support →
      response ∈ countedMenu.actions focal past view)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed)
      (Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
        focal tail) remaining (execution.respond app focal action)).support)
    (resolved : ∀ who, (originalCoordinate who).Resolved final.application)
    (owner : Player) (different : owner ≠ focal) (good : seed.2 owner = true) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final ↔
      (execution.recall owner).length = 1 ∨ ∃ entry ∈ execution.recall owner,
        entry.action.transmission ≠ none := by
  classical
  let players := Function.update
    (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
      focal tail
  let anchor := execution.respond app focal action
  have covered : ∀ who past view response, response ∈ (players who past view).support →
      response ∈ countedMenu.actions who past view := by
    intro who past view response supported
    by_cases same : who = focal
    · subst who
      exact tailCovered past view response (by simpa only [players, Function.update_self]
        using supported)
    · dsimp only [players] at supported
      rw [Function.update_of_ne same] at supported
      exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
        (countedAssessmentProfile assessment who) past view response supported
  obtain ⟨anchorTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
    execution focal action trace offered
  have selected : players owner = countedMenu.decodeProfile initial horizon scheduler
      (countedAssessmentProfile assessment) owner := Function.update_of_ne different _ _
  have retainedWord : anchor.recall owner = execution.recall owner :=
    app.respond_recall_other execution focal owner different action
  obtain ⟨first, _firstView, firstRequest, firstClock, short | long⟩ :=
    original_first_late_foreign_records seed remaining execution focal
      (countedInRaw.trace initial horizon (family seed) trace) request.1.symm clock empty owner
  · have admitted := foreign_singleton_good_original_admission assessment equilibrium seed
      supportedSeed remaining anchor anchorTrace owner (by rw [retainedWord, short]; rfl) good
        players covered selected final reached resolved
    exact ⟨fun _ => Or.inl (by rw [short]; rfl), fun _ => admitted⟩
  · obtain ⟨second, word, _secondView, secondRequest, secondClock⟩ := long
    have actual := good_two_records_run_admission_iff seed remaining anchor anchorTrace owner good
      first second (retainedWord.trans word) firstRequest secondRequest firstClock secondClock
        players covered final reached (resolved owner)
    have forecast : ((execution.recall owner).length = 1 ∨ ∃ entry ∈ execution.recall owner,
        entry.action.transmission ≠ none) ↔
          first.action.transmission ≠ none ∨ second.action.transmission ≠ none := by
      rw [word]
      simp
    exact actual.trans forecast.symm

end Vegas.Examples.CommitSeedBroadcast
