/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastPreparationForecast
import Vegas.Examples.CommitSeedBroadcastBadReceiptForecast

/-! # The native foreign receipt mask under a clock-two preparation change -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every actual foreign receipt under a focal good clock-two response is
read from the original seed and the unchanged physical pre-response history. -/
theorem foreign_clock_two_preparation_receipt_forecast
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
    (good : seed.2 focal = true) (action : app.Action)
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
    (owner : Player) (different : owner ≠ focal) :
    PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner final ↔
      originalReceiptForecast seed execution owner := by
  classical
  cases bit : seed.2 owner with
  | true =>
      simpa only [originalReceiptForecast, bit, ite_true] using
        foreign_good_original_receipt_forecast assessment equilibrium seed supportedSeed remaining
          execution focal trace request clock empty action offered tail tailCovered final reached
            resolved owner different bit
  | false =>
      let players := Function.update
        (countedMenu.decodeProfile initial horizon scheduler (countedAssessmentProfile assessment))
          focal tail
      let anchor := execution.respond app focal action
      have covered : ∀ who past view response, response ∈ (players who past view).support →
          response ∈ countedMenu.actions who past view := by
        intro who past view response supported
        by_cases same : who = focal
        · subst who
          exact tailCovered past view response
            (by simpa only [players, Function.update_self] using supported)
        · dsimp only [players] at supported
          rw [Function.update_of_ne same] at supported
          exact countedMenu.decode_embedPolicy_covered initial horizon scheduler who
            (countedAssessmentProfile assessment who) past view response supported
      obtain ⟨anchorTrace⟩ := countedMenu.trace_respond initial horizon (family seed) remaining
        execution focal action trace offered
      have retained : anchor.recall owner = execution.recall owner :=
        app.respond_recall_other execution focal owner different action
      obtain ⟨first, word, firstRequest, zero⟩ := bad_owner_initial_record_at_good_clock_two seed
        remaining execution focal trace request clock empty good owner bit
      have placement : 6 ≤ execution.environmentRecall.length ∧
          execution.environmentRecall.length ≤ 8 := by
        rcases original_first_late_input_placement seed ⟨remaining, some focal, execution⟩
            (countedMenu.toRawTrace initial horizon (family seed) trace) focal rfl request.1.symm
              clock with early | late
        · exact ⟨early.1, early.2.1⟩
        · rw [good] at late
          cases late.2.2
      have anchorLength : anchor.environmentRecall.length = execution.environmentRecall.length :=
        congrArg List.length (app.respond_environmentRecall execution focal action)
      have forecast := foreign_singleton_bad_original_admission_iff_packets assessment equilibrium
        seed supportedSeed remaining anchor anchorTrace owner bit (by omega) (by omega) first
          (retained.trans word) firstRequest zero players covered
            (Function.update_of_ne different _ _) final reached (resolved owner)
      have packets : initialPublicPackets anchor = initialPublicPackets execution := rfl
      simpa only [originalReceiptForecast, bit, Bool.false_eq_true, ite_false, packets] using
        forecast

end Vegas.Examples.CommitSeedBroadcast
