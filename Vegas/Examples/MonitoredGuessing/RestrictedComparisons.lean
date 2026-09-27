/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedComparator
import Vegas.Examples.MonitoredGuessing.EnforcementPayoffs
import Vegas.Examples.MonitoredGuessing.RestrictedValues
import Vegas.Examples.MonitoredGuessing.RestrictedClock
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Ordinary-response comparisons in native behavioral continuations

These equations connect the concrete service suffixes to the continuation
contexts used by the action-restriction theorem. The utilities include the
fixed deposits and actual receipt/ledger liabilities.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem final_finish_comparison (table : PayoffTable)
    (rawPlayers legalPlayers : Player → nativeApp.Policy)
    (bit guess : Bool) (response : nativeApp.Action)
    (rawChoice : rawPlayers alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) = FinDist.pure response)
    (legalChoice : legalPlayers alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
        FinDist.pure (finalComparator (aliceInput bit guess) response)) :
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler rawPlayers
      (some ⟨4, some alice, beforeAlice bit guess⟩)).expect
        (fun state => Enforcement.stateUtility table state alice) ≤
    (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler legalPlayers
      (some ⟨4, some alice, beforeAlice bit guess⟩)).expect
        (fun state => Enforcement.stateUtility table state alice) := by
  have rawFinish := native_finish_response rawPlayers (nativePlan.take 9) resolutionTail alice
    rfl (beforeAlice bit guess) (before_alice_position bit guess)
  have legalFinish := native_finish_response legalPlayers (nativePlan.take 9) resolutionTail alice
    rfl (beforeAlice bit guess) (before_alice_position bit guess)
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler rawPlayers
    (some ⟨4, some alice, beforeAlice bit guess⟩) = _ at rawFinish
  change nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler legalPlayers
    (some ⟨4, some alice, beforeAlice bit guess⟩) = _ at legalFinish
  rw [rawFinish, legalFinish, rawChoice, legalChoice, FinDist.pure_bind,
    FinDist.pure_bind, FinDist.expect_map, FinDist.expect_map]
  simpa only [Enforcement.stateUtility, ReactiveApplication.finished, Option.elim_some,
    Enforcement.executionUtility,
    Enforcement.liability, ↓reduceIte, mul_ite, mul_one, mul_zero] using
    final_comparator_declared_payoff_le table (Enforcement.deposit table alice)
      (by exact_mod_cast Enforcement.deposit_nonnegative table alice)
      rawPlayers legalPlayers bit guess response

open Classical in
/-- The final comparison has the exact behavioral-policy shape required by
the generic extension theorem, from every retained final information history. -/
theorem final_continuation_comparison (table : PayoffTable)
    (sourceProfile : Profile restrictedModel.behavioralSignature)
    (targetProfile : Profile watchedModel.behavioralSignature)
    (bit guess : Bool) (site : restrictedModel.InformationSite alice)
    (observed : site.1 = aliceInput bit guess)
    (action : watchedModel.Choice alice (ordinaryRestriction.site alice site).1)
    (history : restrictedModel.InformationHistory alice site.1)
    (fuel : Nat) (enough : 9 ≤ fuel) :
    (watchedModel.runBehavioralFrom
      (Profile.update (sig := watchedModel.behavioralSignature) targetProfile alice
        ((targetProfile alice).commit (ordinaryRestriction.site alice site).1 action))
      fuel (ordinaryRestriction.history history.1)).expect
        (fun final => Enforcement.stateUtility table final.state alice) ≤
    (restrictedModel.runBehavioralFrom
      (Profile.update (sig := restrictedModel.behavioralSignature) sourceProfile alice
        ((sourceProfile alice).withLaw site.1 (ordinaryComparator alice site action)))
      fuel history.1).expect
        (fun final => Enforcement.stateUtility table final.state alice) := by
  classical
  rcases site with ⟨information, occurs⟩
  dsimp only at observed
  subst information
  have known := final_alice_known_state bit guess history
  let rawProfile := Profile.update (sig := watchedModel.behavioralSignature) targetProfile alice
    ((targetProfile alice).commit (aliceInput bit guess) action)
  let legalProfile := Profile.update (sig := restrictedModel.behavioralSignature)
    sourceProfile alice ((sourceProfile alice).withLaw (aliceInput bit guess)
      (ordinaryComparator alice ⟨aliceInput bit guess, occurs⟩ action))
  let rawPlayers := watchedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
    rawProfile
  let legalPlayers := restrictedMenu.decodeProfile nativeInitialLaw nativeHorizon nativeScheduler
    legalProfile
  have allowed := action.2
  change ∃ response ∈ watchedMenu.actions alice ((beforeAlice bit guess).recall alice)
    ((beforeAlice bit guess).observe nativeApp alice), action.1 = some response at allowed
  obtain ⟨response, _, same⟩ := allowed
  have rawChoice : rawPlayers alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) = FinDist.pure response := by
    simp only [rawPlayers, rawProfile, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, FinDist.map_comp]
    change (((targetProfile alice).commit (aliceInput bit guess) action)
      (aliceInput bit guess)).map (fun chosen => chosen.1.getD nativeSilent) = _
    rw [InformationModel.BehavioralPolicy.commit_self, FinDist.map_pure, same]
    rfl
  have legalChoice : legalPlayers alice ((beforeAlice bit guess).recall alice)
      ((beforeAlice bit guess).observe nativeApp alice) =
        FinDist.pure (finalComparator (aliceInput bit guess) response) := by
    simp only [legalPlayers, legalProfile, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy,
      ReactiveApplication.ResponseMenu.embedPolicy, FinDist.map_comp]
    change (((sourceProfile alice).withLaw (aliceInput bit guess)
      (ordinaryComparator alice ⟨aliceInput bit guess, occurs⟩ action))
      (aliceInput bit guess)).map (fun chosen => chosen.1.getD nativeSilent) = _
    rw [InformationModel.BehavioralPolicy.withLaw_self]
    simp only [ordinaryComparator, FinDist.map_pure, Option.getD_some, same]
    rfl
  have rawLaw := watchedMenu.run_eq_finish nativeInitialLaw nativeHorizon nativeScheduler
    rawProfile fuel (ordinaryRestriction.history history.1) (by
      change nativeApp.rank nativeHorizon history.1.state ≤ fuel
      rw [known]
      exact enough)
  have legalLaw := restrictedMenu.run_eq_finish nativeInitialLaw nativeHorizon nativeScheduler
    legalProfile fuel history.1 (by rw [known]; exact enough)
  have rawValue := congrArg (fun law : FinDist nativeApp.ProtocolState =>
    law.expect (fun state => Enforcement.stateUtility table state alice)) rawLaw
  have legalValue := congrArg (fun law : FinDist nativeApp.ProtocolState =>
    law.expect (fun state => Enforcement.stateUtility table state alice)) legalLaw
  rw [FinDist.expect_map] at rawValue legalValue
  change (watchedModel.runBehavioralFrom rawProfile fuel
    (ordinaryRestriction.history history.1)).expect _ ≤
      (restrictedModel.runBehavioralFrom legalProfile fuel history.1).expect _
  rw [rawValue, legalValue]
  change (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler rawPlayers
    history.1.state).expect _ ≤
      (nativeApp.finish nativeInitialLaw nativeHorizon nativeScheduler legalPlayers
        history.1.state).expect _
  rw [known]
  exact final_finish_comparison table rawPlayers legalPlayers bit guess response
    rawChoice legalChoice

end Vegas.Examples.MonitoredGuessing.Restricted
