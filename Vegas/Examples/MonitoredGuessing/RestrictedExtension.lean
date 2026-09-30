/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.MonitoredGuessing.RestrictedInitialComparison
import Vegas.Examples.MonitoredGuessing.RestrictedBobComparisons
import Vegas.Examples.MonitoredGuessing.RestrictedComparisons
import Vegas.Examples.MonitoredGuessing.WatcherRaw
import GameTheoryExtensions.Protocol.ContinuationHorizon

/-! # Restoring every ordinary-player response

The actual service and fixed whole-outcome deposits discharge every local
comparison in the generic extension theorem. Initial extra sender traffic is
monitored, receiver traffic is either harmless or audited, and final sender
responses have a legal result-preserving comparator. No rationality assumption
is imposed on these comparisons' continuation profiles.
-/

noncomputable section

namespace Vegas.Examples.MonitoredGuessing.Restricted

open Vegas Vegas.EventGraphRuntime Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem watched_alice_depth (site : restrictedModel.InformationSite alice) :
    watchedDepth alice (ordinaryRestriction.site alice site) =
      match site.1 with
      | none => 2
      | some (past, _) => if past = [] then 2 else 12 := by
  simp only [watchedDepth, effectiveDepth, nativeDecisionDepth,
    show alice ≠ bob by decide, show alice ≠ watcher by decide, ↓reduceIte]
  have information : (effectiveRawRestriction.site alice (watcherRestriction.site alice
    (ordinaryRestriction.site alice site))).1 = site.1 := rfl
  rw [information]
  cases site.1 with
  | none => rfl
  | some data =>
      rcases data with ⟨past, view⟩
      dsimp only

private theorem watched_initial_depth (bit : Bool)
    (site : restrictedModel.InformationSite alice)
    (observed : site.1 = some ([], (aliceActivated bit).observe nativeApp alice)) :
    watchedDepth alice (ordinaryRestriction.site alice site) = 2 := by
  rw [watched_alice_depth, observed]
  rfl

private theorem watched_final_depth (bit guess : Bool)
    (site : restrictedModel.InformationSite alice)
    (observed : site.1 = aliceInput bit guess) :
    watchedDepth alice (ordinaryRestriction.site alice site) = 12 := by
  rw [watched_alice_depth, observed]
  cases guess <;> exact ite_eq_right (List.cons_ne_nil _ _)

/-- Every restricted equilibrium extends to the fixed watched game, with its
retained policies, beliefs, and full initialized history/net-payoff law. -/
theorem ordinary_equilibrium_extends (table : PayoffTable)
    (source : restrictedModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
        restricted_decisionRecall.decisionInformationAntichain
      (fun who site => source.truncatedContinuationContext site
        (fun history => Enforcement.stateUtility table history.state who)
        (2 * nativeHorizon + 1 - restrictedDepth who site))) :
    ∃ target : watchedModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor watched_decisionRecall.decisionInformationAntichain
        (fun who site => target.truncatedContinuationContext site
          (fun history => Enforcement.stateUtility table history.state who)
          (2 * nativeHorizon + 1 - watchedDepth who site)) ∧
      ordinaryRestriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (ordinaryRestriction.site who site) =
        (source.belief who site).map (ordinaryRestriction.informationHistory who site)) ∧
      (restrictedModel.runBehavioral source.strategy (2 * nativeHorizon + 1)).map
          ordinaryRestriction.history =
        watchedModel.runBehavioral target.strategy (2 * nativeHorizon + 1) ∧
      (restrictedModel.runBehavioral source.strategy (2 * nativeHorizon + 1)).map
          (fun history => (ordinaryRestriction.history history,
            Enforcement.stateUtility table history.state)) =
        (watchedModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
          (fun history => (history, Enforcement.stateUtility table history.state)) ∧
      ∀ history ∈ (watchedModel.runBehavioral target.strategy
        (2 * nativeHorizon + 1)).support, watchedArena.terminal history.state := by
  classical
  have targetBounded := watchedMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler
  have sourceBounded := restrictedMenu.bounded nativeInitialLaw nativeHorizon nativeScheduler
  have targetCertificate := targetBounded.wellFoundedHistories
  have sourceCertificate := sourceBounded.wellFoundedHistories
  let _ := Fintype.ofFinite watchedArena.History
  have sourceTerminal := (source.isSequentialEquilibrium_iff_remaining restrictedModel _
    sourceCertificate sourceBounded restrictedDepth restricted_common_depth _).mpr equilibrium
  obtain ⟨target, targetTerminal, agrees, beliefs, historyLaw, joint⟩ :=
    ordinaryRestriction.sequentialEquilibrium_extends_of_comparator
      restricted_decisionRecall.decisionInformationAntichain sourceCertificate targetCertificate
      (watchedMenu.uniformAssessment nativeInitialLaw nativeHorizon nativeScheduler)
      (watchedMenu.uniform_fullyMixed nativeInitialLaw nativeHorizon nativeScheduler)
      watched_decisionRecall (fun who site => watchedDepth who (ordinaryRestriction.site who site))
      (fun who site => watched_common_depth who (ordinaryRestriction.site who site))
      (fun who history => Enforcement.stateUtility table history.state who)
      (fun who history => Enforcement.stateUtility table history.state who)
      (fun _ _ => rfl) ordinaryComparator (fun sourceProfile targetProfile paired who site action
        extra history => by
        rw [ordinaryRestriction.runBehavioralTerminalFrom_history_eq_remaining targetCertificate
            targetBounded _ (watched_common_depth who (ordinaryRestriction.site who site)),
          ordinaryRestriction.runBehavioralTerminalFrom_eq_remaining sourceCertificate
            targetBounded _ (watched_common_depth who (ordinaryRestriction.site who site))]
        fin_cases who
        · change restrictedModel.InformationSite alice at site
          rcases alice_site_cases site with ⟨bit, early⟩ | ⟨bit, guess, final⟩
          · apply initial_continuation_comparison table sourceProfile targetProfile bit site early
              action extra history
            change 23 ≤ 25 - watchedDepth alice (ordinaryRestriction.site alice site)
            rw [watched_initial_depth bit site early]
          · apply final_continuation_comparison table sourceProfile targetProfile bit guess site
              final action history
            change 9 ≤ 25 - watchedDepth alice (ordinaryRestriction.site alice site)
            rw [watched_final_depth bit guess site final]
            decide
        · apply bob_continuation_comparison table sourceProfile targetProfile paired site action
            extra history
          change 17 ≤ 25 - watchedDepth bob (ordinaryRestriction.site bob site)
          simp only [watchedDepth, effectiveDepth, nativeDecisionDepth, ↓reduceIte]
          decide
        · exact (extra (watcher_choice_surjective site.1 action)).elim)
      source sourceTerminal
  rw [InformationModel.runBehavioralTerminalFrom_initHistory _
      sourceCertificate _ sourceBounded,
    InformationModel.runBehavioralTerminalFrom_initHistory _
      targetCertificate _ targetBounded] at historyLaw joint
  exact ⟨target, (target.isSequentialEquilibrium_iff_remaining watchedModel _ targetCertificate
    targetBounded watchedDepth watched_common_depth _).mp targetTerminal, agrees, beliefs,
    historyLaw, joint, fun history supported =>
      watchedModel.runBehavioralFrom_terminal_of_bound _ targetBounded _ history supported⟩

/-- The composed ordinary, watcher and raw-response extensions retain the
joint observation/net-payoff law of every restricted equilibrium. -/
theorem restricted_raw_equilibrium_extends (table : PayoffTable)
    (watcherZero : ∀ result, table result watcher = 0)
    {Observation : Type} (observe : nativeApp.ProtocolState → Observation)
    (observationInvariant : ∀ state, observe (normalization.state state) = observe state)
    (source : restrictedModel.BehavioralAssessment)
    (equilibrium : source.IsSequentialEquilibriumFor
        restricted_decisionRecall.decisionInformationAntichain
      (fun who site => source.truncatedContinuationContext site
        (fun history => Enforcement.stateUtility table history.state who)
        (2 * nativeHorizon + 1 - restrictedDepth who site))) :
    ∃ target : nativeModel.BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (nativeMenu.decisionInformationAntichain nativeInitialLaw nativeHorizon nativeScheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => Enforcement.stateUtility table history.state who)
          (2 * nativeHorizon + 1)) ∧
      (nativeModel.runBehavioral target.strategy (2 * nativeHorizon + 1)).map
          (fun history => (observe history.state, Enforcement.stateUtility table history.state)) =
        (restrictedModel.runBehavioral source.strategy (2 * nativeHorizon + 1)).map
          (fun history => (observe history.state,
            Enforcement.stateUtility table history.state)) := by
  classical
  obtain ⟨watched, watchedSE, _, _, executionLaw, _, _⟩ :=
    ordinary_equilibrium_extends table source equilibrium
  obtain ⟨raw, rawSE, jointLaw⟩ := watcher_raw_equilibrium_extends observe observationInvariant
    (Enforcement.stateUtility table) (Enforcement.stateUtility_normalization table)
    (Enforcement.stateUtility_watcher table watcherZero) watched watchedSE
  refine ⟨raw, rawSE, ?_⟩
  rw [jointLaw, ← executionLaw, PMF.map_comp]
  rfl

end Vegas.Examples.MonitoredGuessing.Restricted
