/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningContinuation
import GameTheoryExtensions.Protocol.SequentialChoices

/-! # Information-local incentives for ordinary opening

The public grant, unfinished event, and owned binding are all observable.
Consequently the same legal opening response gives the checked continuation
guarantee throughout the information fiber, including zero-belief histories.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

theorem native_information_control (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView)
    (history : nativeModel.InformationHistory who (some (past, view))) :
    ∃ control, history.1.state = some control ∧ control.actor = some who ∧
      control.execution.recall who = past ∧ control.execution.observe nativeApp who = view := by
  rcases history with ⟨⟨state, trace⟩, information⟩
  change (nativeMenu.signals (FinDist.pure nativeInitial) nativeHorizon nativeScheduler).infoOf
    who trace = some (past, view) at information
  rw [nativeMenu.info] at information
  cases state with
  | none => cases information
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at information
        exact ⟨control, rfl, active, congrArg Prod.fst (Option.some.inj information),
          congrArg Prod.snd (Option.some.inj information)⟩
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at information
        cases information

theorem native_opening_fiber_lower
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (who : Player) (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (opens : profile who (some (past, view)) = FinDist.pure (nativeOpeningChoice who past view))
    (history : nativeModel.InformationHistory who (some (past, view))) :
    -1 ≤ (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1) history.1).expect
      (fun final => nativeUtility who final.state) := by
  obtain ⟨control, stateEq, active, recall, observed⟩ :=
    native_information_control who past view history
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  have grant : control.execution.application.serviceGrant = some (nativePublicationEvent who) := by
    rw [← observed] at granted
    exact granted
  have incomplete : nativePublicationEvent who ∉
      control.execution.application.config.cut.completed := by
    rw [← observed] at unfinished
    change nativePublicationEvent who ∉
      control.execution.application.config.history.map EventGraph.Completion.event at unfinished
    exact fun completed => unfinished
      ((control.execution.application.config.history_exact _).mpr completed)
  have binding : (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit) := by
    rw [← observed] at stored
    change (nativeBindingRef who).get?
      (nativeGraph.playerStore who control.execution.application.config.store) = _ at stored
    rw [(nativeBindingRef who).get?_playerStore who _ rfl] at stored
    exact stored
  exact native_opening_behavioral_lower profile control trace who bit active grant incomplete
    binding (by subst past; subst view; exact opens)

theorem native_failed_utility (config : nativeGraph.Config) (who : Player)
    (failed : (nativePublicationRef who).get? config.store = some .failure) :
    utility (nativeResults config) who = -4 := by
  fin_cases who
  · change alicePublicationRef.get? config.store = some .failure at failed
    change utility (nativeResults config) alice = -4
    simp [utility_alice, nativeResults, failed]
  · change bobPublicationRef.get? config.store = some .failure at failed
    change utility (nativeResults config) bob = -4
    simp [utility_bob, nativeResults, failed]
  · change carolPublicationRef.get? config.store = some .failure at failed
    change utility (nativeResults config) carol = -4
    simp [utility_carol, nativeResults, failed]

open Classical in
/-- A raw response that fails throughout an opening information set cannot be
used by a sequentially rational assessment. The failing response is arbitrary;
its operational classification is separate from the incentive proof. -/
theorem native_not_supported_failing_opening
    (assessment : nativeModel.BehavioralAssessment) (who : Player)
    (site : nativeModel.InformationSite who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site (fun history => nativeUtility who history.state)
        (2 * nativeHorizon + 1)))
    (choice : nativeModel.Choice who site.1)
    (fails : ∀ history : nativeModel.InformationHistory who site.1,
      ∀ final ∈ (nativeModel.runBehavioralFrom
        (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who
          ((assessment.strategy who).commit site.1 choice))
        (2 * nativeHorizon + 1) history.1).support,
      ∃ control, final.state = some control ∧
        (nativePublicationRef who).get? control.execution.application.config.store =
          some .failure) :
    choice ∉ (assessment.strategy who site.1).support := by
  classical
  let alternative := (assessment.strategy who).commit (some (past, view))
    (nativeOpeningChoice who past view)
  apply assessment.not_supported_choice_of_uniform_gap
    (nativeModel.actsOnceWhereItMatters_of_actsOnce
      (InformationModel.actsOnce_of_decisionInformationAntichain
        (nativeMenu.decisionInformationAntichain (FinDist.pure nativeInitial) nativeHorizon
          nativeScheduler))) site
    (nativeMenu.informationSite_allNonterminal (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler who site)
    (fun history => nativeUtility who history.state) (2 * nativeHorizon) rational choice
    alternative (-4) (-1) (by norm_num)
  · intro history
    apply FinDist.expect_le_of_forall
    intro final supported
    obtain ⟨control, stateEq, failed⟩ := fails history final supported
    rw [stateEq]
    exact le_of_eq (native_failed_utility control.execution.application.config who failed)
  · intro history
    have good := native_opening_fiber_lower
      (Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who alternative)
      who past view bit granted unfinished stored
    exact good (by
      rw [Profile.update]
      rw [Function.update_self]
      exact InformationModel.BehavioralPolicy.commit_self _ _ _)
      ⟨history.1, history.2.trans siteEq⟩

end VegasTests.SelectiveAssociation
