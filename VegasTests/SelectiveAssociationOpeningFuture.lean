/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningEquilibrium
import VegasTests.SelectiveAssociationDecisionContinuation
import Interaction.ReactiveInvariantContinuation

/-! # Opening incentives in later continuation histories -/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

theorem native_full_continuation_of_enough
    (profile : ∀ who, nativeModel.BehavioralPolicy who)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (fuel : Nat) (enough : nativeApp.rank nativeHorizon (some control) ≤ fuel)
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom profile fuel
      ⟨some control, trace⟩).support) :
    ∃ full ∈ (nativeModel.runBehavioralFrom profile (2 * nativeHorizon + 1)
      ⟨some control, trace⟩).support, full.state = final.state := by
  have short := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler profile fuel ⟨some control, trace⟩ enough
  have long := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change nativeApp.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := nativeApp.trace_bound (FinDist.pure nativeInitial) nativeHorizon
        nativeScheduler (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon
          nativeScheduler trace)
      omega)
  have mapped : final.state ∈ ((nativeModel.runBehavioralFrom profile fuel
      ⟨some control, trace⟩).map ExecutionProtocol.History.state).support := by
    rw [FinDist.support_map]
    exact ⟨final, supported, rfl⟩
  rw [short, ← long, FinDist.support_map] at mapped
  exact mapped

open Classical in
/-- A later opening decision uses the same checked information-local theorem;
any amount of fuel reaching termination suffices. -/
theorem native_opening_exact_from_control
    (assessment : nativeModel.BehavioralAssessment)
    (rational : assessment.IsSequentiallyRationalWithin
      (fun who history => nativeUtility who history.state) (2 * nativeHorizon + 1))
    (who : Player) (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (bit : Bool) (stored : (nativeBindingRef who).get?
      control.execution.application.config.store = some (.success bit))
    (fuel : Nat) (enough : nativeApp.rank nativeHorizon (some control) ≤ fuel)
    (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom assessment.strategy fuel
      ⟨some control, trace⟩).support) :
    nativePublicationAt who final.state = some (.success bit) := by
  let past := control.execution.recall who
  let view := control.execution.observe nativeApp who
  have information : nativeModel.infoOf who trace = some (past, view) := by
    change (nativeMenu.signals (FinDist.pure nativeInitial) nativeHorizon nativeScheduler).infoOf
      who trace = some (past, view)
    rw [nativeMenu.info]
    simp only [ReactiveApplication.observe, active, ↓reduceIte]
    rfl
  let history : nativeModel.InformationHistory who (some (past, view)) :=
    ⟨⟨some control, trace⟩, information⟩
  have running : ¬nativeArena.terminal (some control) := by
    intro stopped
    have no : control.actor = none := stopped.2
    rw [active] at no
    cases no
  let site : nativeModel.InformationSite who := ⟨some (past, view), history, running,
    nativeOpeningResponse who view, (nativeOpeningChoice who past view).2⟩
  obtain ⟨full, fullMem, same⟩ := native_full_continuation_of_enough assessment.strategy
    control trace fuel enough final supported
  have exactResult := native_sequentially_rational_opening_exact assessment who site past view
    rfl bit granted (by
      change nativePublicationEvent who ∉
        control.execution.application.config.history.map EventGraph.Completion.event
      intro completed
      exact unfinished ((control.execution.application.config.history_exact _).mp completed))
    (by
      change (nativeBindingRef who).get?
        (nativeGraph.playerStore who control.execution.application.config.store) = _
      rwa [(nativeBindingRef who).get?_playerStore who _ rfl])
    (rational who site) history full fullMem
  rwa [same] at exactResult

theorem native_decision_earlier_completed (event earlier : nativeGraph.EventId)
    (before : earlier.val < event.val) (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control))
    (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event) :
    earlier ∈ control.execution.application.config.cut.completed := by
  have position := (native_decision_cursor event control trace _ active granted).2
  obtain ⟨_, prior, priorMem, activated⟩ :=
    native_decision_predecessor event control trace active position
  obtain ⟨valid, _, completed⟩ :=
    native_response_prefix_facts nativeMenu.uniformResponses event prior priorMem
  exact (nativeRuntime.reactive_environment_progress nativeLeaks nativeInputs prior
    control.execution (.activate (nativeOwner event)) valid activated).completed
      (completed earlier before)

/-- At an opening visit the earlier binding has already been settled. If a
later state contains a successful binding, this same value was available at
the opening decision, independently of the intervening strategy. -/
theorem native_binding_at_opening_from_final
    (profile : ∀ who, nativeModel.BehavioralPolicy who) (who : Player)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (fuel : Nat) (final : nativeArena.History)
    (supported : final ∈ (nativeModel.runBehavioralFrom profile fuel
      ⟨some control, trace⟩).support)
    (result : nativeApp.Control) (finalEq : final.state = some result) (bit : Bool)
    (stored : (nativeBindingRef who).get? result.execution.application.config.store =
      some (.success bit)) :
    (nativeBindingRef who).get? control.execution.application.config.store =
      some (.success bit) := by
  obtain ⟨event, field, earlier⟩ : ∃ event : nativeGraph.EventId,
      (nativeBindingRef who).field = .inr event ∧ event.val < (nativePublicationEvent who).val := by
    fin_cases who
    · exact ⟨aliceBinding, rfl, by decide⟩
    · exact ⟨bobBinding, rfl, by decide⟩
    · exact ⟨carolBinding, rfl, by decide⟩
  have completed := native_decision_earlier_completed (nativePublicationEvent who) event earlier
    control trace (by rwa [native_publication_owner]) granted
  have output := (control.execution.application.config.output_available event).mpr completed
  have present := (nativeBindingRef who).get?_isSome
    control.execution.application.config.store (by rw [field]; exact output)
  cases value : (nativeBindingRef who).get? control.execution.application.config.store with
  | none => rw [value] at present; cases present
  | some binding =>
      obtain ⟨later, laterEq, preserved⟩ :=
        (native_binding_invariant who binding).behavioral_continuation nativeMenu
          (FinDist.pure nativeInitial) nativeHorizon nativeScheduler profile fuel control trace
          final value supported
      have same : later = result := Option.some.inj (laterEq.symm.trans finalEq)
      subst later
      exact preserved.symm.trans stored

end VegasTests.SelectiveAssociation
