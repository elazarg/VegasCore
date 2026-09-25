/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationRestrictedPrefixExecution
import Vegas.Pending.ReactiveEvidenceOrigin
import Interaction.ReactiveObservationRestriction

/-! # Hidden accepted candidates in restricted native prefixes

A successful true binding that has no public true certificate has no public
certificate for its accepted handle at all: soundness excludes certificates
for every other value. Empty passive observation then excludes possession by
every foreign player. These statements cover all legal raw histories.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation.Restricted.Prefix

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

theorem true_binding_handle (control : app.Control) (trace : arena.Trace (some control))
    (successful : aliceBindingRef.get? control.execution.application.config.store =
      some (.success true)) :
    ∃ selected : Handle nativeGraph,
      control.execution.application.accepted aliceBindingRef.field = some selected ∧
      selected.1 = alice ∧
      control.execution.application.candidates.lookup selected = .openable ⟨.bool, true⟩ :=
  (history_invariants control trace).1.success_provenance aliceBindingRef true successful

/-- At a fixed information view the successful binding fixes one common
handle, so the later probability injection uses one fixed involution. -/
theorem true_view_handle (control : app.Control) (trace : arena.Trace (some control))
    (observer : Player) (view : app.PlayerView)
    (observed : control.execution.observe app observer = view)
    (successful : aliceBindingRef.get? control.execution.application.config.store =
      some (.success true)) :
    let selected :=
      (view.application.publicView.accepted aliceBindingRef.field).getD (alice, .prepared 0)
    selected.1 = alice ∧
      control.execution.application.accepted aliceBindingRef.field = some selected ∧
      control.execution.application.candidates.lookup selected = .openable ⟨.bool, true⟩ := by
  obtain ⟨selected, associated, owner, fixed⟩ := true_binding_handle control trace successful
  have viewAccepted : view.application.publicView.accepted aliceBindingRef.field =
      some selected := by
    rw [← observed]
    exact associated
  simpa only [viewAccepted, Option.getD_some] using And.intro owner (And.intro associated fixed)

theorem uncertified_ledger (control : app.Control) (trace : arena.Trace (some control))
    (selected : Handle nativeGraph)
    (associated : control.execution.application.accepted aliceBindingRef.field = some selected)
    (fixed : control.execution.application.candidates.lookup selected = .openable ⟨.bool, true⟩)
    (observer : Player)
    (uncertified : publicGuess (control.execution.observe app observer) = false) :
    ∀ sent ∈ control.execution.network.ledger, ∀ fact,
      sent.payload.evidence = some fact → fact.handle ≠ selected := by
  intro sent published fact certified sameHandle
  have raw := menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace
  have sound := (nativeRuntime.packetEvidence leaks).history_sound
    (FinDist.pure nativeInitial) nativeHorizon scheduler raw
  have factValid : fact.Holds control.execution.application :=
    sound.ledger sent published fact (by
      change fact ∈ sent.payload.evidence.toList
      simp only [certified, Option.toList_some, List.mem_singleton])
  change control.execution.application.candidates.lookup fact.handle = .openable fact.raw
    at factValid
  rw [sameHandle, fixed] at factValid
  have rawEq : fact.raw = ⟨.bool, true⟩ := by
    injection factValid with same
    exact same.symm
  have factEq : fact = ⟨selected, ⟨.bool, true⟩⟩ := by
    cases fact
    exact congrArg₂ OpeningFact.mk sameHandle rawEq
  rw [factEq] at certified
  have disclosed : publicGuess (control.execution.observe app observer) = true := by
    change (match control.execution.application.accepted aliceBindingRef.field with
      | none => false
      | some accepted => control.execution.network.ledger.any fun message =>
          message.payload.evidence.any fun evidence =>
            decide (evidence.handle = accepted) && (evidence.raw.as? .bool).getD false) = true
    rw [associated]
    apply List.any_eq_true.mpr
    refine ⟨sent, published, ?_⟩
    simp only [certified, Option.any_some, decide_true, Bool.true_and,
      Raw.as?, dite_true, Option.getD_some]
    rfl
  rw [uncertified] at disclosed
  cases disclosed

theorem no_certificate_observed (control : app.Control) (trace : arena.Trace (some control))
    (selected : Handle nativeGraph)
    (unpublished : ∀ sent ∈ control.execution.network.ledger, ∀ fact,
      sent.payload.evidence = some fact → fact.handle ≠ selected) (who : Player) :
    ∀ sent ∈ control.execution.network.leaked who ++ control.execution.network.ledger,
      ∀ fact, sent.payload.evidence = some fact → fact.handle ≠ selected := by
  have raw := menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace
  have empty := app.history_leaked_empty (by intros; rfl) (FinDist.pure nativeInitial)
    nativeHorizon scheduler raw who
  simpa only [empty, List.nil_append] using unpublished

theorem no_foreign_certificate_known (control : app.Control)
    (trace : arena.Trace (some control)) (selected : Handle nativeGraph)
    (unpublished : ∀ sent ∈ control.execution.network.ledger, ∀ fact,
      sent.payload.evidence = some fact → fact.handle ≠ selected)
    (who : Player) (foreign : selected.1 ≠ who) :
    ∀ sent ∈ control.execution.network.known who, ∀ fact,
      sent.payload.evidence = some fact → fact.handle ≠ selected := by
  intro sent known fact certified sameHandle
  obtain ⟨publication, published, carried⟩ := nativeRuntime.foreign_certificate_published leaks
    (by intros; rfl) (FinDist.pure nativeInitial) nativeHorizon scheduler control
    (menu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon scheduler trace)
    who sent known fact certified (by rwa [sameHandle])
  exact unpublished publication published fact carried sameHandle

theorem respond_ledger (execution : app.Execution) (who : Player) (action : app.Action) :
    (execution.respond app who action).network.ledger = execution.network.ledger := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit => rfl
      | replay id =>
          cases found : (execution.network.known who).find? (fun sent => sent.id = id) <;>
            simp only [ReactiveApplication.Execution.respond, MessageNetwork.replay, found]

theorem environmentResult_ledger_subset (execution : app.Execution) (command : app.Command) :
    execution.network.ledger ⊆ (environmentResult execution command).network.ledger := by
  have reached : environmentResult execution command ∈
      (execution.environmentStep app command).support := by
    rw [environmentResult_law]
    exact FinDist.mem_support_pure.mpr rfl
  cases command with
  | activate who => rw [environmentResult_activate]; exact List.Subset.refl _
  | wait =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        FinDist.mem_support_pure] at reached
      rw [reached]
  | «include» id =>
      simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_pure,
        FinDist.mem_support_pure] at reached
      rw [reached]
      cases found : execution.network.lookup id <;>
        simp only [ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
          found]
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _
  | application command =>
      obtain ⟨updated, supported, same⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨state, _, updatedEq⟩ := FinDist.support_map .. ▸ supported
      rw [← same, ← updatedEq]

theorem bob_ledger_subset (responses : BobResponses) :
    (carolInput responses.beforeCarol).network.ledger ⊆ (bobInput responses).network.ledger := by
  intro sent member
  let submittedExecution :=
    (carolInput responses.beforeCarol).respond app carol responses.carolBinding
  have submitted : sent ∈ submittedExecution.network.ledger := by
    dsimp only [submittedExecution]
    rw [respond_ledger]
    exact member
  exact environmentResult_ledger_subset _ _
    (environmentResult_ledger_subset _ _
      (environmentResult_ledger_subset _ _
        (environmentResult_ledger_subset _ _
          (environmentResult_ledger_subset _ _ submitted))))

theorem environmentResult_inputRecall (execution : app.Execution) (command : app.Command)
    (valid : execution.InputRecall app) :
    (environmentResult execution command).InputRecall app := by
  apply app.environment_inputRecall execution _ command valid
  rw [environmentResult_law]
  exact FinDist.mem_support_pure.mpr rfl

theorem bobPrelude_inputRecall (first : app.Action) : (bobPreludeInput first).InputRecall app :=
  app.respond_inputRecall _ alice first (app.initial_inputRecall nativeInitial)

theorem aliceInput_inputRecall (first second : app.Action) :
    (aliceInput first second).InputRecall app :=
  environmentResult_inputRecall _ _
    (app.respond_inputRecall _ bob second (bobPrelude_inputRecall first))

end VegasTests.SelectiveAssociation.Restricted.Prefix
