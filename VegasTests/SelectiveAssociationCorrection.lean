/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningContinuation
import VegasTests.SelectiveAssociationResponses
import Vegas.Pending.ReactiveCandidateBudget

/-! # Bob can replace his earlier pending guess

Bob has only one earlier response. Two candidate slots therefore suffice for
a fresh Boolean binding, regardless of what that earlier response transmitted.
The new packet is immediately selected by the real reserved service. These
lemmas establish a feasible corrective choice; optimality still requires the
subsequent publication incentives.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

def bobCorrection (serial : Nat) (bit : Bool) : nativeApp.Action :=
  nativeRuntime.reactiveBinding nativeLeaks bob bobBinding .bool (.success bit) serial

theorem bob_correction_available (serial : Nat) (bit : Bool) (bounded : serial < 2)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) :
    bobCorrection serial bit ∈ nativeMenu.actions bob past view := by
  change bobCorrection serial bit ∈
    (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions bob past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change (⟨⟨.commitment bobBinding (bob, .prepared serial), some ⟨.bool, bit⟩⟩, .none⟩ :
    WitnessedSubmission nativeGraph) ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  refine ⟨⟨bounded, ?_⟩, trivial⟩
  change (⟨.bool, bit⟩ : Raw simpleExpr) ∈ nativeBounds.values
  cases bit <;> decide

def bobCorrectiveResponse (bit : Bool) (view : nativeApp.PlayerView) : nativeApp.Action :=
  match reactiveFreshSlot view.application with
  | none => ⟨none⟩
  | some serial => if serial < 2 then bobCorrection serial bit else ⟨none⟩

theorem bob_corrective_response_available (bit : Bool)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView) :
    bobCorrectiveResponse bit view ∈ nativeMenu.actions bob past view := by
  have silent : (⟨none⟩ : nativeApp.Action) ∈ nativeMenu.actions bob past view := by
    change (⟨none⟩ : nativeApp.Action) ∈
      (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions bob past view
    rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
    trivial
  unfold bobCorrectiveResponse
  split
  · exact silent
  · split
    · exact bob_correction_available _ bit ‹_› past view
    · exact silent

theorem bob_correction_fresh (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control))
    (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding) (bit : Bool) :
    ∃ serial, serial < 2 ∧
      control.execution.application.candidates.lookup (bob, .prepared serial) = .fresh ∧
      bobCorrectiveResponse bit (control.execution.observe nativeApp bob) =
        bobCorrection serial bit := by
  have recall := native_bob_binding_recall control trace active granted
  have rawTrace := nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler trace
  have recorded := nativeRuntime.candidateRecall_history nativeLeaks (FinDist.pure nativeInputs)
    nativeHorizon nativeScheduler (state := some control)
    (by rw [FinDist.map_pure]; exact rawTrace)
  obtain ⟨serial, bound, allocated⟩ := nativeRuntime.reactiveFreshSlot_le_recall nativeLeaks
    control.execution bob recorded
  have bounded : serial < 2 := by omega
  refine ⟨serial, bounded, reactiveFreshSlot_spec _ serial allocated, ?_⟩
  simp only [bobCorrectiveResponse, allocated, ite_eq_left bounded]

theorem bob_correction_selected (execution : nativeApp.Execution) (serial : Nat) (bit : Bool)
    (serials : execution.network.SerialsBeforeNext) :
    nativeRuntime.reactiveLatest nativeLeaks bobBinding bob
      ((execution.respond nativeApp bob (bobCorrection serial bit)).observeEnvironment nativeApp) =
        .include (bob, execution.network.nextSerial bob) :=
  nativeRuntime.reactiveLatest_after_submit nativeLeaks bob bobBinding execution serials
    ⟨⟨.commitment bobBinding (bob, .prepared serial), some ⟨.bool, bit⟩⟩, .none⟩ rfl

theorem bob_correction_realizes (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (serial : Nat) (bit : Bool)
    (valid : execution.application.BindingInvariant)
    (serials : execution.network.SerialsBeforeNext)
    (fresh : execution.application.candidates.lookup (bob, .prepared serial) = .fresh)
    (ready : execution.application.config.cut.Ready bobBinding)
    (timely : execution.application.WithinDeadline nativeRuntime bobBinding) :
    ∃ next, bobBindingRef.get? next.config.store = some (.success bit) ∧
      (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest bobBinding bob)
        (execution.respond nativeApp bob (bobCorrection serial bit))).map
          (fun result => result.application) = FinDist.pure next := by
  let submitted := execution.respond nativeApp bob (bobCorrection serial bit)
  have facts := nativeRuntime.reactive_respond_application nativeLeaks execution bob
    (bobCorrection serial bit)
  have configEq : submitted.application.config = execution.application.config := facts.1
  have publicEq : submitted.application.publicView = execution.application.publicView := facts.2
  have acceptedEq : submitted.application.accepted = execution.application.accepted :=
    congrArg PublicView.accepted publicEq
  have readyAfter : submitted.application.config.cut.Ready bobBinding := by rwa [configEq]
  have timelyAfter : submitted.application.WithinDeadline nativeRuntime bobBinding := by
    change (match submitted.application.publicView.activatedAt bobBinding with
      | none => False
      | some entered => submitted.application.publicView.clock - entered <
          nativeRuntime.deadline bobBinding)
    rw [publicEq]
    exact timely
  have vacant : submitted.application.accepted (.inr bobBinding) = none := by
    rw [acceptedEq]
    cases associated : execution.application.accepted (.inr bobBinding) with
    | none => rfl
    | some candidate => exact False.elim (ready.1
        (valid.toAssociationInvariant.accepted_complete bobBinding candidate associated))
  have unused : submitted.application.HandleUnused (bob, .prepared serial) := by
    intro field associated
    rw [acceptedEq] at associated
    exact valid.accepted_fixed field _ associated fresh
  have meaning := nativeRuntime.reactiveBinding_result nativeLeaks bob bobBinding .bool
    (.success bit) serial execution fresh
  change submitted.application.bindingResult (bob, .prepared serial) .bool = .success bit
    at meaning
  have accepted := nativeRuntime.handle_commitment_eq submitted.application
    (bob, execution.network.nextSerial bob) bobBinding (bob, .prepared serial) bob .bool
    rfl rfl rfl readyAfter timelyAfter rfl rfl vacant unused
  refine ⟨(handle nativeRuntime submitted.application
    ⟨(bob, execution.network.nextSerial bob),
      .commitment bobBinding (bob, .prepared serial)⟩).getD submitted.application, ?_, ?_⟩
  · rw [accepted]
    simp [bobBindingRef, State.complete, EventGraph.Config.store, EventGraph.FieldRef.get?, meaning]
  · have found : submitted.network.lookup (bob, execution.network.nextSerial bob) =
        some ⟨(bob, execution.network.nextSerial bob),
          ⟨.commitment bobBinding (bob, .prepared serial), none⟩⟩ := serials.lookup_submit bob _
    simp only [interactionStep, interactionInstruction,
      bob_correction_selected execution serial bit serials, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
      ReactiveApplication.resume, FinDist.map_pure]
    change FinDist.pure (submitted.includePending nativeApp
      (bob, execution.network.nextSerial bob)).application = _
    unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
    rw [found]
    change FinDist.pure ((handle nativeRuntime submitted.application
      ⟨(bob, execution.network.nextSerial bob),
        .commitment bobBinding (bob, .prepared serial)⟩).getD submitted.application) = _
    rfl

/-- The actual correction is feasible at every legal Bob binding decision,
including after an arbitrary first response. No extra candidate is assumed. -/
theorem bob_corrective_response_realizes (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (active : control.actor = some bob)
    (granted : control.execution.application.serviceGrant = some bobBinding)
    (unfinished : bobBinding ∉ control.execution.application.config.cut.completed) (bit : Bool) :
    ∃ next, bobBindingRef.get? next.config.store = some (.success bit) ∧
      (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest bobBinding bob)
        (control.execution.respond nativeApp bob
          (bobCorrectiveResponse bit (control.execution.observe nativeApp bob)))).map
            (fun result => result.application) = FinDist.pure next := by
  have position := (native_decision_cursor bobBinding control trace bob active granted).2
  obtain ⟨_, service⟩ := native_decision_service bobBinding control trace active position
  obtain ⟨ready, timely⟩ := service.resolve_left unfinished
  obtain ⟨valid, _, serials⟩ := native_history_invariants control trace
  obtain ⟨serial, _, fresh, response⟩ := bob_correction_fresh control trace active granted bit
  rw [response]
  exact bob_correction_realizes players control.execution serial bit valid serials fresh
    ready timely

end VegasTests.SelectiveAssociation
