/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationService

/-! # The concrete execution prefix ending at Bob's response -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeRecord (before after : nativeApp.Execution) (command : nativeApp.Command) :
    nativeApp.Execution :=
  { after with environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, command⟩] }

def nativeActivate (execution : nativeApp.Execution) (who : Bool) : nativeApp.Execution :=
  nativeRecord execution execution (.activate who)

def nativeGrant (execution : nativeApp.Execution) (event : nativeGraph.EventId) :
    nativeApp.Execution :=
  nativeRecord execution { execution with
    application := { execution.application with serviceGrant := some event } }
    (.application (.grant event))

def nativeInclude (execution : nativeApp.Execution) (id : MessageId Bool) :
    nativeApp.Execution :=
  nativeRecord execution (execution.includePending nativeApp id) (.include id)

theorem native_activate_law (execution : nativeApp.Execution) (who : Bool) :
    execution.environmentStep nativeApp (.activate who) =
      FinDist.pure (nativeActivate execution who) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, FinDist.map_pure, MessageNetwork.learn_empty]
  rfl

theorem native_grant_law (execution : nativeApp.Execution) (event : nativeGraph.EventId) :
    execution.environmentStep nativeApp (.application (.grant event)) =
      FinDist.pure (nativeGrant execution event) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    environmentStep, FinDist.map_pure]
  rfl

theorem native_include_law (execution : nativeApp.Execution) (id : MessageId Bool) :
    execution.environmentStep nativeApp (.include id) =
      FinDist.pure (nativeInclude execution id) := by
  rw [ReactiveApplication.Execution.environmentStep, FinDist.map_pure]
  rfl

def nativeWindow (execution : nativeApp.Execution) (event : nativeGraph.EventId)
    (who : Bool) (submission : Submission nativeGraph) : nativeApp.Execution :=
  nativeInclude ((nativeActivate (nativeGrant execution event) who).respond nativeApp who
    ⟨some (.submit submission)⟩) (who, execution.network.nextSerial who)

theorem native_window_application (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool) (submission : Submission nativeGraph)
    (next : State nativeGraph) (empty : execution.network.pending = [])
    (accepted : nativeSubmit { execution.application with serviceGrant := some event }
      who (execution.network.nextSerial who) submission = some next) :
    (nativeWindow execution event who submission).application = next := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeGrant, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  change (nativeSubmit { execution.application with serviceGrant := some event }
    who (execution.network.nextSerial who) submission).getD _ = next
  rw [accepted]
  rfl

theorem native_window_pending (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool) (submission : Submission nativeGraph)
    (empty : execution.network.pending = []) :
    (nativeWindow execution event who submission).network.pending = [] := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeGrant, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  simp [MessagePool.removeFirst]

theorem native_window_serial (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who observer : Bool) (submission : Submission nativeGraph)
    (empty : execution.network.pending = []) :
    (nativeWindow execution event who submission).network.nextSerial observer =
      if observer = who then execution.network.nextSerial who + 1
      else execution.network.nextSerial observer := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeGrant, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]

theorem native_window_ledger (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool) (submission : Submission nativeGraph)
    (empty : execution.network.pending = []) :
    (nativeWindow execution event who submission).network.ledger =
      execution.network.ledger ++
        [⟨(who, execution.network.nextSerial who), submission.packet⟩] := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeGrant, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  rfl

theorem native_window_receipts (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool) (submission : Submission nativeGraph)
    (next : State nativeGraph) (empty : execution.network.pending = [])
    (accepted : nativeSubmit { execution.application with serviceGrant := some event }
      who (execution.network.nextSerial who) submission = some next) :
    (nativeWindow execution event who submission).receipts =
      execution.receipts ++ [((who, execution.network.nextSerial who), true)] := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeGrant, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  change execution.receipts ++ [(_, (nativeSubmit _ _ _ _).isSome)] = _
  rw [accepted]
  rfl

theorem native_window_length (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who : Bool) (submission : Submission nativeGraph) :
    (nativeWindow execution event who submission).environmentRecall.length =
      execution.environmentRecall.length + 3 := by
  change (((nativeActivate (nativeGrant execution event) who).respond nativeApp who
    ⟨some (.submit submission)⟩).environmentRecall ++ [_]).length = _
  rw [nativeApp.respond_environmentRecall]
  simp [nativeActivate, nativeGrant, nativeRecord]

theorem native_window_recall_other (execution : nativeApp.Execution)
    (event : nativeGraph.EventId) (who observer : Bool) (submission : Submission nativeGraph)
    (different : observer ≠ who) (empty : execution.network.pending = []) :
    (nativeWindow execution event who submission).recall observer = execution.recall observer := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeGrant, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true,
    ite_eq_right different]

def nativeInitialExecution (bit : Bool) : nativeApp.Execution :=
  .initial nativeApp (nativeStart bit)

def nativeFirst (bit : Bool) : nativeApp.Execution :=
  nativeWindow (nativeInitialExecution bit) bindingEvent false dummySubmission

def nativeSecond (bit : Bool) : nativeApp.Execution :=
  nativeWindow (nativeFirst bit) dummyEvent false dummyOpening

def nativeThird (bit : Bool) : nativeApp.Execution :=
  nativeWindow (nativeSecond bit) secretEvent false (secretOpening bit)

def nativeBobExecution (bit : Bool) : nativeApp.Execution :=
  nativeActivate (nativeGrant (nativeThird bit) guessEvent) true

theorem native_binding_grant (bit : Bool) (grant : Option nativeGraph.EventId) :
    nativeSubmit { nativeStart bit with serviceGrant := grant } false 0 dummySubmission =
      some { nativeBoundState bit with serviceGrant := grant } := by
  unfold nativeSubmit
  rw [handle_submitStep]
  change handle nativeRuntime { nativeRegistered bit with serviceGrant := grant }
    ⟨(false, 0), dummySubmission.packet⟩ = _
  rw [handle_serviceGrant_update]
  have accepted := native_binding_law bit
  unfold nativeSubmit at accepted
  rw [handle_submitStep] at accepted
  change handle nativeRuntime (nativeRegistered bit) ⟨(false, 0), dummySubmission.packet⟩ =
    some (nativeBoundState bit) at accepted
  rw [accepted]
  rfl

theorem native_dummy_grant (bit : Bool) (grant : Option nativeGraph.EventId) :
    nativeSubmit { nativeBound bit with serviceGrant := grant } false 1 dummyOpening =
      some { nativeDummyState bit with serviceGrant := grant } := by
  unfold nativeSubmit
  rw [handle_submitStep]
  change handle nativeRuntime { nativeBound bit with serviceGrant := grant }
    ⟨(false, 1), dummyOpening.packet⟩ = _
  rw [handle_serviceGrant_update]
  have accepted := native_dummy_law bit
  unfold nativeSubmit at accepted
  rw [handle_submitStep] at accepted
  change handle nativeRuntime (nativeBound bit) ⟨(false, 1), dummyOpening.packet⟩ =
    some (nativeDummyState bit) at accepted
  rw [accepted]
  rfl

theorem native_secret_grant (bit : Bool) (grant : Option nativeGraph.EventId) :
    nativeSubmit { nativeDummyPublished bit with serviceGrant := grant } false 2
      (secretOpening bit) = some { nativeSecretState bit with serviceGrant := grant } := by
  unfold nativeSubmit
  rw [handle_submitStep]
  change handle nativeRuntime { nativeDummyPublished bit with serviceGrant := grant }
    ⟨(false, 2), (secretOpening bit).packet⟩ = _
  rw [handle_serviceGrant_update]
  have accepted := native_secret_law bit
  unfold nativeSubmit at accepted
  rw [handle_submitStep] at accepted
  change handle nativeRuntime (nativeDummyPublished bit) ⟨(false, 2), (secretOpening bit).packet⟩ =
    some (nativeSecretState bit) at accepted
  rw [accepted]
  rfl

theorem native_first_pending (bit : Bool) : (nativeFirst bit).network.pending = [] :=
  native_window_pending _ _ _ _ rfl

theorem native_second_pending (bit : Bool) : (nativeSecond bit).network.pending = [] :=
  native_window_pending _ _ _ _ (native_first_pending bit)

theorem native_third_pending (bit : Bool) : (nativeThird bit).network.pending = [] :=
  native_window_pending _ _ _ _ (native_second_pending bit)

theorem native_first_serial (bit : Bool) : (nativeFirst bit).network.nextSerial false = 1 := by
  rw [nativeFirst, native_window_serial _ _ _ _ _ rfl]
  rfl

theorem native_second_serial (bit : Bool) : (nativeSecond bit).network.nextSerial false = 2 := by
  rw [nativeSecond, native_window_serial _ _ _ _ _ (native_first_pending bit)]
  simp only [↓reduceIte, native_first_serial]

theorem native_first_application (bit : Bool) :
    (nativeFirst bit).application =
      { nativeBound bit with serviceGrant := some bindingEvent } := by
  rw [nativeBound_eq]
  exact native_window_application _ _ _ _ _ rfl (native_binding_grant bit _)

theorem native_second_application (bit : Bool) :
    (nativeSecond bit).application =
      { nativeDummyPublished bit with serviceGrant := some dummyEvent } := by
  rw [nativeDummyPublished_eq]
  apply native_window_application _ _ _ _ _ (native_first_pending bit)
  rw [native_first_application, native_first_serial]
  exact native_dummy_grant bit _

theorem native_third_application (bit : Bool) :
    (nativeThird bit).application =
      { nativeSecretPublished bit with serviceGrant := some secretEvent } := by
  rw [nativeSecretPublished_eq]
  apply native_window_application _ _ _ _ _ (native_second_pending bit)
  rw [native_second_application, native_second_serial]
  exact native_secret_grant bit _

theorem native_bob_application (bit : Bool) :
    (nativeBobExecution bit).application =
      { nativeSecretPublished bit with serviceGrant := some guessEvent } := by
  change { (nativeThird bit).application with serviceGrant := some guessEvent } = _
  rw [native_third_application]

theorem native_bob_ledger (bit : Bool) : (nativeBobExecution bit).network.ledger =
    [⟨(false, 0), dummySubmission.packet⟩, ⟨(false, 1), dummyOpening.packet⟩,
      ⟨(false, 2), (secretOpening bit).packet⟩] := by
  change (nativeThird bit).network.ledger = _
  rw [nativeThird, native_window_ledger _ _ _ _ (native_second_pending bit), native_second_serial]
  rw [nativeSecond, native_window_ledger _ _ _ _ (native_first_pending bit), native_first_serial]
  rw [nativeFirst, native_window_ledger _ _ _ _ rfl]
  rfl

theorem native_bob_recall (bit : Bool) : (nativeBobExecution bit).recall true = [] := by
  change (nativeThird bit).recall true = _
  rw [nativeThird, native_window_recall_other _ _ _ _ _ (by decide) (native_second_pending bit)]
  rw [nativeSecond, native_window_recall_other _ _ _ _ _ (by decide) (native_first_pending bit)]
  rw [nativeFirst, native_window_recall_other _ _ _ _ _ (by decide) rfl]
  rfl

theorem native_bob_position (bit : Bool) :
    (nativeBobExecution bit).environmentRecall.length = 11 := by
  change ((nativeThird bit).environmentRecall ++ [_] ++ [_]).length = _
  simp only [List.length_append, List.length_singleton]
  rw [nativeThird, native_window_length, nativeSecond, native_window_length,
    nativeFirst, native_window_length]
  rfl

end VegasTests.SequentialValidation
