/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SequentialValidation.Service

/-! # The concrete execution prefix ending at Bob's response -/

noncomputable section

namespace Vegas.Examples.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def nativeRecord (before after : nativeApp.Execution) (command : nativeApp.Command) :
    nativeApp.Execution :=
  { after with environmentRecall := before.environmentRecall ++
      [⟨before.observeEnvironment nativeApp, command⟩] }

def nativeActivate (execution : nativeApp.Execution) (who : Bool) : nativeApp.Execution :=
  nativeRecord execution execution (.activate who)

def nativeInclude (execution : nativeApp.Execution) (id : MessageId Bool) :
    nativeApp.Execution :=
  nativeRecord execution (execution.includePending nativeApp id) (.include id)

theorem native_activate_law (execution : nativeApp.Execution) (who : Bool) :
    execution.environmentStep nativeApp (.activate who) =
      PMF.pure (nativeActivate execution who) := by
  simp only [ReactiveApplication.Execution.environmentStep, nativeApp, reactiveApplication,
    nativeLeaks, PMF.pure_map, MessageNetwork.learn_empty]
  rfl

theorem native_include_law (execution : nativeApp.Execution) (id : MessageId Bool) :
    execution.environmentStep nativeApp (.include id) =
      PMF.pure (nativeInclude execution id) := by
  rw [ReactiveApplication.Execution.environmentStep, PMF.pure_map]
  rfl

def nativeWindow (execution : nativeApp.Execution) (who : Bool)
    (submission : Submission nativeGraph) : nativeApp.Execution :=
  nativeInclude ((nativeActivate execution who).respond nativeApp who
    ⟨some ⟨submission, .none⟩⟩) (who, execution.network.nextSerial who)

theorem native_window_application (execution : nativeApp.Execution)
    (who : Bool) (submission : Submission nativeGraph)
    (next : EventGraphRuntime.State nativeGraph) (empty : execution.network.pending = [])
    (accepted : nativeSubmit execution.application
      who (execution.network.nextSerial who) submission = some next) :
    (nativeWindow execution who submission).application = next := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  have valid : (WitnessedPacket.mk submission.packet none
      ((nativeApp.submit execution.application who ⟨submission, .none⟩).publicView.tokenFor
        submission.packet)).tokenValid = true :=
    tokenFor_tokenValid_of_handle nativeRuntime _ next _ submission.packet none accepted
  rw [reactiveApplication_packet_none]
  rw [reactiveApplication_submit_publicView] at valid
  rw [show nativeApp.handle (nativeApp.submit execution.application who ⟨submission, .none⟩)
      ⟨(who, execution.network.nextSerial who), ⟨submission.packet, none,
        execution.application.publicView.tokenFor submission.packet⟩⟩ = some next from
    (reactiveApplication_handle_of_tokenValid nativeRuntime nativeLeaks _ _ valid).trans accepted]
  rfl

theorem native_window_pending (execution : nativeApp.Execution)
    (who : Bool) (submission : Submission nativeGraph)
    (empty : execution.network.pending = []) :
    (nativeWindow execution who submission).network.pending = [] := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  simp [MessagePool.removeFirst]

theorem native_window_serial (execution : nativeApp.Execution)
    (who observer : Bool) (submission : Submission nativeGraph)
    (empty : execution.network.pending = []) :
    (nativeWindow execution who submission).network.nextSerial observer =
      if observer = who then execution.network.nextSerial who + 1
      else execution.network.nextSerial observer := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]

theorem native_window_ledger (execution : nativeApp.Execution)
    (who : Bool) (submission : Submission nativeGraph)
    (empty : execution.network.pending = []) :
    (nativeWindow execution who submission).network.ledger =
      execution.network.ledger ++
        [⟨(who, execution.network.nextSerial who), ⟨submission.packet, none,
          execution.application.publicView.tokenFor submission.packet⟩⟩] := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  rw [reactiveApplication_packet_none]

theorem native_window_receipts (execution : nativeApp.Execution)
    (who : Bool) (submission : Submission nativeGraph)
    (next : EventGraphRuntime.State nativeGraph) (empty : execution.network.pending = [])
    (accepted : nativeSubmit execution.application
      who (execution.network.nextSerial who) submission = some next) :
    (nativeWindow execution who submission).receipts =
      execution.receipts ++ [((who, execution.network.nextSerial who), true)] := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true]
  have valid : (WitnessedPacket.mk submission.packet none
      ((nativeApp.submit execution.application who ⟨submission, .none⟩).publicView.tokenFor
        submission.packet)).tokenValid = true :=
    tokenFor_tokenValid_of_handle nativeRuntime _ next _ submission.packet none accepted
  rw [reactiveApplication_packet_none]
  rw [reactiveApplication_submit_publicView] at valid
  rw [show nativeApp.handle (nativeApp.submit execution.application who ⟨submission, .none⟩)
      ⟨(who, execution.network.nextSerial who), ⟨submission.packet, none,
        execution.application.publicView.tokenFor submission.packet⟩⟩ = some next from
    (reactiveApplication_handle_of_tokenValid nativeRuntime nativeLeaks _ _ valid).trans accepted]
  rfl

theorem native_window_length (execution : nativeApp.Execution)
    (who : Bool) (submission : Submission nativeGraph) :
    (nativeWindow execution who submission).environmentRecall.length =
      execution.environmentRecall.length + 2 := by
  change (((nativeActivate execution who).respond nativeApp who
    ⟨some ⟨submission, .none⟩⟩).environmentRecall ++ [_]).length = _
  rw [nativeApp.respond_environmentRecall]
  simp [nativeActivate, nativeRecord]

theorem native_window_recall_other (execution : nativeApp.Execution)
    (who observer : Bool) (submission : Submission nativeGraph)
    (different : observer ≠ who) (empty : execution.network.pending = []) :
    (nativeWindow execution who submission).recall observer = execution.recall observer := by
  simp only [nativeWindow, nativeInclude, nativeActivate, nativeRecord,
    ReactiveApplication.Execution.respond, MessageNetwork.submit,
    ReactiveApplication.Execution.includePending, MessageNetwork.includePending,
    MessageNetwork.lookup, empty, List.nil_append, List.find?_cons, decide_true,
    ite_eq_right different]

def nativeInitialExecution (bit : Bool) : nativeApp.Execution :=
  .initial nativeApp (nativeStart bit)

def nativeFirst (bit : Bool) : nativeApp.Execution :=
  nativeWindow (nativeInitialExecution bit) false dummySubmission

def nativeSecond (bit : Bool) : nativeApp.Execution :=
  nativeWindow (nativeFirst bit) false dummyOpening

def nativeThird (bit : Bool) : nativeApp.Execution :=
  nativeWindow (nativeSecond bit) false (secretOpening bit)

def nativeBobExecution (bit : Bool) : nativeApp.Execution :=
  nativeActivate (nativeThird bit) true

theorem native_first_pending (bit : Bool) : (nativeFirst bit).network.pending = [] :=
  native_window_pending _ _ _ rfl

theorem native_second_pending (bit : Bool) : (nativeSecond bit).network.pending = [] :=
  native_window_pending _ _ _ (native_first_pending bit)

theorem native_third_pending (bit : Bool) : (nativeThird bit).network.pending = [] :=
  native_window_pending _ _ _ (native_second_pending bit)

theorem native_first_serial (bit : Bool) : (nativeFirst bit).network.nextSerial false = 1 := by
  rw [nativeFirst, native_window_serial _ _ _ _ rfl]
  rfl

theorem native_second_serial (bit : Bool) : (nativeSecond bit).network.nextSerial false = 2 := by
  rw [nativeSecond, native_window_serial _ _ _ _ (native_first_pending bit)]
  simp only [↓reduceIte, native_first_serial]

theorem native_first_application (bit : Bool) :
    (nativeFirst bit).application = nativeBound bit := by
  rw [nativeBound_eq]
  exact native_window_application _ _ _ _ rfl (native_binding_law bit)

theorem native_second_application (bit : Bool) :
    (nativeSecond bit).application = nativeDummyPublished bit := by
  rw [nativeDummyPublished_eq]
  apply native_window_application _ _ _ _ (native_first_pending bit)
  rw [native_first_application, native_first_serial]
  exact native_dummy_law bit

theorem native_third_application (bit : Bool) :
    (nativeThird bit).application = nativeSecretPublished bit := by
  rw [nativeSecretPublished_eq]
  apply native_window_application _ _ _ _ (native_second_pending bit)
  rw [native_second_application, native_second_serial]
  exact native_secret_law bit

theorem native_bob_application (bit : Bool) :
    (nativeBobExecution bit).application = nativeSecretPublished bit := by
  unfold nativeBobExecution nativeActivate nativeRecord
  exact native_third_application bit

theorem native_bob_ledger (bit : Bool) : (nativeBobExecution bit).network.ledger =
    [⟨(false, 0), ⟨dummySubmission.packet, none, some ⟨bindingEvent⟩⟩⟩,
      ⟨(false, 1), ⟨dummyOpening.packet, none, some ⟨dummyEvent⟩⟩⟩,
      ⟨(false, 2), ⟨(secretOpening bit).packet, none, some ⟨secretEvent⟩⟩⟩] := by
  change (nativeThird bit).network.ledger = _
  rw [nativeThird, native_window_ledger _ _ _ (native_second_pending bit), native_second_serial]
  rw [nativeSecond, native_window_ledger _ _ _ (native_first_pending bit), native_first_serial]
  rw [nativeFirst, native_window_ledger _ _ _ rfl]
  have first : (nativeInitialExecution bit).application.config.cut.Ready bindingEvent :=
    native_registered_ready bit
  have second : (nativeFirst bit).application.config.cut.Ready dummyEvent := by
    rw [native_first_application]
    exact native_bound_ready bit
  have third : (nativeSecond bit).application.config.cut.Ready secretEvent := by
    rw [native_second_application]
    exact native_dummy_ready bit
  change (nativeInitialExecution bit).network.ledger ++ [⟨_, ⟨_, none,
      (nativeInitialExecution bit).application.publicView.tokenFor _⟩⟩] ++
    [⟨_, ⟨_, none, (nativeFirst bit).application.publicView.tokenFor _⟩⟩] ++
    [⟨_, ⟨_, none, (nativeSecond bit).application.publicView.tokenFor _⟩⟩] = _
  rw [State.publicView_tokenFor_of_ready _ _ _ rfl first,
    State.publicView_tokenFor_of_ready _ _ _ rfl second,
    State.publicView_tokenFor_of_ready _ _ _ rfl third]
  rfl

theorem native_bob_recall (bit : Bool) : (nativeBobExecution bit).recall true = [] := by
  change (nativeThird bit).recall true = _
  rw [nativeThird, native_window_recall_other _ _ _ _ (by decide) (native_second_pending bit)]
  rw [nativeSecond, native_window_recall_other _ _ _ _ (by decide) (native_first_pending bit)]
  rw [nativeFirst, native_window_recall_other _ _ _ _ (by decide) rfl]
  rfl

theorem native_bob_position (bit : Bool) :
    (nativeBobExecution bit).environmentRecall.length = 7 := by
  change ((nativeThird bit).environmentRecall ++ [_]).length = _
  simp only [List.length_append, List.length_singleton]
  rw [nativeThird, native_window_length, nativeSecond, native_window_length,
    nativeFirst, native_window_length]
  rfl

end Vegas.Examples.SequentialValidation
