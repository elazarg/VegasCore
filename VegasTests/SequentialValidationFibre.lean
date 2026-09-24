/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SequentialValidationHistory
import Vegas.Pending.ReactiveObservedState

/-! # The actual native information set following authenticated disclosure -/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem native_first_receipts (bit : Bool) : (nativeFirst bit).receipts = [((false, 0), true)] := by
  rw [nativeFirst, native_window_receipts _ _ _ _ _ rfl (native_binding_grant bit _)]
  rfl

theorem native_second_receipts (bit : Bool) :
    (nativeSecond bit).receipts = [((false, 0), true), ((false, 1), true)] := by
  have accepted : nativeSubmit
      { (nativeFirst bit).application with serviceGrant := some dummyEvent }
      false ((nativeFirst bit).network.nextSerial false) dummyOpening =
        some { nativeDummyState bit with serviceGrant := some dummyEvent } := by
    rw [native_first_application, native_first_serial]
    exact native_dummy_grant bit _
  rw [nativeSecond, native_window_receipts _ _ _ _ _ (native_first_pending bit) accepted,
    native_first_receipts, native_first_serial]
  rfl

theorem native_bob_receipts (bit : Bool) : (nativeBobExecution bit).receipts =
    [((false, 0), true), ((false, 1), true), ((false, 2), true)] := by
  have accepted : nativeSubmit
      { (nativeSecond bit).application with serviceGrant := some secretEvent }
      false ((nativeSecond bit).network.nextSerial false) (secretOpening bit) =
        some { nativeSecretState bit with serviceGrant := some secretEvent } := by
    rw [native_second_application, native_second_serial]
    exact native_secret_grant bit _
  simp only [nativeBobExecution, nativeActivate, nativeGrant, nativeRecord]
  rw [nativeThird, native_window_receipts _ _ _ _ _ (native_second_pending bit) accepted,
    native_second_receipts, native_second_serial]
  rfl

theorem native_bob_observed (bit : Bool) : nativeRuntime.openingObserved nativeLeaks
    ((nativeBobExecution bit).observe nativeApp true)
    (false, .initial secretInput) ⟨.bool, bit⟩ := by
  have observed (execution : nativeApp.Execution)
      (ledger : execution.network.ledger =
        [⟨(false, 0), dummySubmission.packet⟩, ⟨(false, 1), dummyOpening.packet⟩,
          ⟨(false, 2), (secretOpening bit).packet⟩])
      (receipts : execution.receipts =
        [((false, 0), true), ((false, 1), true), ((false, 2), true)]) :
      nativeRuntime.openingObserved nativeLeaks (execution.observe nativeApp true)
        (false, .initial secretInput) ⟨.bool, bit⟩ := by
    refine ⟨secretEvent, (false, 2), ?_⟩
    change _ ∈ execution.network.ledger.zip execution.receipts
    rw [ledger, receipts]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_singleton_self _))
  exact observed _ (native_bob_ledger bit) (native_bob_receipts bit)

theorem native_info (who : Bool) (history : nativeArena.History) :
    nativeModel.infoOf who history.trace = nativeApp.observe who history.state :=
  nativeMenu.info nativeInitialLaw 56 nativeScheduler who history.trace

theorem native_bob_info (bit : Bool) : (nativeBobSite bit).1 =
    some ([], (nativeBobExecution bit).observe nativeApp true) := by
  change nativeModel.infoOf true (nativeBobHistory bit).trace = _
  rw [native_info]
  change some ((nativeBobExecution bit).recall true, _) = _
  rw [native_bob_recall]

theorem native_bob_fibre (bit : Bool)
    (history : nativeModel.InformationHistory true (nativeBobSite bit).1) :
    ∃ execution, history.1.state = some ⟨45, some true, execution⟩ ∧
      execution.environmentRecall.length = 11 ∧ execution.recall true = [] ∧
      execution.observe nativeApp true = (nativeBobExecution bit).observe nativeApp true := by
  have observed := history.2.trans (native_bob_info bit)
  rw [native_info] at observed
  cases state : history.1.state with
  | none => rw [state] at observed; cases observed
  | some control =>
      rw [state] at observed
      change (if control.actor = some true then some
        (control.execution.recall true, control.execution.observe nativeApp true) else none) = _
        at observed
      split at observed
      · rename_i active
        have trace := state ▸ history.1.trace
        have position := native_bob_remaining control trace active
        have same := Option.some.inj observed
        refine ⟨control.execution, ?_, position.1, congrArg Prod.fst same,
          congrArg Prod.snd same⟩
        rcases control with ⟨remaining, actor, execution⟩
        simp_all only
      · cases observed

theorem native_bob_type (bit : Bool)
    (history : nativeModel.InformationHistory true (nativeBobSite bit).1) :
    nativeStoredType nativeLeaks history.1.state = some bit := by
  have same := native_bob_info bit
  exact native_information_type nativeLeaks nativeMenu 56 nativeScheduler true bit []
    ((nativeBobExecution bit).observe nativeApp true) (native_bob_observed bit)
    ⟨history.1, history.2.trans same⟩

theorem native_no_bob_pending (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) (empty : control.execution.recall true = [])
    (message : Message Bool (Payload nativeGraph))
    (pending : message ∈ control.execution.network.pending) : message.sender ≠ true := by
  have valid := nativeApp.history_provenance nativeInitialLaw 56 nativeScheduler
    (nativeMenu.toRawTrace nativeInitialLaw 56 nativeScheduler trace)
  obtain ⟨entry, member, _⟩ := valid.pending message pending
  intro same
  rw [same, empty] at member
  exact List.not_mem_nil member

theorem native_remembered (control : nativeApp.Control)
    (trace : nativeArena.Trace (some control)) :
    control.execution.application.remembered = fun _ => none := by
  apply (nativeRuntime.reactiveRememberedInvariant nativeLeaks (fun _ => none)).history
    nativeInitialLaw 56 nativeScheduler _
    (nativeMenu.toRawTrace nativeInitialLaw 56 nativeScheduler trace)
  intro state supported
  obtain ⟨bit, _, rfl⟩ := FinDist.support_map .. ▸ supported
  rfl

end VegasTests.SequentialValidation
