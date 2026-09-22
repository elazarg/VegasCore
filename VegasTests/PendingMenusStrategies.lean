/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.PendingMenus
import GameTheoryExtensions.Protocol.BehavioralContinuation
import Mathlib.Tactic.IntervalCases

/-! # Public outcomes attainable by native continuation policies

The two policies use only the public service grant. Sending an opening at the
contested binding grant selects the first pending commitment; waiting selects
the second. At the disclosure grant each policy submits the corresponding
opening. The reserved inclusion publishes that value.
-/

noncomputable section

namespace VegasTests.PendingMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

def preferredValue (preferOne : Bool) : Int := if preferOne then 1 else 2
def preferredSlot (preferOne : Bool) : Nat := if preferOne then 0 else 1

def openingPacket (preferOne : Bool) : Payload graph :=
  .opening 1 ((), .prepared (preferredSlot preferOne)) ⟨.int, preferredValue preferOne⟩

def openingAction (preferOne : Bool) : PlayerAction graph :=
  ⟨[], some (.submit ⟨openingPacket preferOne, none⟩)⟩

/-- No service cursor or hidden state is consulted. -/
def recoveryPolicy (preferOne : Bool) : NativePolicy graph := fun _ view =>
  FinDist.pure (if preferOne || view.publicView.serviceGrant == some 1 then
    openingAction preferOne else PlayerAction.wait)

def selectionAction (preferOne : Bool) : PlayerAction graph :=
  if preferOne then openingAction preferOne else PlayerAction.wait

theorem recovery_at_root (preferOne : Bool) :
    recoveryPolicy preferOne (contested.principalHistory ())
      (runtime.nativeView contested.native ()) = FinDist.pure (selectionAction preferOne) := by
  cases preferOne <;> rfl

theorem recovery_selects (preferOne : Bool) :
    selected (selectionAction preferOne) = preferredSlot preferOne ∧
      selectedValue (selectionAction preferOne) = preferredValue preferOne := by
  cases preferOne <;> exact ⟨rfl, rfl⟩

/-- Expected environment record after a deterministic instruction. These
snapshots are checked against the actual native instruction kernel below. -/
private def environmentRecord (execution : NativeExecution runtime)
    (command : app.EnvironmentPolicyCommand) (native : app.State) : NativeExecution runtime :=
  { execution with native := native, environmentHistory := execution.environmentHistory ++
      [⟨MessageApplication.State.environmentView app execution.native, command⟩] }

private def includedExecution (execution : NativeExecution runtime) (serial : Nat) :=
  environmentRecord execution (.include ((), serial))
    (app.includePending execution.native ((), serial))

private def grantedExecution (execution : NativeExecution runtime) (event : graph.EventId) :=
  environmentRecord execution (.application (.grant event))
    { execution.native with application := { execution.native.application with
      serviceGrant := some event } }

private def sampledExecution (execution : NativeExecution runtime) (event : graph.EventId) :=
  environmentRecord execution (.application (.executeSample event)) execution.native

/-- The ten expected snapshots up to successful reserved disclosure. -/
private def snapshot (preferOne : Bool) : Nat → NativeExecution runtime
  | 0 => contested
  | 1 => afterAction (selectionAction preferOne)
  | 2 => includedExecution (snapshot preferOne 1) (preferredSlot preferOne)
  | 3 => includedExecution (snapshot preferOne 2) (if preferOne then 1 else 0)
  | 4 => sampledExecution (snapshot preferOne 3) 0
  | 5 => grantedExecution (snapshot preferOne 4) 1
  | 6 => runtime.takeAction () (snapshot preferOne 5) (openingAction preferOne)
  | 7 => runtime.takeAction () (snapshot preferOne 6) (openingAction preferOne)
  | 8 => runtime.takeAction () (snapshot preferOne 7) (openingAction preferOne)
  | 9 => includedExecution (snapshot preferOne 8) 0
  | _ + 10 => includedExecution (snapshot preferOne 9) (if preferOne then 5 else 4)
termination_by stage => stage
decreasing_by all_goals omega

private def control (preferOne : Bool) (stage : Nat) : NativeProtocolState runtime :=
  some ⟨5, (secondControl first second).plan.drop stage, snapshot preferOne stage⟩

def recoveryKernel (preferOne : Bool) : arena.State → FinDist arena.State :=
  runtime.nativeControlStep (FinDist.pure input) [] 1 (fun _ => recoveryPolicy preferOne)
    wire ordering

private theorem wire_includes (execution : NativeExecution runtime) (serial : Nat)
    (chosen : wire execution.environmentHistory
      (MessageApplication.State.environmentView app execution.native) =
        FinDist.pure (.include ((), serial))) :
    runtime.nativeInstructionStep wire .wire execution (fun _ => none) =
      FinDist.pure (includedExecution execution serial) := by
  simp only [nativeInstructionStep, serviceStep, MessageApplication.invoke,
    MessageApplication.wireEnvironment, NativeExecution.environmentExecution, chosen,
    FinDist.map_pure, FinDist.pure_bind, WireCommand.toEnvironmentCommand,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
  rfl

private theorem reserved_includes (execution : NativeExecution runtime) (event : graph.EventId)
    (serial : Nat)
    (chosen : runtime.latestEventSubmissionCommand event ()
      (MessageApplication.State.environmentView app execution.native) = .include ((), serial)) :
    runtime.nativeInstructionStep wire (.includeLatest event ()) execution (fun _ => none) =
      FinDist.pure (includedExecution execution serial) := by
  simp only [nativeInstructionStep, serviceStep, NativeExecution.environmentExecution, chosen,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

private theorem grant_step (execution : NativeExecution runtime) (event : graph.EventId) :
    runtime.nativeInstructionStep wire (.grant event) execution (fun _ => none) =
      FinDist.pure (grantedExecution execution event) := by
  simp only [nativeInstructionStep, serviceStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, application, environmentStep, FinDist.map_pure, FinDist.pure_bind]
  rfl

private theorem first_wire (preferOne : Bool) :
    wire (snapshot preferOne 1).environmentHistory
      (MessageApplication.State.environmentView app (snapshot preferOne 1).native) =
        FinDist.pure (.include ((), preferredSlot preferOne)) := by
  simp only [snapshot]
  cases preferOne <;> rfl

private theorem first_reserved (preferOne : Bool) :
    runtime.latestEventSubmissionCommand 0 ()
      (MessageApplication.State.environmentView app (snapshot preferOne 2).native) =
        .include ((), if preferOne then 1 else 0) := by
  unfold latestEventSubmissionCommand
  simp only [MessageApplication.State.environmentView, snapshot, includedExecution,
    environmentRecord, MessageApplication.includePending_pool]
  cases preferOne <;> rfl

private theorem second_wire (preferOne : Bool) :
    wire (snapshot preferOne 8).environmentHistory
      (MessageApplication.State.environmentView app (snapshot preferOne 8).native) =
        FinDist.pure (.include ((), 0)) := by
  unfold wire
  simp only [MessageApplication.State.environmentView, snapshot, includedExecution,
    grantedExecution, sampledExecution, environmentRecord, takeAction, transmit,
    openingAction, MessageApplication.includePending_pool]
  cases preferOne <;> rfl

private theorem second_reserved (preferOne : Bool) :
    runtime.latestEventSubmissionCommand 1 ()
      (MessageApplication.State.environmentView app (snapshot preferOne 9).native) =
        .include ((), if preferOne then 5 else 4) := by
  unfold latestEventSubmissionCommand
  simp only [MessageApplication.State.environmentView, snapshot, includedExecution,
    grantedExecution, sampledExecution, environmentRecord, takeAction, transmit,
    openingAction, MessageApplication.includePending_pool]
  cases preferOne <;> rfl

private theorem binding_ready (preferOne : Bool) :
    (snapshot preferOne 1).native.application.config.cut.Ready 0 := by
  simp only [snapshot]
  cases preferOne <;> decide

private def boundApplication (preferOne : Bool) : State graph :=
  let before := (snapshot preferOne 1).native.application
  let candidate := ((), Slot.prepared (preferredSlot preferOne))
  { (before.complete 0 (binding_ready preferOne)
      (.success (preferredValue preferOne)) (.success (preferredValue preferOne))) with
    accepted := Function.update before.accepted (.inr 0) (some candidate)
    candidates := before.candidates.freeze candidate }

private theorem binding_handler (preferOne : Bool) (serial : Nat) :
    handle runtime (snapshot preferOne 1).native.application
      ⟨((), serial), .commitment 0 ((), .prepared (preferredSlot preferOne))⟩ =
        some (boundApplication preferOne) := by
  have law := handle_commitment_eq runtime (snapshot preferOne 1).native.application
    ((), serial) 0 ((), .prepared (preferredSlot preferOne)) () .int rfl rfl rfl
    (binding_ready preferOne) (by
      simp only [snapshot]
      cases preferOne <;> change 0 < 2 <;> decide) rfl rfl
    (by simp only [snapshot]; cases preferOne <;> rfl) (by
      simp only [snapshot]
      intro field
      cases field with
      | inl index => exact Fin.elim0 index
      | inr event => cases preferOne <;> exact nofun)
  have value : (snapshot preferOne 1).native.application.bindingResult
      ((), .prepared (preferredSlot preferOne)) .int =
        PublicationResult.success (preferredValue preferOne) := by
    simp only [snapshot]
    cases preferOne <;> rfl
  simpa only [value, cast_eq, boundApplication] using law

private theorem bound_application (preferOne : Bool) :
    (snapshot preferOne 2).native.application = boundApplication preferOne := by
  have pending : (snapshot preferOne 1).native.pool.lookup ((), preferredSlot preferOne) =
      some ⟨((), preferredSlot preferOne),
        .commitment 0 ((), .prepared (preferredSlot preferOne))⟩ := by
    simp only [snapshot]
    cases preferOne <;> rfl
  have law := app.includePending_accept _ _ _ _ pending (binding_handler preferOne _)
  simpa only [snapshot, includedExecution, environmentRecord] using
    congrArg (fun state : app.State => state.application) law

private theorem bound_not_ready (preferOne : Bool) :
    ¬ (boundApplication preferOne).config.cut.Ready 0 := by
  intro ready
  apply ready.1
  change 0 ∈ insert 0 _
  exact Finset.mem_insert_self _ _

private theorem leftover_application (preferOne : Bool) :
    (snapshot preferOne 3).native.application = boundApplication preferOne := by
  have pending : (snapshot preferOne 2).native.pool.lookup ((), if preferOne then 1 else 0) =
      some ⟨((), if preferOne then 1 else 0),
        .commitment 0 ((), .prepared (if preferOne then 1 else 0))⟩ := by
    simp only [snapshot, includedExecution, environmentRecord,
      MessageApplication.includePending_pool]
    cases preferOne <;> rfl
  have rejected : handle runtime (snapshot preferOne 2).native.application
      ⟨((), if preferOne then 1 else 0),
        .commitment 0 ((), .prepared (if preferOne then 1 else 0))⟩ = none := by
    simp only [bound_application, handle, dite_eq_right (bound_not_ready preferOne)]
  have law := app.includePending_reject _ _ _ pending rejected
  have same := congrArg (fun state : app.State => state.application) law
  rw [snapshot]
  change (app.includePending (snapshot preferOne 2).native _).application = _
  exact same.trans (bound_application preferOne)

private def disclosureApplication (preferOne : Bool) : State graph :=
  { boundApplication preferOne with serviceGrant := some 1 }

private theorem disclosure_application (preferOne : Bool) :
    (snapshot preferOne 9).native.application = disclosureApplication preferOne := by
  have missing : (snapshot preferOne 8).native.pool.lookup ((), 0) = none := by
    simp only [snapshot, includedExecution, environmentRecord, grantedExecution,
      sampledExecution, takeAction, transmit, openingAction, MessageApplication.includePending_pool]
    cases preferOne <;> rfl
  have unchanged := app.includePending_missing _ _ missing
  rw [snapshot]
  change (app.includePending (snapshot preferOne 8).native ((), 0)).application = _
  rw [unchanged]
  have opened (execution : NativeExecution runtime) :
      (runtime.takeAction () execution (openingAction preferOne)).native.application =
        execution.native.application := rfl
  rw [snapshot, opened, snapshot, opened, snapshot, opened, snapshot, snapshot]
  change { (snapshot preferOne 3).native.application with serviceGrant := some 1 } = _
  rw [leftover_application]
  rfl

private theorem publication_ready (preferOne : Bool) :
    (disclosureApplication preferOne).config.cut.Ready 1 := by
  simp only [disclosureApplication, boundApplication, snapshot]
  cases preferOne <;> decide

private theorem publication_handler (preferOne : Bool) (serial : Nat) :
    handle runtime (snapshot preferOne 9).native.application
      ⟨((), serial), openingPacket preferOne⟩ =
        some ((disclosureApplication preferOne).complete 1 (publication_ready preferOne)
          true (.success (preferredValue preferOne))) := by
  rw [disclosure_application]
  apply handle_opening_eq runtime (disclosureApplication preferOne)
    ((), serial) 1 ((), .prepared (preferredSlot preferOne)) () .int binding [] rfl rfl rfl
    (publication_ready preferOne)
  · simp only [disclosureApplication, boundApplication, snapshot, State.WithinDeadline,
      State.complete]
    cases preferOne <;> change 0 < 2 <;> decide
  · rfl
  · rfl
  · simp only [disclosureApplication, boundApplication, Function.update_self]
  · simp only [disclosureApplication, boundApplication, snapshot]
    cases preferOne <;> rfl
  · exact EventGraph.Config.complete_output_same _ _ _ _ _
  · change EventGraph.EventCode.resolveOutput? binding [] true
      (disclosureApplication preferOne).config.store = _
    simp only [EventGraph.EventCode.resolveOutput?, EventGraph.FieldRef.get?,
      EventGraph.Config.store, disclosureApplication, boundApplication, State.complete,
      EventGraph.Config.complete_output_same, bind, Option.bind_some,
      EventGraph.GuardCheck.allAccepted?]
    rfl

/-- Both benchmarks are attained by successful publication, with no clock
advance or computational cost between the player invocations. -/
private theorem publication_snapshot (preferOne : Bool) :
    (snapshot preferOne 10).native.application.config.outputs 1 =
      some (.success (preferredValue preferOne)) := by
  have pending : (snapshot preferOne 9).native.pool.lookup ((), if preferOne then 5 else 4) =
      some ⟨((), if preferOne then 5 else 4), openingPacket preferOne⟩ := by
    simp only [snapshot, includedExecution, environmentRecord, grantedExecution,
      sampledExecution, takeAction, transmit, openingAction, MessageApplication.includePending_pool]
    cases preferOne <;> rfl
  have law := app.includePending_accept _ _ _ _ pending (publication_handler preferOne _)
  have output := congrArg (fun state : app.State => state.application.config.outputs 1) law
  rw [snapshot]
  exact output.trans (EventGraph.Config.complete_output_same _ _ _ _ _)

private theorem sample_step (execution : NativeExecution runtime)
    (notReady : ¬ execution.native.application.config.cut.Ready 0) :
    runtime.nativeInstructionStep wire (.sample 0) execution (fun _ => none) =
      FinDist.pure (sampledExecution execution 0) := by
  simp only [nativeInstructionStep, serviceStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, application, NativeExecution.environmentExecution,
    environmentStep_executeSample_of_not_ready runtime _ _ notReady,
    FinDist.map_pure, FinDist.pure_bind]
  rfl

private theorem recovery_at_disclosure (preferOne : Bool) (stage : Nat)
    (lower : 5 ≤ stage) (upper : stage ≤ 7) :
    recoveryPolicy preferOne ((snapshot preferOne stage).principalHistory ())
      (runtime.nativeView (snapshot preferOne stage).native ()) =
        FinDist.pure (openingAction preferOne) := by
  have grant : (runtime.nativeView (snapshot preferOne stage).native ()).publicView.serviceGrant =
      some 1 := by
    interval_cases stage <;> simp only [snapshot] <;> rfl
  simp only [recoveryPolicy, grant, beq_self_eq_true, Bool.or_true, ↓reduceIte]

private theorem recovery_step (preferOne : Bool) (stage : Nat) (early : stage < 10) :
    recoveryKernel preferOne (control preferOne stage) =
      FinDist.pure (control preferOne (stage + 1)) := by
  interval_cases stage
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 0)).map _ = _
    rw [snapshot, invokeNative, recovery_at_root, FinDist.pure_bind, actionStep,
      FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire .wire (snapshot preferOne 1)
      (fun _ => none)).map _ = _
    rw [wire_includes _ _ (first_wire preferOne), FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.includeLatest 0 ()) (snapshot preferOne 2)
      (fun _ => none)).map _ = _
    rw [reserved_includes _ _ _ (first_reserved preferOne), FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.sample 0) (snapshot preferOne 3)
      (fun _ => none)).map _ = _
    rw [sample_step _ (by rw [leftover_application]; exact bound_not_ready preferOne),
      FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.grant 1) (snapshot preferOne 4)
      (fun _ => none)).map _ = _
    rw [grant_step, FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 5)).map _ = _
    rw [invokeNative, recovery_at_disclosure preferOne 5 (by omega) (by omega),
      FinDist.pure_bind, actionStep, FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 6)).map _ = _
    rw [invokeNative, recovery_at_disclosure preferOne 6 (by omega) (by omega),
      FinDist.pure_bind, actionStep, FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 7)).map _ = _
    rw [invokeNative, recovery_at_disclosure preferOne 7 (by omega) (by omega),
      FinDist.pure_bind, actionStep, FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire .wire (snapshot preferOne 8)
      (fun _ => none)).map _ = _
    rw [wire_includes _ _ (second_wire preferOne), FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.includeLatest 1 ()) (snapshot preferOne 9)
      (fun _ => none)).map _ = _
    rw [reserved_includes _ _ _ (second_reserved preferOne), FinDist.map_pure]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl

private theorem recovery_iterate (preferOne : Bool) (stage : Nat) (early : stage ≤ 10) :
    (fun law => law.bind (recoveryKernel preferOne))^[stage]
        (FinDist.pure (some (secondControl first second))) =
      FinDist.pure (control preferOne stage) := by
  induction stage with
  | zero => simp only [Function.iterate_zero_apply, control, snapshot, List.drop_zero]; rfl
  | succ stage ih =>
      rw [Function.iterate_succ_apply', ih (by omega), FinDist.pure_bind,
        recovery_step preferOne stage (by omega)]

abbrev nativeModel := runtime.nativeInformation (FinDist.pure input) [] 1 wire ordering

abbrev nativeRun (policy : NativePolicy graph) (fuel : Nat) (history : arena.History) :=
  nativeModel.runSingleMoverBehavioralFrom
    (runtime.native_singleMover (FinDist.pure input) [] 1 wire ordering)
    (fun _ => encodeNativePolicy policy) fuel history

def nativeResult : arena.State → Option (PublicationResult Int)
  | none => none
  | some state => state.execution.native.application.config.outputs 1

private theorem recovery_ten (preferOne : Bool) :
    (nativeRun (recoveryPolicy preferOne) 10 (secondHistory first second)).map
      ExecutionProtocol.History.state = FinDist.pure (control preferOne 10) := by
  rw [native_run_map_state]
  exact recovery_iterate preferOne 10 (by omega)

/-- The successful publication persists through every remaining service step.
This is the canonical randomized history runner, including its private recall. -/
theorem recovery_result (preferOne : Bool) (extra : Nat) (final : arena.History)
    (reached : final ∈
      (nativeRun (recoveryPolicy preferOne) (10 + extra) (secondHistory first second)).support) :
    nativeResult final.state = some (.success (preferredValue preferOne)) := by
  rw [nativeRun, InformationModel.runSingleMoverBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_add, FinDist.support_bind] at reached
  obtain ⟨middle, prefixRun, suffix⟩ := Set.mem_iUnion₂.mp reached
  have atTen : middle.state ∈
      ((nativeRun (recoveryPolicy preferOne) 10 (secondHistory first second)).map
        ExecutionProtocol.History.state).support := by
    rw [FinDist.support_map]
    exact ⟨middle, prefixRun, rfl⟩
  rw [recovery_ten, FinDist.mem_support_pure] at atTen
  have path := ExecutionProtocol.runRandomizedFor_reachesWithin _ _ _ _ suffix
  obtain ⟨after, afterEq, actions, native⟩ := runtime.native_reaches_native
    (FinDist.pure input) [] 1 wire ordering path
    ⟨5, (secondControl first second).plan.drop 10, snapshot preferOne 10⟩ atTen
  have stored := runtime.applicationRun_store_of_some _ _ actions native (.inr 1)
    (.success (preferredValue preferOne)) (publication_snapshot preferOne)
  rw [afterEq]
  exact stored

/-- Each public utility has a native deviation attaining its residual maximum. -/
theorem recovery_value (preferOne : Bool) (extra : Nat) :
    (nativeRun (recoveryPolicy preferOne) (10 + extra) (secondHistory first second)).expect
      (fun final => publicUtility preferOne (nativeResult final.state)) = 2 := by
  calc
    _ = (nativeRun (recoveryPolicy preferOne) (10 + extra)
        (secondHistory first second)).expect (fun _ => 2) := by
      apply FinDist.expect_congr
      intro final reached
      rw [recovery_result preferOne extra final reached]
      cases preferOne <;> norm_num [preferredValue, publicUtility]
    _ = _ := FinDist.expect_const _ _

private def selectionControl (action : PlayerAction graph) : NativeControl runtime :=
  ⟨5, (secondControl first second).plan.drop 2,
    includedExecution (afterAction action) (selected action)⟩

private theorem first_two_law (policy : NativePolicy graph) :
    (nativeRun policy 2 (secondHistory first second)).map ExecutionProtocol.History.state =
      (policy (contested.principalHistory ()) (runtime.nativeView contested.native ())).map
        (fun action => some (selectionControl action)) := by
  rw [native_run_map_state]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind]
  change ((runtime.invokeNative () policy contested).map _).bind _ = _
  simp only [invokeNative, actionStep, FinDist.map_bind, FinDist.map_pure, FinDist.bind_bind,
    FinDist.pure_bind]
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro action _
  change (runtime.nativeInstructionStep wire .wire (afterAction action)
    (fun _ => none)).map _ = _
  rw [wire_includes _ _ (show wire (afterAction action).environmentHistory
      (MessageApplication.State.environmentView app (afterAction action).native) =
        FinDist.pure (.include ((), selected action)) from rfl), FinDist.map_pure]
  rfl

/-- Every randomized continuation passes through one of the two immutable
winning bindings before any further strategic choice. -/
theorem native_after_two (policy : NativePolicy graph) (middle : arena.History)
    (reached : middle ∈ (nativeRun policy 2 (secondHistory first second)).support) :
    ∃ (control : NativeControl runtime) (action : PlayerAction graph),
      middle.state = some control ∧ control.execution.native = included action := by
  have stateSupport : middle.state ∈
      ((nativeRun policy 2 (secondHistory first second)).map
        ExecutionProtocol.History.state).support :=
    FinDist.support_map .. ▸ ⟨middle, reached, rfl⟩
  rw [first_two_law, FinDist.support_map] at stateSupport
  obtain ⟨action, _, same⟩ := stateSupport
  exact ⟨selectionControl action, action, same.symm, rfl⟩

/-- No native behavioral policy can attain both continuation benchmarks. -/
theorem native_value_sum_le (policy : NativePolicy graph) (extra : Nat) :
    (nativeRun policy (2 + extra) (secondHistory first second)).expect
      (fun final => publicUtility true (nativeResult final.state)) +
    (nativeRun policy (2 + extra) (secondHistory first second)).expect
      (fun final => publicUtility false (nativeResult final.state)) ≤ 3 := by
  rw [← FinDist.expect_add]
  apply FinDist.expect_le_of_forall
  intro final reached
  rw [nativeRun, InformationModel.runSingleMoverBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_add, FinDist.support_bind] at reached
  obtain ⟨middle, prefixRun, suffix⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨before, action, beforeEq, nativeEq⟩ := native_after_two policy middle prefixRun
  have path := ExecutionProtocol.runRandomizedFor_reachesWithin _ _ _ _ suffix
  obtain ⟨after, afterEq, actions, native⟩ := runtime.native_reaches_native
    (FinDist.pure input) [] 1 wire ordering path before beforeEq
  rw [nativeEq] at native
  rw [afterEq]
  exact residual_utility_sum_le action actions _ native

def nativePayoff (preferOne : Bool) (final : arena.History) (_who : Unit) : ℝ :=
  publicUtility preferOne (nativeResult final.state)

/-- The actual native service has no common behavioral SPE for these two
public utilities. Quantification includes all randomized information-local
policies, not only policies generated by a particular compiler. -/
theorem no_common_native_spe :
    ¬ ∃ profile : GameTheory.Profile nativeModel.behavioralSignature,
      nativeModel.IsBehavioralSubgamePerfect
        (runtime.native_singleMover (FinDist.pure input) [] 1 wire ordering)
        (runtime.native_bounded (FinDist.pure input) [] 1 wire ordering)
        profile (nativePayoff true) ∧
      nativeModel.IsBehavioralSubgamePerfect
        (runtime.native_singleMover (FinDist.pure input) [] 1 wire ordering)
        (runtime.native_bounded (FinDist.pure input) [] 1 wire ordering)
        profile (nativePayoff false) := by
  rintro ⟨profile, one, two⟩
  let policy := decodeNativePolicy (profile ())
  have profileEq : profile = fun _ => encodeNativePolicy policy := by
    funext who
    cases who
    exact (encode_decodeNativePolicy (profile ())).symm
  have deviation (preferOne : Bool) :
      GameTheory.Profile.update profile () (encodeNativePolicy (recoveryPolicy preferOne)) =
        fun _ => encodeNativePolicy (recoveryPolicy preferOne) := by
    funext who
    cases who
    simp [GameTheory.Profile.update]
  rw [InformationModel.isBehavioralSubgamePerfect_iff] at one two
  have oneBound := one (secondHistory first second) contested_isSubgameRoot ()
    (encodeNativePolicy (recoveryPolicy true))
  have twoBound := two (secondHistory first second) contested_isSubgameRoot ()
    (encodeNativePolicy (recoveryPolicy false))
  rw [deviation, profileEq] at oneBound twoBound
  change (nativeRun (recoveryPolicy true) (10 + 99) _).expect _ ≤
    (nativeRun policy (2 + 107) _).expect _ at oneBound
  change (nativeRun (recoveryPolicy false) (10 + 99) _).expect _ ≤
    (nativeRun policy (2 + 107) _).expect _ at twoBound
  rw [show nativePayoff true = fun final _ =>
      publicUtility true (nativeResult final.state) from rfl, recovery_value] at oneBound
  rw [show nativePayoff false = fun final _ =>
      publicUtility false (nativeResult final.state) from rfl, recovery_value] at twoBound
  linarith [native_value_sum_le policy 107]

end VegasTests.PendingMenus
