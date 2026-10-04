/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PendingMenus
import GameTheoryExtensions.Protocol.BehavioralContinuation
import Mathlib.Tactic.IntervalCases

/-! # Public outcomes attainable by native continuation policies

The two policies use only public acceptance. Sending an opening while the
binding is still contested selects the first pending commitment; waiting
selects the second. Once the binding is accepted, each policy submits the
corresponding opening. The reserved inclusion publishes that value.
-/

noncomputable section

namespace Vegas.Examples.PendingMenus

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

def preferredValue (preferOne : Bool) : Int := if preferOne then 1 else 2
def preferredSlot (preferOne : Bool) : Nat := if preferOne then 0 else 1

def openingPacket (preferOne : Bool) : Payload graph :=
  .opening 1 ((), .prepared (preferredSlot preferOne)) ⟨.int, preferredValue preferOne⟩

def openingAction (preferOne : Bool) : PlayerAction graph :=
  ⟨[], some ⟨openingPacket preferOne, none⟩⟩

/-- Only public acceptance of the binding is consulted: it marks the
disclosure event's readiness. No hidden state is read. -/
def recoveryPolicy (preferOne : Bool) : NativePolicy graph := fun _ view =>
  PMF.pure (if preferOne || (view.publicView.accepted (.inr 0)).isSome then
    openingAction preferOne else PlayerAction.wait)

def selectionAction (preferOne : Bool) : PlayerAction graph :=
  if preferOne then openingAction preferOne else PlayerAction.wait

theorem recovery_at_root (preferOne : Bool) :
    recoveryPolicy preferOne (contested.principalHistory ())
      (runtime.nativeView contested.native ()) = PMF.pure (selectionAction preferOne) := by
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

private def sampledExecution (execution : NativeExecution runtime) (event : graph.EventId) :=
  environmentRecord execution (.application (.executeSample event)) execution.native

/-- The nine expected snapshots up to successful reserved disclosure. -/
private def snapshot (preferOne : Bool) : Nat → NativeExecution runtime
  | 0 => contested
  | 1 => afterAction (selectionAction preferOne)
  | 2 => includedExecution (snapshot preferOne 1) (preferredSlot preferOne)
  | 3 => includedExecution (snapshot preferOne 2) (if preferOne then 1 else 0)
  | 4 => sampledExecution (snapshot preferOne 3) 0
  | 5 => runtime.takeAction () (snapshot preferOne 4) (openingAction preferOne)
  | 6 => runtime.takeAction () (snapshot preferOne 5) (openingAction preferOne)
  | 7 => runtime.takeAction () (snapshot preferOne 6) (openingAction preferOne)
  | 8 => includedExecution (snapshot preferOne 7) 0
  | _ + 9 => includedExecution (snapshot preferOne 8) (if preferOne then 5 else 4)
termination_by stage => stage
decreasing_by all_goals omega

private def control (preferOne : Bool) (stage : Nat) : NativeProtocolState runtime :=
  some ⟨5, (secondControl first second).plan.drop stage, snapshot preferOne stage⟩

def recoveryKernel (preferOne : Bool) : arena.State → PMF arena.State :=
  runtime.nativeControlStep (PMF.pure input) [] 1 (fun _ => recoveryPolicy preferOne)
    wire ordering

private theorem wire_includes (execution : NativeExecution runtime) (serial : Nat)
    (chosen : wire execution.environmentHistory
      (MessageApplication.State.environmentView app execution.native) =
        PMF.pure (.include ((), serial))) :
    runtime.nativeInstructionStep wire .wire execution (fun _ => none) =
      PMF.pure (includedExecution execution serial) := by
  simp only [nativeInstructionStep, serviceStep, MessageApplication.invoke,
    MessageApplication.wireEnvironment, NativeExecution.environmentExecution, chosen,
    PMF.pure_map, PMF.pure_bind, WireCommand.toEnvironmentCommand,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step]
  rfl

private theorem reserved_includes (execution : NativeExecution runtime) (event : graph.EventId)
    (serial : Nat)
    (chosen : runtime.latestEventSubmissionCommand event ()
      (MessageApplication.State.environmentView app execution.native) = .include ((), serial)) :
    runtime.nativeInstructionStep wire (.includeLatest event ()) execution (fun _ => none) =
      PMF.pure (includedExecution execution serial) := by
  simp only [nativeInstructionStep, serviceStep, NativeExecution.environmentExecution, chosen,
    MessageApplication.environmentPolicyStep, MessageApplication.advance,
    MessageApplication.EnvironmentPolicyCommand.toAction, MessageApplication.step,
    PMF.pure_bind, PMF.pure_map]
  rfl

private theorem first_wire (preferOne : Bool) :
    wire (snapshot preferOne 1).environmentHistory
      (MessageApplication.State.environmentView app (snapshot preferOne 1).native) =
        PMF.pure (.include ((), preferredSlot preferOne)) := by
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
    wire (snapshot preferOne 7).environmentHistory
      (MessageApplication.State.environmentView app (snapshot preferOne 7).native) =
        PMF.pure (.include ((), 0)) := by
  unfold wire
  simp only [MessageApplication.State.environmentView, snapshot, includedExecution,
    sampledExecution, environmentRecord, takeAction, transmit,
    openingAction, MessageApplication.includePending_pool]
  cases preferOne <;> rfl

private theorem second_reserved (preferOne : Bool) :
    runtime.latestEventSubmissionCommand 1 ()
      (MessageApplication.State.environmentView app (snapshot preferOne 8).native) =
        .include ((), if preferOne then 5 else 4) := by
  unfold latestEventSubmissionCommand
  simp only [MessageApplication.State.environmentView, snapshot, includedExecution,
    sampledExecution, environmentRecord, takeAction, transmit,
    openingAction, MessageApplication.includePending_pool]
  cases preferOne <;> rfl

private theorem binding_ready (preferOne : Bool) :
    (snapshot preferOne 1).native.application.config.cut.Ready 0 := by
  simp only [snapshot]
  cases preferOne <;> decide

private def boundApplication (preferOne : Bool) : EventGraphRuntime.State graph :=
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

private def disclosureApplication (preferOne : Bool) : EventGraphRuntime.State graph :=
  boundApplication preferOne

/-- Sampling and the owner's opening submissions leave the bound application
unchanged. -/
private theorem disclosure_stage_application (preferOne : Bool) (stage : Nat)
    (lower : 4 ≤ stage) (upper : stage ≤ 7) :
    (snapshot preferOne stage).native.application = boundApplication preferOne := by
  have four : (snapshot preferOne 4).native.application = boundApplication preferOne := by
    rw [snapshot]
    exact leftover_application preferOne
  have five : (snapshot preferOne 5).native.application = boundApplication preferOne := by
    rw [snapshot]
    exact four
  have six : (snapshot preferOne 6).native.application = boundApplication preferOne := by
    rw [snapshot]
    exact five
  interval_cases stage
  · exact four
  · exact five
  · exact six
  · rw [snapshot]
    exact six

private theorem disclosure_application (preferOne : Bool) :
    (snapshot preferOne 8).native.application = disclosureApplication preferOne := by
  have missing : (snapshot preferOne 7).native.pool.lookup ((), 0) = none := by
    simp only [snapshot, includedExecution, environmentRecord,
      sampledExecution, takeAction, transmit, openingAction, MessageApplication.includePending_pool]
    cases preferOne <;> rfl
  have unchanged := app.includePending_missing _ _ missing
  rw [snapshot]
  change (app.includePending (snapshot preferOne 7).native ((), 0)).application = _
  rw [unchanged]
  exact disclosure_stage_application preferOne 7 (by omega) (by omega)

private theorem publication_ready (preferOne : Bool) :
    (disclosureApplication preferOne).config.cut.Ready 1 := by
  simp only [disclosureApplication, boundApplication, snapshot]
  cases preferOne <;> decide

private theorem publication_handler (preferOne : Bool) (serial : Nat) :
    handle runtime (snapshot preferOne 8).native.application
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
    (snapshot preferOne 9).native.application.config.outputs 1 =
      some (.success (preferredValue preferOne)) := by
  have pending : (snapshot preferOne 8).native.pool.lookup ((), if preferOne then 5 else 4) =
      some ⟨((), if preferOne then 5 else 4), openingPacket preferOne⟩ := by
    simp only [snapshot, includedExecution, environmentRecord,
      sampledExecution, takeAction, transmit, openingAction, MessageApplication.includePending_pool]
    cases preferOne <;> rfl
  have law := app.includePending_accept _ _ _ _ pending (publication_handler preferOne _)
  have output := congrArg (fun state : app.State => state.application.config.outputs 1) law
  rw [snapshot]
  exact output.trans (EventGraph.Config.complete_output_same _ _ _ _ _)

private theorem sample_step (execution : NativeExecution runtime)
    (notReady : ¬ execution.native.application.config.cut.Ready 0) :
    runtime.nativeInstructionStep wire (.sample 0) execution (fun _ => none) =
      PMF.pure (sampledExecution execution 0) := by
  simp only [nativeInstructionStep, serviceStep, MessageApplication.environmentPolicyStep,
    MessageApplication.advance, MessageApplication.EnvironmentPolicyCommand.toAction,
    MessageApplication.step, application, NativeExecution.environmentExecution,
    environmentStep_executeSample_of_not_ready runtime _ _ notReady,
    PMF.pure_map, PMF.pure_bind]
  rfl

private theorem recovery_at_disclosure (preferOne : Bool) (stage : Nat)
    (lower : 4 ≤ stage) (upper : stage ≤ 6) :
    recoveryPolicy preferOne ((snapshot preferOne stage).principalHistory ())
      (runtime.nativeView (snapshot preferOne stage).native ()) =
        PMF.pure (openingAction preferOne) := by
  have accepted : (runtime.nativeView (snapshot preferOne stage).native ()).publicView.accepted
      (.inr 0) = some ((), .prepared (preferredSlot preferOne)) := by
    change (snapshot preferOne stage).native.application.accepted (.inr 0) = _
    rw [disclosure_stage_application preferOne stage lower (by omega)]
    simp [boundApplication]
  simp only [recoveryPolicy, accepted, Option.isSome_some, Bool.or_true, ↓reduceIte]

private theorem recovery_step (preferOne : Bool) (stage : Nat) (early : stage < 9) :
    recoveryKernel preferOne (control preferOne stage) =
      PMF.pure (control preferOne (stage + 1)) := by
  interval_cases stage
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 0)).map _ = _
    rw [snapshot, invokeNative, recovery_at_root, PMF.pure_bind, actionStep,
      PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire .wire (snapshot preferOne 1)
      (fun _ => none)).map _ = _
    rw [wire_includes _ _ (first_wire preferOne), PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.includeLatest 0 ()) (snapshot preferOne 2)
      (fun _ => none)).map _ = _
    rw [reserved_includes _ _ _ (first_reserved preferOne), PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.sample 0) (snapshot preferOne 3)
      (fun _ => none)).map _ = _
    rw [sample_step _ (by rw [leftover_application]; exact bound_not_ready preferOne),
      PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 4)).map _ = _
    rw [invokeNative, recovery_at_disclosure preferOne 4 (by omega) (by omega),
      PMF.pure_bind, actionStep, PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 5)).map _ = _
    rw [invokeNative, recovery_at_disclosure preferOne 5 (by omega) (by omega),
      PMF.pure_bind, actionStep, PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.invokeNative () (recoveryPolicy preferOne) (snapshot preferOne 6)).map _ = _
    rw [invokeNative, recovery_at_disclosure preferOne 6 (by omega) (by omega),
      PMF.pure_bind, actionStep, PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire .wire (snapshot preferOne 7)
      (fun _ => none)).map _ = _
    rw [wire_includes _ _ (second_wire preferOne), PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl
  · change (runtime.nativeInstructionStep wire (.includeLatest 1 ()) (snapshot preferOne 8)
      (fun _ => none)).map _ = _
    rw [reserved_includes _ _ _ (second_reserved preferOne), PMF.pure_map]
    simp only [control, Nat.reduceAdd, snapshot]
    rfl

private theorem recovery_iterate (preferOne : Bool) (stage : Nat) (early : stage ≤ 9) :
    (fun law => law.bind (recoveryKernel preferOne))^[stage]
        (PMF.pure (some (secondControl first second))) =
      PMF.pure (control preferOne stage) := by
  induction stage with
  | zero => simp only [Function.iterate_zero_apply, control, snapshot, List.drop_zero]; rfl
  | succ stage ih =>
      rw [Function.iterate_succ_apply', ih (by omega), PMF.pure_bind,
        recovery_step preferOne stage (by omega)]

abbrev nativeModel := runtime.nativeInformation (PMF.pure input) [] 1 wire ordering

abbrev nativeRun (policy : NativePolicy graph) (fuel : Nat) (history : arena.History) :=
  nativeModel.runSingleMoverBehavioralFrom
    (runtime.native_singleMover (PMF.pure input) [] 1 wire ordering)
    (fun _ => encodeNativePolicy policy) fuel history

def nativeResult : arena.State → Option (PublicationResult Int)
  | none => none
  | some state => state.execution.native.application.config.outputs 1

private theorem recovery_nine (preferOne : Bool) :
    (nativeRun (recoveryPolicy preferOne) 9 (secondHistory first second)).map
      ExecutionProtocol.History.state = PMF.pure (control preferOne 9) := by
  rw [native_run_map_state]
  exact recovery_iterate preferOne 9 (by omega)

/-- The successful publication persists through every remaining service step.
This is the canonical randomized history runner, including its private recall. -/
theorem recovery_result (preferOne : Bool) (extra : Nat) (final : arena.History)
    (reached : final ∈
      (nativeRun (recoveryPolicy preferOne) (9 + extra) (secondHistory first second)).support) :
    nativeResult final.state = some (.success (preferredValue preferOne)) := by
  rw [nativeRun, InformationModel.runSingleMoverBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_add, PMF.support_bind] at reached
  obtain ⟨middle, prefixRun, suffix⟩ := Set.mem_iUnion₂.mp reached
  have atNine : middle.state ∈
      ((nativeRun (recoveryPolicy preferOne) 9 (secondHistory first second)).map
        ExecutionProtocol.History.state).support := by
    rw [PMF.support_map]
    exact ⟨middle, prefixRun, rfl⟩
  rw [recovery_nine, PMF.mem_support_pure_iff _ _] at atNine
  have path := ExecutionProtocol.runRandomizedFor_reachesWithin _ _ _ _ suffix
  obtain ⟨after, afterEq, actions, native⟩ := runtime.native_reaches_native
    (PMF.pure input) [] 1 wire ordering path
    ⟨5, (secondControl first second).plan.drop 9, snapshot preferOne 9⟩ atNine
  have stored := runtime.applicationRun_store_of_some _ _ actions native (.inr 1)
    (.success (preferredValue preferOne)) (publication_snapshot preferOne)
  rw [afterEq]
  exact stored

/-- Each public utility has a native deviation attaining its residual maximum. -/
theorem recovery_value (preferOne : Bool) (extra : Nat) :
    expect (nativeRun (recoveryPolicy preferOne) (9 + extra) (secondHistory first second))
      (fun final => publicUtility preferOne (nativeResult final.state)) = 2 := by
  calc
    _ = expect (nativeRun (recoveryPolicy preferOne) (9 + extra)
        (secondHistory first second)) (fun _ => 2) := by
      apply expect_congr_on_support
      intro final reached
      rw [recovery_result preferOne extra final reached]
      cases preferOne <;> norm_num [preferredValue, publicUtility]
    _ = _ := expect_constant _ _

private def selectionControl (action : PlayerAction graph) : NativeControl runtime :=
  ⟨5, (secondControl first second).plan.drop 2,
    includedExecution (afterAction action) (selected action)⟩

private theorem first_two_law (policy : NativePolicy graph) :
    (nativeRun policy 2 (secondHistory first second)).map ExecutionProtocol.History.state =
      (policy (contested.principalHistory ()) (runtime.nativeView contested.native ())).map
        (fun action => some (selectionControl action)) := by
  rw [native_run_map_state]
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, PMF.pure_bind]
  change ((runtime.invokeNative () policy contested).map _).bind _ = _
  simp only [invokeNative, actionStep, PMF.map_bind, PMF.pure_map, PMF.bind_bind,
    PMF.pure_bind]
  rw [← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro action _
  change (runtime.nativeInstructionStep wire .wire (afterAction action)
    (fun _ => none)).map _ = _
  rw [wire_includes _ _ (show wire (afterAction action).environmentHistory
      (MessageApplication.State.environmentView app (afterAction action).native) =
        PMF.pure (.include ((), selected action)) from rfl), PMF.pure_map]
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
    PMF.support_map .. ▸ ⟨middle, reached, rfl⟩
  rw [first_two_law, PMF.support_map] at stateSupport
  obtain ⟨action, _, same⟩ := stateSupport
  exact ⟨selectionControl action, action, same.symm, rfl⟩

/-- No native behavioral policy can attain both continuation benchmarks. -/
theorem native_value_sum_le (policy : NativePolicy graph) (extra : Nat) :
    expect (nativeRun policy (2 + extra) (secondHistory first second))
      (fun final => publicUtility true (nativeResult final.state)) +
    expect (nativeRun policy (2 + extra) (secondHistory first second))
      (fun final => publicUtility false (nativeResult final.state)) ≤ 3 := by
  have sum := expect_add (μ := nativeRun policy (2 + extra) (secondHistory first second))
    (f := fun final => publicUtility true (nativeResult final.state))
    (g := fun final => publicUtility false (nativeResult final.state))
    (payoffIntegrable_of_bounded _ _ fun final => publicUtility_abs_le _ _)
    (payoffIntegrable_of_bounded _ _ fun final => publicUtility_abs_le _ _)
  rw [← sum]
  refine expect_le_const _ _ (payoffIntegrable_of_bounded _ _ (C := 3 + 3) fun final =>
    (abs_add_le _ _).trans (add_le_add (publicUtility_abs_le _ _) (publicUtility_abs_le _ _)))
    _ fun final reached => ?_
  rw [nativeRun, InformationModel.runSingleMoverBehavioralFrom,
    ExecutionProtocol.runRandomizedFor_add, PMF.support_bind] at reached
  obtain ⟨middle, prefixRun, suffix⟩ := Set.mem_iUnion₂.mp reached
  obtain ⟨before, action, beforeEq, nativeEq⟩ := native_after_two policy middle prefixRun
  have path := ExecutionProtocol.runRandomizedFor_reachesWithin _ _ _ _ suffix
  obtain ⟨after, afterEq, actions, native⟩ := runtime.native_reaches_native
    (PMF.pure input) [] 1 wire ordering path before beforeEq
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
      nativeModel.IsSingleMoverBehavioralSubgamePerfect
        (runtime.native_singleMover (PMF.pure input) [] 1 wire ordering)
        (runtime.native_bounded (PMF.pure input) [] 1 wire ordering)
        profile (nativePayoff true) ∧
      nativeModel.IsSingleMoverBehavioralSubgamePerfect
        (runtime.native_singleMover (PMF.pure input) [] 1 wire ordering)
        (runtime.native_bounded (PMF.pure input) [] 1 wire ordering)
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
  rw [InformationModel.isSingleMoverBehavioralSubgamePerfect_iff] at one two
  have oneBound := (one (secondHistory first second) contested_isSubgameRoot ()
    (encodeNativePolicy (recoveryPolicy true))).2.2
  have twoBound := (two (secondHistory first second) contested_isSubgameRoot ()
    (encodeNativePolicy (recoveryPolicy false))).2.2
  rw [deviation, profileEq] at oneBound twoBound
  have runIntegrable (preferOne : Bool) (policy : NativePolicy graph) (fuel : Nat) :=
    payoffIntegrable_of_bounded (nativeRun policy fuel (secondHistory first second))
      (fun final => publicUtility preferOne (nativeResult final.state))
      fun final => publicUtility_abs_le preferOne (nativeResult final.state)
  change GameTheory.extendedExpectedUtility (nativePayoff true) ()
      (nativeRun (recoveryPolicy true) (9 + 88) (secondHistory first second)) ≤
    GameTheory.extendedExpectedUtility (nativePayoff true) ()
      (nativeRun policy (2 + 95) (secondHistory first second)) at oneBound
  change GameTheory.extendedExpectedUtility (nativePayoff false) ()
      (nativeRun (recoveryPolicy false) (9 + 88) (secondHistory first second)) ≤
    GameTheory.extendedExpectedUtility (nativePayoff false) ()
      (nativeRun policy (2 + 95) (secondHistory first second)) at twoBound
  replace oneBound := (GameTheory.extendedExpectedUtility_le_iff (runIntegrable true _ _)
    (runIntegrable true _ _)).mp oneBound
  replace twoBound := (GameTheory.extendedExpectedUtility_le_iff (runIntegrable false _ _)
    (runIntegrable false _ _)).mp twoBound
  change expect (nativeRun (recoveryPolicy true) (9 + 88) _)
      (fun final => publicUtility true (nativeResult final.state)) ≤
    expect (nativeRun policy (2 + 95) _)
      (fun final => publicUtility true (nativeResult final.state)) at oneBound
  change expect (nativeRun (recoveryPolicy false) (9 + 88) _)
      (fun final => publicUtility false (nativeResult final.state)) ≤
    expect (nativeRun policy (2 + 95) _)
      (fun final => publicUtility false (nativeResult final.state)) at twoBound
  rw [recovery_value] at oneBound twoBound
  linarith [native_value_sum_le policy 95]

end Vegas.Examples.PendingMenus
