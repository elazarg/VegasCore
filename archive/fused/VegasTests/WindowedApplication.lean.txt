/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors.
-/

import Vegas.Compile.WindowedApplication
import Vegas.Compile.WindowedSourceSafety
import Vegas.Compile.BindingTimeoutCompilation
import VegasTests.ApplicationOrder

/-! # Activation-relative windows on a generated ordered application -/

noncomputable section

namespace VegasTests.WindowedApplication

open Vegas Vegas.EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability
open VegasTests.ApplicationEarlyBinding

abbrev Player := ApplicationEarlyBinding.Player

def firstFallback : SourceDecisionSite.PublicFallback ApplicationOrder.firstSite where
  expr := .constBool false
  legal _ := rfl

def secondFallback : SourceDecisionSite.PublicFallback secondSite where
  expr := .constBool false
  legal _ := rfl

def decoratedImage : ApplicationImage Player simpleExpr :=
  secondFallback.installBindingTimeout source.fresh compilerInitial 10 <|
    firstFallback.installBindingTimeout source.fresh compilerInitial 10 image

/-- One selector has the same left-to-right effect as the two concrete timeout
installations above. -/
def bindingSelector (code : BindingCode Player simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.ty) :=
  secondFallback.selectBindingTimeout source.fresh compilerInitial 10
    { code with timeout :=
        firstFallback.selectBindingTimeout source.fresh compilerInitial 10 code }

def choiceSelector (code : PublicChoiceCode Player simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.guard.ty) := code.timeout

def compiledRuntime : WindowedApplication Player simpleExpr :=
  applicationPlan.windowed (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)

def runtime : WindowedApplication Player simpleExpr where
  image := decoratedImage
  windowOf _ := 10

/-- The executable regression runtime is the application-plan constructor,
not an independently assembled interpreter. -/
theorem runtime_eq_compiled : runtime = compiledRuntime := by
  unfold runtime compiledRuntime ApplicationPlan.windowed decoratedImage
    SourceDecisionSite.PublicFallback.installBindingTimeout
    ApplicationImage.withBindingTimeouts ApplicationImage.withChoiceTimeouts
  apply congrArg (fun instructions =>
    WindowedApplication.mk (ApplicationImage.mk instructions) (fun _ => 10))
  simp only [List.map_map]
  apply List.map_congr_left
  intro instruction _
  cases instruction <;> rfl

def initial : runtime.application.State :=
  MessageApplication.State.initial runtime.application (runtime.initial initialNative)

def expiryRun : List runtime.application.Action :=
  [.environment (.advance 100),
    .submit 1 (.expireBinding 0), .include (1, 0),
    .submit 0 (.expireBinding 1), .include (0, 0),
    .environment (.advance 110),
    .submit 0 (.expireBinding 1), .include (0, 1),
    .environment (.advance 111),
    .submit 0 (.expireBinding 1), .include (0, 2)]

def rejectedRun : List runtime.application.Action :=
  [.environment (.advance 100),
    .submit 1 (.expireBinding 0), .include (1, 0),
    .submit 0 (.expireBinding 1), .include (0, 0),
    .environment (.advance 110),
    .submit 0 (.expireBinding 1), .include (0, 1)]

/-- Rejected attempts and clock advancement retain the second instruction's
original activation time. -/
theorem rejected_traffic_retains_origin :
    (runtime.application.run rejectedRun initial).map (fun result =>
      (result.application.base.memory.done 1, result.application.active,
        result.receipts)) =
      FinDist.pure (false, some ⟨1, 100⟩,
        [((1, 0), true), ((0, 0), false), ((0, 1), false)]) := by
  simp only [rejectedRun, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, WindowedApplication.application_advance,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

def replayedRejectedRun : List runtime.application.Action :=
  [.environment (.advance 100),
    .submit 1 (.expireBinding 0), .include (1, 0),
    .submit 0 (.expireBinding 1), .deliver 1 (0, 0), .include (0, 0),
    .replay 1 (0, 0), .include (0, 0)]

/-- A locally observed rejected expiry can be replayed as raw traffic. Its
second rejection is recorded and the active window still keeps origin 100. -/
theorem replayed_rejection_retains_origin :
    (runtime.application.run replayedRejectedRun initial).map (fun result =>
      (result.application.base.memory.done 1, result.application.active,
        result.pool.ledger, result.receipts)) =
      FinDist.pure (false, some ⟨1, 100⟩,
        [⟨(1, 0), .expireBinding 0⟩, ⟨(0, 0), .expireBinding 1⟩,
          ⟨(0, 0), .expireBinding 1⟩],
        [((1, 0), true), ((0, 0), false), ((0, 0), false)]) := by
  simp only [replayedRejectedRun, MessageApplication.run_cons,
    MessageApplication.run_nil, MessageApplication.step,
    WindowedApplication.application_advance, FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- Time spent at the first instruction does not consume the second window.
The second fallback is rejected at activation and at the strict boundary, then
accepted one tick later. Rejections retain ledger entries and receipts without
restarting the public activation origin. -/
theorem second_window_starts_on_activation :
    (runtime.application.run expiryRun initial).map (fun result =>
      (result.application.base.memory.done 0,
        result.application.base.memory.done 1,
        result.application.base.memory.accepted 0,
        result.application.base.memory.accepted 1,
        result.application.active,
        result.pool.ledger,
        result.receipts)) =
      FinDist.pure (true, true,
        some (.publicDefault ⟨.bool, false⟩),
        some (.publicDefault ⟨.bool, false⟩),
        some ⟨(firstConditionalSite.choice.publicationNode
          source.fresh compilerInitial).val, 111⟩,
        [⟨(1, 0), .expireBinding 0⟩,
          ⟨(0, 0), .expireBinding 1⟩,
          ⟨(0, 1), .expireBinding 1⟩,
          ⟨(0, 2), .expireBinding 1⟩],
        [((1, 0), true), ((0, 0), false), ((0, 1), false), ((0, 2), true)]) := by
  simp only [expiryRun, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, WindowedApplication.application_advance,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

def ordinaryWins : List runtime.application.Action :=
  [.environment (.advance 100),
    .submit 1 (.expireBinding 0), .include (1, 0),
    .environment (.advance 111),
    .privateCommand 1 (.register 1 ⟨.bool, true⟩),
    .submit 1 (.binding 1 (1, 1)), .include (1, 1),
    .submit 0 (.expireBinding 1), .include (0, 0)]

/-- Passing the relative deadline does not itself resolve an instruction. A
canonical ordinary binding included first wins the existing first-resolution
race, and the later expiry is rejected. -/
theorem ordinary_binding_can_win_after_deadline :
    (runtime.application.run ordinaryWins initial).map (fun result =>
      (result.application.base.memory.accepted 1,
        result.application.base.frozen 1,
        result.receipts)) =
      FinDist.pure (some (.opaque ((1 : Player), 1)), some ⟨.bool, true⟩,
        [((1, 0), true), ((1, 1), true), ((0, 0), false)]) := by
  simp only [ordinaryWins, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, WindowedApplication.application_advance,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- Activation metadata is part of both public observations. -/
theorem public_view_exposes_origin :
    runtime.application.observeEnvironment initial.application =
      (initialNative.memory, some ⟨0, 0⟩) ∧
    ∀ who, runtime.application.observePlayer initial.application who =
      (initialNative.memory, some ⟨0, 0⟩) := by
  exact ⟨rfl, fun _ => rfl⟩

def absoluteApplication := decoratedImage.orderedApplication

def absoluteInitial : absoluteApplication.State :=
  MessageApplication.State.initial absoluteApplication initialNative

def absoluteRun : List absoluteApplication.Action :=
  [.environment (.advance 100),
    .submit 1 (.expireBinding 0), .include (1, 0),
    .submit 0 (.expireBinding 1), .include (0, 0)]

/-- Reusing the emitted absolute deadline does not provide a fresh response
window: after the delayed first resolution, the second fallback is immediately
eligible in the original ordered application. -/
theorem absolute_deadline_expires_second_immediately :
    (absoluteApplication.run absoluteRun absoluteInitial).map (fun result =>
      (result.application.memory.done 1,
        result.application.memory.accepted 1, result.receipts)) =
      FinDist.pure (true, some (.publicDefault ⟨.bool, false⟩),
        [((1, 0), true), ((0, 0), true)]) := by
  simp only [absoluteRun, MessageApplication.run_cons, MessageApplication.run_nil,
    MessageApplication.step, absoluteApplication, ApplicationImage.ordered_advance,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

/-- Every finished execution of the compiler-constructed runtime, under
arbitrary player and environment policies, decodes to an actual source
execution. This is support safety, not progress or a policy-law comparison. -/
theorem compiled_runtime_finished_source_safe
    (players : Player → compiledRuntime.application.PlayerPolicy)
    (environment : compiledRuntime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (next : compiledRuntime.application.PolicyExecution)
    (hnext : next ∈ (compiledRuntime.application.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial _
        (MessageApplication.State.initial _
          (compiledRuntime.initial (ApplicationImage.State.initial
            (ApplicationImage.Memory.initial compiled.graph)))))).support)
    (hfinished : next.native.application.base.memory.finished compiled.graph.nodeCount = true) :
    ∃ terminalEnv : VEnv simpleExpr compiled.terminalCtx,
      SmallStep.Star
        { ctx := source.Γ, env := source.env, cont := source.prog }
        { ctx := compiled.terminalCtx, env := terminalEnv,
          cont := .ret compiled.sourcePayoffs } ∧
      compiled.readPublicTerminal? next.native.application.base.memory =
        some terminalEnv.erasePubEnv := by
  exact applicationPlan.windowed_runPolicies_source_public_outcome checked
    (fun _ => 10) bindingSelector choiceSelector (fun _ => 10)
    players environment schedule next hnext hfinished

end VegasTests.WindowedApplication

/-- info: 'VegasTests.WindowedApplication.second_window_starts_on_activation'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedApplication.second_window_starts_on_activation

/-- info: 'VegasTests.WindowedApplication.ordinary_binding_can_win_after_deadline'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedApplication.ordinary_binding_can_win_after_deadline

/-- info: 'VegasTests.WindowedApplication.rejected_traffic_retains_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedApplication.rejected_traffic_retains_origin

/-- info: 'VegasTests.WindowedApplication.replayed_rejection_retains_origin'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedApplication.replayed_rejection_retains_origin

/-- info: 'VegasTests.WindowedApplication.compiled_runtime_finished_source_safe'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedApplication.compiled_runtime_finished_source_safe
