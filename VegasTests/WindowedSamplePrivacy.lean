/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedSamplePrivacy
import VegasTests.ApplicationImage

/-! # Paired execution of an actual source chance checkpoint -/

noncomputable section

namespace VegasTests.WindowedSamplePrivacy

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory.Math.Probability
open VegasTests.ApplicationImage

abbrev TestPlayer := VegasTests.ApplicationImage.Player

def source : GraphProgram TestPlayer simpleExpr where
  Γ := []
  prog := sampleCore
  env := VEnv.empty simpleExpr
  wctx := by simp
  fresh := sampleFresh

def checked : WFProgram TestPlayer simpleExpr where
  core := source
  accounted := sampleAccounting
  legal := by
    change Legal sampleCore
    unfold sampleCore
    trivial

def nextState : BuildState TestPlayer simpleExpr [(0, .pub .bool)] :=
  (sampleState.addSampleEvent 0 (.weighted (b := .bool) fairCoin) sampleFresh.1).1

def nextPlan : ApplicationPlan (CommitmentAccounting.ret rfl) sampleFresh.2 nextState :=
  .ret rfl sampleFresh.2 nextState

def plan : ApplicationPlan sampleAccounting sampleFresh sampleState := by
  unfold sampleAccounting sampleCore
  exact .sample nextPlan

def deadlineOf : Nat → Nat := fun _ => 10

def noBinding (code : BindingCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.ty) := none

def noChoice (code : PublicChoiceCode TestPlayer simpleExpr) :
    Option (PublicFallbackCode simpleExpr code.guard.ty) := none

def windowOf : Nat → Nat := fun _ => 10

def runtime : WindowedApplication TestPlayer simpleExpr :=
  plan.windowed deadlineOf noBinding noChoice windowOf

def initial : runtime.application.PolicyExecution :=
  plan.windowedInitialExecution deadlineOf noBinding noChoice windowOf

def replacement
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) : runtime.application.PlayerPolicy :=
  fun history view => FinDist.pure (command history view)

def players (profile : SourceBehavioralProfile sampleCore)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) :
    TestPlayer → runtime.application.PlayerPolicy :=
  plan.windowedPlayers profile deadlineOf noBinding noChoice windowOf 0
    (replacement command)

/-- At the actual initialized sample checkpoint, any two complete service
branches taking the same supported source coin retain focal information. The
entire source profile and the fixed pure focal command remain arbitrary. -/
theorem initial_sample_block_agreement_of_same_draw
    (profile : SourceBehavioralProfile sampleCore)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (value : Bool) (hvalue : value ∈ fairCoin.denote.support)
    (middleLeft middleRight finalLeft finalRight : runtime.application.PolicyExecution)
    (hmiddleLeft : middleLeft ∈ (runtime.application.runPolicies
      (players profile command) (runtime.blockEnvironment [0, 1])
      ([Invocation.player 0, .player 0, .player 1, .player 1]) initial).support)
    (hmiddleRight : middleRight ∈ (runtime.application.runPolicies
      (players profile command) (runtime.blockEnvironment [0, 1])
      ([Invocation.player 0, .player 0, .player 1, .player 1]) initial).support)
    (hfinalLeft : finalLeft ∈ (runtime.application.runPolicies
      (players profile command) (runtime.blockEnvironment [0, 1])
      [.environment, .player 0, .environment, .player 1, .environment]
      (runtime.sampleExecution middleLeft
        (ApplicationPlan.headSampleCode sampleFresh sampleState) value)).support)
    (hfinalRight : finalRight ∈ (runtime.application.runPolicies
      (players profile command) (runtime.blockEnvironment [0, 1])
      [.environment, .player 0, .environment, .player 1, .environment]
      (runtime.sampleExecution middleRight
        (ApplicationPlan.headSampleCode sampleFresh sampleState) value)).support) :
    WindowedApplication.PolicyAgreement runtime 0 finalLeft finalRight ∧
      finalLeft ∈ (runtime.application.runPolicies (players profile command)
        (runtime.blockEnvironment [0, 1])
        (WindowedApplication.blockInvocations [0, 1]) initial).support ∧
      finalRight ∈ (runtime.application.runPolicies (players profile command)
        (runtime.blockEnvironment [0, 1])
        (WindowedApplication.blockInvocations [0, 1]) initial).support := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked plan profile deadlineOf
    noBinding noChoice windowOf (runtime.blockService [0, 1]) 0 (replacement command)
  have agreement : WindowedApplication.PolicyAgreement runtime 0 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  apply ApplicationPlan.WindowedCheckpoint.sample_block_agreement_of_same_draw
    nextPlan profile _ _ initial initial checkpoint checkpoint agreement command rfl
    (by decide) value
  · change value ∈ fairCoin.denote.support
    exact hvalue
  · change value ∈ fairCoin.denote.support
    exact hvalue
  · simpa [runtime, players] using hmiddleLeft
  · simpa [runtime, players] using hmiddleRight
  · simpa [runtime, players] using hfinalLeft
  · simpa [runtime, players] using hfinalRight

/-- The source-indexed endpoint needs only actual complete-block support and
the recorded successors' refinement, not an externally supplied decomposition
into polling and fixed-chance branches. -/
theorem initial_sample_block_agreement_at_source
    (profile : SourceBehavioralProfile sampleCore)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (value : Bool)
    (recordedLeft recordedRight : CoupledAt (compileCore sampleCore sampleFresh sampleState).graph
      nextState)
    (hsourceLeft : recordedLeft.current.source =
      (compiledInitialCoupled source).current.source.cons value)
    (hsourceRight : recordedRight.current.source =
      (compiledInitialCoupled source).current.source.cons value)
    (finalLeft finalRight : runtime.application.PolicyExecution)
    (hrefinesLeft : finalLeft.native.application.base.Refines recordedLeft.current.graph.1)
    (hrefinesRight : finalRight.native.application.base.Refines recordedRight.current.graph.1)
    (hfinalLeft : finalLeft ∈ (runtime.application.runPolicies (players profile command)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support)
    (hfinalRight : finalRight ∈ (runtime.application.runPolicies (players profile command)
      (runtime.blockEnvironment [0, 1])
      (WindowedApplication.blockInvocations [0, 1]) initial).support) :
    WindowedApplication.PolicyAgreement runtime 0 finalLeft finalRight := by
  have checkpoint := ApplicationPlan.WindowedCheckpoint.initial checked plan profile deadlineOf
    noBinding noChoice windowOf (runtime.blockService [0, 1]) 0 (replacement command)
  have agreement : WindowedApplication.PolicyAgreement runtime 0 initial initial :=
    ⟨⟨ApplicationImage.State.AgreesFor.refl _ _, rfl⟩, rfl, rfl, rfl⟩
  exact ApplicationPlan.WindowedCheckpoint.sample_block_agreement_at_source nextPlan profile
    (compiledInitialCoupled source) (compiledInitialCoupled source)
    initial initial finalLeft finalRight checkpoint checkpoint agreement command rfl (by decide)
    recordedLeft recordedRight value hsourceLeft hsourceRight hrefinesLeft hrefinesRight
    hfinalLeft hfinalRight

end VegasTests.WindowedSamplePrivacy

/-- info: 'VegasTests.WindowedSamplePrivacy.initial_sample_block_agreement_of_same_draw'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  VegasTests.WindowedSamplePrivacy.initial_sample_block_agreement_of_same_draw

/-- info: 'VegasTests.WindowedSamplePrivacy.initial_sample_block_agreement_at_source'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.WindowedSamplePrivacy.initial_sample_block_agreement_at_source
