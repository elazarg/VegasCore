/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedResolvedReads
import VegasTests.SealedPolicy

/-! # Compiled policies continue after nullable resolution

This uses the checked multistage source whose second commitment copies its
first public revelation. Both a missing commitment and a missing opening must
allow that next source decision. An existing private value is retained even
when its public revelation defaults to null.
-/

noncomputable section

namespace VegasTests.SealedResolutionPolicy

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction GameTheory.Math.Probability
open PendingStages

abbrev runtime := supported.resolvingRuntime none 2
abbrev app := runtime.messageApplication

def view (state : SealedResolution.ApplicationState PendingStages.Player Value) : app.View :=
  MessageApplication.State.observe app (MessageApplication.State.initial app state) 0

def missingCommit := runtime.tick (runtime.tick runtime.initial)

def registered (value : Value) : SealedResolution.ApplicationState PendingStages.Player Value :=
  { runtime.initial with service := (IdealCommitments.empty.sealValue 0 0 value).state }

def accepted (value : Value) : SealedResolution.ApplicationState PendingStages.Player Value :=
  (runtime.handle (registered value) ⟨(0, 0), .commitment 0 (0, 0)⟩).getD (registered value)

def missingOpening (value : Value) := runtime.tick (runtime.tick (accepted value))

def history (value : Value) : List app.PlayerEntry :=
  [⟨view runtime.initial, .privateCommand ⟨(0, value)⟩⟩]

theorem acceptance (value : Value) :
    runtime.handle (registered value) ⟨(0, 0), .commitment 0 (0, 0)⟩ =
      some (accepted value) := rfl

theorem private_and_public_values_after_missing_opening (value : Value) :
    (missingOpening value).service.lookup (0, 0) = some value ∧
      (missingOpening value).visible.published? 1 = some none ∧
      Store.getAs (supported.resolvedPlayerStore 0 none
        (missingOpening value).visible.timeouts (runtime.eventHistory (history value))
        (runtime.eventView (view (missingOpening value)))) 0 (.option .bool) = some value := by
  fin_cases value <;> exact ⟨rfl, rfl, rfl⟩

def secondSite : SourceDecisionSite (L := simpleExpr) 0 core
    [(1, .pub (.option .bool)), (0, .sealed 0 (.option .bool))]
    2 (.option .bool) (Expr.nullableCommitGuard (Expr.constBool true)) :=
  .commit (.reveal (.here _ _))

def secondBuild := decisionSiteState secondSite source.core.fresh SealedPolicy.initialBuild

def secondGuard : EventGuard simpleExpr :=
  eventGuardOf secondBuild 0
    (Expr.nullableCommitGuard (x := 2) (b := .bool) (Expr.constBool true))

/-- The general native-invariant theorem applies to a checked source after
its first commitment and public reveal have defaulted. No source decoding is
assumed at this state. -/
theorem missing_commit_reads_available :
    ∃ reads, ReadEnv.ofStoreExec?
      (supported.resolvedPlayerStore 0 none missingCommit.visible.timeouts []
        (runtime.eventView (view missingCommit))) secondGuard.choiceReads = some reads := by
  let execution := MessageApplication.PolicyExecution.initial app
    (MessageApplication.State.initial app missingCommit)
  have hinvariant : runtime.EventInvariant execution.native.application :=
    (SealedResolution.EventInvariant.initial (runtime := runtime)).tick.tick
  have hmemory : runtime.RegistrationMemory execution := by
    intro owner slot
    rfl
  exact supported.resolvedPlayerStore_reads_of_ready none 2 0 execution hinvariant hmemory
    (node 2) secondGuard rfl (by decide)

private theorem second_kernel (law : FinDist Value)
    (reads : ReadEnv simpleExpr secondGuard.choiceReads) :
    compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
        (SourceGraph.repeatPolicy law 0) (node 2) secondGuard rfl reads =
      compileSourceDecision secondBuild 0
        (Expr.nullableCommitGuard (x := 2) (b := .bool) (Expr.constBool true))
        (SourceGraph.repeatPolicy law 0 secondSite) reads :=
  compileSourcePolicy_at core source.core.fresh SealedPolicy.initialBuild rfl 0
    (SourceGraph.repeatPolicy law 0) _ secondSite (node 2) rfl rfl rfl reads

theorem missing_commit_continues (law : FinDist Value) :
    SealedPolicy.compilation.compileResolvingPolicy none 2 0 (SourceGraph.repeatPolicy law 0)
        [] (view missingCommit) =
      FinDist.pure (.privateCommand ⟨(2, none)⟩ : app.PlayerCommand) := by
  change supported.commitCommand 0
    (compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
      (SourceGraph.repeatPolicy law 0)) (node 2) secondGuard rfl []
      (supported.resolvedPlayerStore 0 none missingCommit.visible.timeouts []
        (runtime.eventView (view missingCommit))) = _
  unfold SealedFragment.commitCommand
  simp only [MessageApplication.ChoiceEncoding.cachedValue_nil]
  change (compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
    (SourceGraph.repeatPolicy law 0) (node 2) secondGuard rfl _).map _ = _
  rw [second_kernel]
  simp only [compileSourceDecision, SourceGraph.repeatPolicy, secondSite,
    VegasCore.commit.noConfusion, VegasCore.reveal.noConfusion, id_eq, FinDist.map_pure]
  rfl

theorem missing_opening_continues (law : FinDist Value) (value : Value) :
    SealedPolicy.compilation.compileResolvingPolicy none 2 0 (SourceGraph.repeatPolicy law 0)
        (history value) (view (missingOpening value)) =
      FinDist.pure (.privateCommand ⟨(2, none)⟩ : app.PlayerCommand) := by
  have hview : view (missingOpening value) = view (missingOpening none) := rfl
  rw [hview]
  change supported.commitCommand 0
    (compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
      (SourceGraph.repeatPolicy law 0)) (node 2) secondGuard rfl
      (runtime.eventHistory (history value))
      (supported.resolvedPlayerStore 0 none (missingOpening none).visible.timeouts
        (runtime.eventHistory (history value))
        (runtime.eventView (view (missingOpening none)))) = _
  unfold SealedFragment.commitCommand
  change (compileSourcePolicy core source.core.fresh SealedPolicy.initialBuild rfl 0
    (SourceGraph.repeatPolicy law 0) (node 2) secondGuard rfl _).map _ = _
  rw [second_kernel]
  simp only [compileSourceDecision, SourceGraph.repeatPolicy, secondSite,
    VegasCore.commit.noConfusion, VegasCore.reveal.noConfusion, id_eq, FinDist.map_pure]
  fin_cases value <;> rfl

/-- The resumed source decision runs through the shared native runner. Its
registration and submission retain `none` as a value inside an opaque seal. -/
theorem resumed_native_seal (law : FinDist Value) (environment : app.EnvironmentPolicy) :
    let initial := MessageApplication.PolicyExecution.initial app
      (MessageApplication.State.initial app missingCommit)
    let policies := fun _ => SealedPolicy.compilation.compileResolvingPolicy none 2 0
      (SourceGraph.repeatPolicy law 0)
    ((app.runPolicies policies environment [.player 0, .player 0] initial).map
      (fun execution => (execution.native.application.service.lookup (0, 2),
        execution.native.pool.pending))) =
      FinDist.pure (some none, [⟨(0, 0), .commitment 2 (0, 2)⟩]) := by
  dsimp only
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.bind_pure, FinDist.bind_bind]
  erw [missing_commit_continues]
  simp only [FinDist.pure_bind, MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step]
  have hcached : SealedPolicy.compilation.compileResolvingPolicy none 2 0
      (SourceGraph.repeatPolicy law 0)
      [⟨view missingCommit, .privateCommand ⟨(2, none)⟩⟩] (view missingCommit) =
      FinDist.pure (.submit (.commitment 2 (0, 2)) : app.PlayerCommand) := rfl
  erw [hcached]
  simp only [FinDist.pure_bind, MessageApplication.playerStep, MessageApplication.advance,
    MessageApplication.PlayerCommand.toAction, MessageApplication.step, FinDist.map_pure]
  rfl

end VegasTests.SealedResolutionPolicy

/-- info: 'VegasTests.SealedResolutionPolicy.missing_commit_continues' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedResolutionPolicy.missing_commit_continues

/-- info: 'VegasTests.SealedResolutionPolicy.missing_opening_continues' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedResolutionPolicy.missing_opening_continues

/-- info: 'VegasTests.SealedResolutionPolicy.resumed_native_seal' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedResolutionPolicy.resumed_native_seal
