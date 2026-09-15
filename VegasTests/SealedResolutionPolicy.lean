/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Vegas.Compile.SealedResolvedReads
import Vegas.Compile.SealedPolicyProgress
import Vegas.Compile.SealedResolutionClosure
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
  exact supported.resolvedPlayerStore_reads_of_ready none 2 0 [] (view missingCommit)
    hinvariant.publicEvents
    (supported.ownCommitCache_of_registered none 2 0 execution hinvariant hmemory)
    (node 2) secondGuard rfl (by decide)

/-- The general progress theorem selects the next real source site after the
first commitment and reveal default. It applies to every source kernel, not
just the concrete repeat policy used by the execution examples. -/
theorem missing_commit_progress (policy : CommitPolicy graph 0) :
    ∀ command ∈ (supported.resolvingPolicy none 2 0 policy [] (view missingCommit)).support,
      supported.ProgressCommand 0 [] (node 2) command := by
  let execution := MessageApplication.PolicyExecution.initial app
    (MessageApplication.State.initial app missingCommit)
  have hinvariant : runtime.EventInvariant execution.native.application :=
    (SealedResolution.EventInvariant.initial (runtime := runtime)).tick.tick
  have hmemory : runtime.RegistrationMemory execution := by
    intro owner slot
    rfl
  have hclosed : execution.native.application.visible.ResolutionClosed runtime :=
    SealedResolution.PublicState.ResolutionClosed.tick
      (fun _ _ hrule _ hprior => supported.compile_rule_requires_lt hrule hprior)
      (fun _ _ _ _ hrule => supported.compile_reveal_source_lt hrule rfl)
  intro command hcommand
  obtain ⟨selected, hbound, hnotDone, _, hprogress⟩ :=
    supported.resolvingPolicy_progress_of_ready none 2 0 policy [] (view missingCommit)
      hinvariant.publicEvents
      (supported.ownCommitCache_of_registered none 2 0 execution hinvariant hmemory)
      hclosed (node 2) (by decide) (by decide)
      (Or.inl ⟨secondGuard, rfl⟩) command hcommand
  have hselected : selected = node 2 := by
    apply Fin.ext
    have hindex : selected.val ≤ 2 := hbound
    have hcases : selected.val = 0 ∨ selected.val = 1 ∨ selected.val = 2 := by omega
    rcases hcases with hzero | hone | htwo
    · rw [hzero] at hnotDone
      have : (true : Bool) = false := hnotDone
      contradiction
    · rw [hone] at hnotDone
      have : (true : Bool) = false := hnotDone
      contradiction
    · exact htwo
  subst selected
  exact hprogress

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
  unfold SealedShape.commitCommand
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
  unfold SealedShape.commitCommand
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

def resumedPending (value : Value) : app.State :=
  let initial := MessageApplication.State.initial app missingCommit
  { initial with
    application.service := (initial.application.service.sealValue 0 2 value).state
    pool := (initial.pool.submit 0 (.commitment 2 (0, 2))).2 }

/-- Native inclusion accepts a ready commitment after earlier defaults. The
canonical source site's declared prerequisites are discharged by those defaults. -/
theorem resumed_commit_included (value : Value) :
    (app.includePending (resumedPending value) (0, 0)).application.visible.completed 2 = true :=
  runtime.includePending_commitment_completed (resumedPending value) 0 0 2
    (graph.messagePrerequisites (node 2)) value rfl rfl rfl rfl

def resumedOpeningPending (value : Value) : app.State :=
  let acceptedState := app.includePending (resumedPending value) (0, 0)
  { acceptedState with pool := (acceptedState.pool.submit 0 (.opening 3 (0, 2) value)).2 }

/-- The accepted commitment can be opened through the same pending-message
interface, including when the registered source choice is `none`. -/
theorem resumed_opening_included (value : Value) :
    (app.includePending (resumedOpeningPending value) (0, 1)).application.visible.completed 3 =
      true :=
  runtime.includePending_opening_completed (resumedOpeningPending value) 0 1 3 2
    (graph.messagePrerequisites (node 3)) value rfl rfl rfl rfl rfl

/-- Queue drainage after arbitrary intervening player and environment actions
completes this ready source commitment; it cannot silently discard its packet. -/
theorem resumed_commit_complete_of_drained (value : Value)
    (players : PendingStages.Player → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation PendingStages.Player))
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial app (resumedPending value))).support)
    (hempty : next.native.pool.pending = []) :
    next.native.application.visible.completed 2 = true := by
  have hresult := runtime.runPolicies_commitment_pendingOrCompleted players environment schedule
    (MessageApplication.PolicyExecution.initial app (resumedPending value)) next 0 0 2
    (graph.messagePrerequisites (node 2)) value rfl (by exact List.mem_cons_self) rfl rfl hnext
  rcases hresult with hdone | hpending
  · exact hdone
  · simp only [hempty, List.not_mem_nil, false_and] at hpending

/-- The same arbitrary-traffic guarantee holds for its opening. Acceptance of
the producer is retained even if unrelated nodes time out before drainage. -/
theorem resumed_opening_complete_of_drained (value : Value)
    (players : PendingStages.Player → app.PlayerPolicy) (environment : app.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation PendingStages.Player))
    (next : app.PolicyExecution)
    (hnext : next ∈ (app.runPolicies players environment schedule
      (MessageApplication.PolicyExecution.initial app (resumedOpeningPending value))).support)
    (hempty : next.native.pool.pending = []) :
    next.native.application.visible.completed 3 = true := by
  have hbase : runtime.EventInvariant (resumedPending value).application :=
    ((SealedResolution.EventInvariant.initial (runtime := runtime)).tick.tick).register 0 2 value
  have hinvariant : runtime.EventInvariant (resumedOpeningPending value).application :=
    app.includePending_application_invariant runtime.EventInvariant
      (fun _ message _ invariant hhandle => invariant.handle message hhandle)
      (resumedPending value) (0, 0) hbase
  have hresult := runtime.runPolicies_opening_pendingOrCompleted players environment schedule
    (MessageApplication.PolicyExecution.initial app (resumedOpeningPending value)) next 0 1 3 2
    (graph.messagePrerequisites (node 3)) (graph.messagePrerequisites (node 2)) value rfl rfl
    hinvariant (by exact List.mem_cons_self) rfl rfl rfl hnext
  rcases hresult with hdone | hpending
  · exact hdone
  · simp only [hempty, List.not_mem_nil, false_and] at hpending

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
