/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedPolicy
import VegasTests.SourceGraph

/-! # The actual source-policy translation on native pending messages

The first source kernel may be any finite law. Its native implementation
privately registers the sampled value, then publishes an opaque handle without
sampling again. The source is multistage and its later choice has nonempty reads.
-/

noncomputable section

namespace VegasTests.SealedPolicy

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction GameTheory.Math.Probability
open PendingStages

theorem compilation : SealedCompilation source (.option .bool) := ⟨supported⟩

abbrev app := compilation.program.messageApplication (Value := Value)

def initial : app.PolicyExecution :=
  MessageApplication.PolicyExecution.initial app
    (MessageApplication.State.initial app ⟨IdealCommitments.empty, []⟩)

def policy (law : FinDist Value) : app.PlayerPolicy :=
  compilation.compilePolicy 0 (SourceGraph.repeatPolicy law 0)

def initialBuild : BuildState PendingStages.Player simpleExpr [] :=
  BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx)

def firstGuard : EventGuard simpleExpr :=
  eventGuardOf initialBuild 0
    (Expr.nullableCommitGuard (x := 0) (b := .bool) (Expr.constBool true))

theorem first_kernel (law : FinDist Value)
    (reads : ReadEnv simpleExpr firstGuard.choiceReads) :
    compileSourcePolicy core source.core.fresh initialBuild rfl 0
        (SourceGraph.repeatPolicy law 0) (node 0) firstGuard rfl reads =
      law.map (fun value => ⟨value, by cases value <;> rfl⟩) := by
  refine (compileSourcePolicy_at core source.core.fresh initialBuild rfl 0
    (SourceGraph.repeatPolicy law 0)
    (Expr.nullableCommitGuard (x := 0) (b := .bool) (Expr.constBool true))
    (.here _ _) (node 0) rfl rfl rfl reads).trans ?_
  simp only [compileSourceDecision, SourceGraph.repeatPolicy,
    VegasCore.commit.noConfusion, id_eq, FinDist.map_comp]
  rfl

theorem first_command (law : FinDist Value) :
    policy law [] (MessageApplication.State.observe app initial.native 0) =
      law.map (fun value => (.privateCommand ⟨(0, value)⟩ : app.PlayerCommand)) := by
  change supported.commitCommand 0
    (compileSourcePolicy core source.core.fresh initialBuild rfl 0
      (SourceGraph.repeatPolicy law 0)) (node 0) firstGuard rfl []
      (supported.playerStore 0 [] (MessageApplication.State.observe app initial.native 0)) = _
  unfold SealedFragment.commitCommand
  simp only [MessageApplication.ChoiceEncoding.cachedValue_nil]
  change (compileSourcePolicy core source.core.fresh initialBuild rfl 0
    (SourceGraph.repeatPolicy law 0) (node 0) firstGuard rfl _).map _ = _
  rw [first_kernel, FinDist.map_comp]
  rfl

theorem cached_command (law : FinDist Value) (value : Value) :
    policy law
      [⟨MessageApplication.State.observe app initial.native 0, .privateCommand ⟨(0, value)⟩⟩]
      (MessageApplication.State.observe app initial.native 0) =
      FinDist.pure (.submit (.commitment 0 (0, 0))) := by
  change supported.commitCommand 0
    (compileSourcePolicy core source.core.fresh initialBuild rfl 0
      (SourceGraph.repeatPolicy law 0)) (node 0) firstGuard rfl
      [⟨MessageApplication.State.observe app initial.native 0, .privateCommand ⟨(0, value)⟩⟩]
      (supported.playerStore 0
        [⟨MessageApplication.State.observe app initial.native 0, .privateCommand ⟨(0, value)⟩⟩]
        (MessageApplication.State.observe app initial.native 0)) = _
  apply supported.commitCommand_cached _ _ _ _ _ _ _ value
  rfl

def registered (value : Value) : app.PolicyExecution :=
  { initial with
    native := { initial.native with
      application.service := (IdealCommitments.empty.sealValue 0 0 value).state }
    principalHistory := fun who => if who = 0 then
      [⟨MessageApplication.State.observe app initial.native 0, .privateCommand ⟨(0, value)⟩⟩]
      else []
    nativeTrace := [.privateCommand 0 ⟨(0, value)⟩] }

def prepared (value : Value) : app.PolicyExecution :=
  { registered value with
    native := { (registered value).native with
      pool := ((registered value).native.pool.submit 0 (.commitment 0 (0, 0))).2 }
    principalHistory := fun who => if who = 0 then
      (registered value).principalHistory 0 ++
        [⟨MessageApplication.State.observe app (registered value).native 0,
          .submit (.commitment 0 (0, 0))⟩]
      else (registered value).principalHistory who
    nativeTrace := (registered value).nativeTrace ++ [.submit 0 (.commitment 0 (0, 0))] }

/-- A source law is carried jointly into private memory and the pending pool
by the actual native runner. The environment policy is unchanged. -/
theorem native_seal_law (law : FinDist Value) (environment : app.EnvironmentPolicy) :
    app.runPolicies (fun _ => policy law) environment [.player 0, .player 0] initial =
      law.map prepared := by
  have hregister (value : Value) :
      app.playerStep 0 initial (.privateCommand ⟨(0, value)⟩) =
        FinDist.pure (registered value) := by
    simp only [MessageApplication.playerStep, MessageApplication.advance,
      MessageApplication.PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
    rfl
  have hsubmit (value : Value) :
      app.playerStep 0 (registered value) (.submit (.commitment 0 (0, 0))) =
        FinDist.pure (prepared value) := by
    simp only [MessageApplication.playerStep, MessageApplication.advance,
      MessageApplication.PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind]
    rfl
  have hcached (value : Value) :
      policy law ((registered value).principalHistory 0)
        (MessageApplication.State.observe app (registered value).native 0) =
        FinDist.pure (.submit (.commitment 0 (0, 0))) := cached_command law value
  simp only [MessageApplication.runPolicies, MessageApplication.invoke,
    FinDist.bind_pure, FinDist.bind_bind]
  change ((policy law [] (MessageApplication.State.observe app initial.native 0)).bind
    (fun command => (app.playerStep 0 initial command).bind fun current =>
      (policy law (current.principalHistory 0)
        (MessageApplication.State.observe app current.native 0)).bind
          (app.playerStep 0 current))) = _
  rw [first_command, FinDist.bind_map]
  simp_rw [hregister, FinDist.pure_bind, hcached, FinDist.pure_bind, hsubmit]
  rw [FinDist.map_eq_bind]

/-- Pending commitment packets are independent of the sampled payload. -/
theorem prepared_pending (value : Value) :
    (prepared value).native.pool.pending = [⟨(0, 0), .commitment 0 (0, 0)⟩] := rfl

/-- The native source-policy execution satisfies the general history/service
invariant, not just the explicit packet fixture. -/
theorem prepared_memory (value : Value) :
    SealedProgram.RegistrationMemory compilation.program (prepared value) := by
  let environment : app.EnvironmentPolicy := fun _ _ => FinDist.pure .wait
  apply SealedProgram.RegistrationMemory.runPolicies
    (fun _ => policy (FinDist.pure value)) environment [.player 0, .player 0]
    initial (prepared value) SealedProgram.RegistrationMemory.initial
  rw [native_seal_law, FinDist.map_pure, FinDist.mem_support_pure]

end VegasTests.SealedPolicy

/-- info: 'VegasTests.SealedPolicy.native_seal_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPolicy.native_seal_law

/-- info: 'VegasTests.SealedPolicy.prepared_memory' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.SealedPolicy.prepared_memory
