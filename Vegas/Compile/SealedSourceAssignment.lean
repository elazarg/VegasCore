/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceRealization
import Vegas.Compile.SealedSourceChoices

/-! # Source realizations of every honest assignment

Fix the same extracted focal policy and realize arbitrary honest values using
legal deterministic source policies. This supplies source inputs throughout
each replay cylinder, including assignments outside the support of the honest
profile whose probabilities are being compared. No new evaluator or runtime
is introduced: realizations come from the existing source-policy execution.
-/

noncomputable section

namespace Vegas.SealedCompilation

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (compilation : SealedCompilation source ty)

variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerEntry →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.View →
  (compilation.supported.resolvingRuntime nullValue window).messageApplication.PlayerCommand)
variable (environment :
  List
    (compilation.supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  MessageApplication.EnvironmentObservation
    (compilation.supported.resolvingRuntime nullValue window).messageApplication →
  MessageApplication.EnvironmentPolicyCommand
    (compilation.supported.resolvingRuntime nullValue window).messageApplication)
variable (schedule : List (@Invocation Player)) (fallback : L.Val ty)
variable (values : Fin (compile source.core).graph.nodeCount → L.Val ty)

/-- A complete source realization with assigned honest choices and the same
extracted focal policy. Existence follows from normalized source execution,
independently of the support of any other source profile. -/
def assignmentRealization : ReachableConfig (compile source.core).graph :=
  Classical.choose (compilation.extractedSourceRun nullValue window focal deviator environment
    schedule fallback (compilation.valueSourceProfile values)).support_nonempty

private theorem assignmentRealization_mem :
    compilation.assignmentRealization nullValue window focal deviator environment schedule
      fallback values ∈
        (compilation.extractedSourceRun nullValue window focal deviator environment schedule
          fallback (compilation.valueSourceProfile values)).support :=
  Classical.choose_spec (compilation.extractedSourceRun nullValue window focal deviator environment
    schedule fallback (compilation.valueSourceProfile values)).support_nonempty

/-- Every honest commitment in the complete source retains the assigned
value. The focal player's extracted policy is not replaced by that assignment. -/
theorem assignmentRealization_honest (who : Player) (hwho : who ≠ focal)
    (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
    (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard) :
    (compilation.assignmentRealization nullValue window focal deviator environment schedule
      fallback values).1.nodeValues fallback node = values node := by
  let cfg := compilation.assignmentRealization nullValue window focal deviator environment schedule
    fallback values
  have hcfg := compilation.assignmentRealization_mem nullValue window focal deviator environment
    schedule fallback values
  have hterminal := compilation.extractedSourceRun_terminal nullValue window focal deviator
    environment schedule fallback (compilation.valueSourceProfile values) cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues (compile source.core).graphWF
    (compile_guardLive source.core source.legal) _ _ (CommitValuesSupported.initial _)
    (compile source.core).graph.nodeOrder cfg hcfg
  obtain ⟨reads, _, choice, hchoice, hvalue⟩ := hchoices node (hterminal node) who guard hsem
  rw [Profile.update_of_ne _ _ hwho] at hchoice
  simp only [valueSourceProfile, compile_backtranslateCommitPolicy,
    EventGraph.SealedFragment.assignedCommitPolicy, FinDist.mem_support_pure] at hchoice
  subst choice
  change cfg.1.store ((compile source.core).graph.nodeTarget node) =
    some (⟨guard.ty, cast (congrArg L.Val
      (compilation.supported.commitType node who guard hsem).symm) (values node)⟩ : TypedValue L)
    at hvalue
  change cfg.1.nodeValues fallback node = values node
  rw [Config.nodeValues, Store.getAs, hvalue]
  simp only [TypedValue.as?, dif_pos (compilation.supported.commitType node who guard hsem),
    cast_cast, cast_eq, Option.getD_some]

/-- Source realization does not change any native replay snapshot. Values at
focal and reveal coordinates are ignored by honest value-substituted policies. -/
theorem assignmentRealization_replay :
    compilation.supported.resolvingReplay nullValue window
        ((compilation.assignmentRealization nullValue window focal deviator environment schedule
          fallback values).1.nodeValues fallback) focal deviator environment schedule =
      compilation.supported.resolvingReplay nullValue window values focal deviator environment
        schedule :=
  compilation.supported.resolvingReplay_congr nullValue window _ focal deviator environment
    schedule values (compilation.assignmentRealization_honest nullValue window focal deviator
      environment schedule fallback values)

/-- For every honest assignment, each fresh pre-timeout replay registration
uses the selected source policy's kernel at that assignment's complete source
inputs. No positive-probability assumption for that policy is required. -/
theorem assignmentRealization_registration_kernel
    (release :
      (compilation.supported.resolvingRuntime nullValue window).messageApplication.PolicyExecution →
        Bool) :
    let cfg := compilation.assignmentRealization nullValue window focal deviator environment
      schedule fallback values
    let runtime := compilation.supported.resolvingRuntime nullValue window
    let stopped := ((compilation.supported.resolvingReplay nullValue window values focal
      deviator environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)).firstRelease release
    stopped.native.application.visible.timeouts = [] →
    ∀ who, who ≠ focal → ∀ slot value,
      .privateCommand ⟨(slot, value)⟩ ∈
        (compilation.supported.resolvingValuePlayers nullValue window values focal
          (fun history view => FinDist.pure (deviator history view)) who
          (stopped.principalHistory who)
          (State.observe runtime.messageApplication stopped.native who)).support →
      ∀ policy : SourceBehavioralPolicy source.core.prog who,
      ∃ (node : Fin (compile source.core).graph.nodeCount) (guard : EventGuard L)
        (hsem : ((compile source.core).graph.nodeRow node).sem = .commit who guard)
        (reads : ReadEnv L guard.choiceReads),
        slot = node.val ∧ stopped.native.application.service.lookup (who, node.val) = none ∧
        ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads ∧
        compilation.compileResolvingPolicy nullValue window who policy
          (stopped.principalHistory who) (State.observe runtime.messageApplication stopped.native
            who) =
          ((compileSourcePolicy source.core.prog source.core.fresh
            (BuildState.fromInitial (initialState source.core.Γ source.core.env source.core.wctx))
            rfl who policy) node guard hsem reads).map (fun choice =>
              .privateCommand ⟨(node.val, cast (congrArg L.Val
                (compilation.supported.commitType node who guard hsem)) choice.1)⟩) := by
  intro cfg runtime stopped hclear who hwho slot value hcommand policy
  have hkernel := compilation.extractedSourceRun_registration_kernel nullValue window focal
    deviator environment schedule fallback (compilation.valueSourceProfile values) cfg
    (compilation.assignmentRealization_mem nullValue window focal deviator environment
      schedule fallback values) release
  have hplayers := compilation.supported.resolvingValuePlayers_congr nullValue window
    (cfg.1.nodeValues fallback) values focal
    (fun history view => FinDist.pure (deviator history view))
    (compilation.assignmentRealization_honest nullValue window focal deviator environment
      schedule fallback values)
  have hreplay := compilation.assignmentRealization_replay nullValue window focal deviator
    environment schedule fallback values
  dsimp only at hkernel
  rw [hreplay, hplayers] at hkernel
  exact hkernel hclear who hwho slot value hcommand policy

end Vegas.SealedCompilation

/-- info: 'Vegas.SealedCompilation.assignmentRealization_honest' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.assignmentRealization_honest

/-- info: 'Vegas.SealedCompilation.assignmentRealization_registration_kernel' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.SealedCompilation.assignmentRealization_registration_kernel
