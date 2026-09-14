/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedSourceAssignment

/-! # A native pending disclosure becomes a legal source input

The honest player's opening precedes the focal source choice. Native delivery
lets the focal player copy that opening before its inclusion. The extracted
source policy must copy the corresponding public source binding, using no
runtime history as a source input.
-/

noncomputable section

namespace VegasTests.SealedSourceExtraction

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction Interaction.MessageApplication
open GameTheory.Math.Probability

abbrev Player := Fin 2
abbrev Value := Option Bool

def core : VegasCore Player simpleExpr [] :=
  .commit 0 0 (b := .option .bool)
    (Expr.nullableCommitGuard (Expr.constBool true))
    (.reveal 1 0 0 .here
      (.commit 2 1 (b := .option .bool)
        (Expr.nullableCommitGuard (Expr.constBool true))
        (.reveal 3 1 2 .here (.ret []))))

def source : WFProgram Player simpleExpr where
  core := {
    Γ := []
    prog := core
    env := VEnv.empty simpleExpr
    wctx := by simp
    fresh := by simp [core, FreshBindings, Fresh] }
  accounted := CommitmentAccounting.ofRevealComplete core
    (by simp [core, FreshBindings, Fresh]) [] (by simp) (by decide)
  legal := by
    unfold core
    constructor
    · intro env
      exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
    · constructor
      · intro env
        exact ⟨declineValue .bool, evalExpr_nullableCommitGuard_declineValue _ _⟩
      · trivial

abbrev graph := (compile source.core).graph
def node (index : Fin 4) : Fin graph.nodeCount := index

theorem supported : SealedFragment graph (.option .bool) where
  graphWF := (compile source.core).graphWF
  rowType node := by fin_cases node <;> rfl
  noSamples node dist := by fin_cases node <;> intro h <;> cases h
  commitType node who guard hsem := by fin_cases node <;> cases hsem <;> rfl
  commitGuard node who guard hsem value env := by
    fin_cases node <;> cases hsem <;> cases value <;> rfl
  revealSource node sourceField hsem := by
    fin_cases node
    · cases hsem
    · cases hsem; exact ⟨node 0, 0, _, rfl, rfl⟩
    · cases hsem
    · cases hsem; exact ⟨node 2, 1, _, rfl, rfl⟩

theorem compilation : SealedCompilation source (.option .bool) := ⟨supported⟩
abbrev runtime := supported.resolvingRuntime none 3
abbrev app := runtime.messageApplication

def secondSite : SourceDecisionSite (L := simpleExpr) 1 core
    [(1, .pub (.option .bool)), (0, .sealed 0 (.option .bool))]
    2 (.option .bool) (Expr.nullableCommitGuard (Expr.constBool true)) :=
  .commit (.reveal (.here _ _))

def secondGuard : EventGuard simpleExpr :=
  eventGuardOf (decisionSiteState secondSite source.core.fresh
    (BuildState.fromInitial (initialState [] (VEnv.empty simpleExpr) (by simp)))) 1
    (Expr.nullableCommitGuard (x := 2) (b := .bool) (Expr.constBool true))

def reads (value : Value) : ReadEnv simpleExpr secondGuard.choiceReads where
  read ref href := by
    have htype : ref.ty = .option .bool := by
      change ref ∈ ({⟨1, .option .bool⟩} : Finset (FieldRef simpleExpr)) at href
      exact congrArg FieldRef.ty (Finset.mem_singleton.mp href)
    exact cast (congrArg simpleExpr.Val htype.symm) value

theorem inputs (value : Value) :
    compilation.disclosureInputs 1 (node 2) secondGuard rfl (reads value) =
      fun _ => value := by
  funext coordinate
  simp only [SealedCompilation.disclosureInputs, reads, cast_eq]

def deviator (_history : List app.PlayerEntry) (view : app.View) : app.PlayerCommand :=
  match view.messages.inbox with
  | ⟨_, .opening _ _ value⟩ :: _ => .privateCommand ⟨(2, value)⟩
  | _ => .wait

def environment (history : List app.EnvironmentEntry)
    (_view : app.EnvironmentObservation) : app.EnvironmentPolicyCommand :=
  if history.isEmpty then .include (0, 0) else .deliver 1 (0, 1)

def schedule : List (@Invocation Player) :=
  [.player 0, .player 0, .environment, .player 0, .environment, .player 1]

private def initial := PolicyExecution.initial app (State.initial app runtime.initial)

private def registered (value : Value) : app.PolicyExecution :=
  { initial with
    native := { initial.native with
      application.service := (IdealCommitments.empty.sealValue 0 0 value).state }
    principalHistory := fun who => if who = 0 then
      [⟨State.observe app initial.native 0, .privateCommand ⟨(0, value)⟩⟩] else []
    nativeTrace := [.privateCommand 0 ⟨(0, value)⟩] }

private def submitted (value : Value) : app.PolicyExecution :=
  { registered value with
    native.pool := ((registered value).native.pool.submit 0 (.commitment 0 (0, 0))).2
    principalHistory := fun who => if who = 0 then (registered value).principalHistory 0 ++
      [⟨State.observe app (registered value).native 0, .submit (.commitment 0 (0, 0))⟩]
      else (registered value).principalHistory who
    nativeTrace := (registered value).nativeTrace ++ [.submit 0 (.commitment 0 (0, 0))] }

private def included (value : Value) : app.PolicyExecution :=
  { submitted value with
    native := {
      application := {
        service := (IdealCommitments.empty.sealValue 0 0 value).state
        visible := { events := [.accepted 0 (0, 0)], readyAt := [(0, 0), (1, 0)] } }
      pool := ((submitted value).native.pool.includePending (0, 0)).state
      receipts := [((0, 0), true)] }
    environmentHistory := [⟨State.environmentView app (submitted value).native, .include (0, 0)⟩]
    nativeTrace := (submitted value).nativeTrace ++ [.include (0, 0)] }

private def opened (value : Value) : app.PolicyExecution :=
  { included value with
    native.pool := ((included value).native.pool.submit 0 (.opening 1 (0, 0) value)).2
    principalHistory := fun who => if who = 0 then (included value).principalHistory 0 ++
      [⟨State.observe app (included value).native 0, .submit (.opening 1 (0, 0) value)⟩]
      else (included value).principalHistory who
    nativeTrace := (included value).nativeTrace ++ [.submit 0 (.opening 1 (0, 0) value)] }

private def delivered (value : Value) : app.PolicyExecution :=
  { opened value with
    native.pool := {
      pending := [⟨(0, 1), .opening 1 (0, 0) value⟩]
      ledger := [⟨(0, 0), .commitment 0 (0, 0)⟩]
      inbox := fun who => if who = 1 then [⟨(0, 1), .opening 1 (0, 0) value⟩] else []
      sent := (opened value).native.pool.sent
      nextSerial := (opened value).native.pool.nextSerial }
    environmentHistory := (opened value).environmentHistory ++
      [⟨State.environmentView app (opened value).native, .deliver 1 (0, 1)⟩]
    nativeTrace := (opened value).nativeTrace ++ [.deliver 1 (0, 1)] }

private theorem first_policy (values : Fin graph.nodeCount → Value) :
    supported.resolvingPolicy none 3 0 (supported.valuePolicy values 0)
      [] (State.observe app initial.native 0) =
        FinDist.pure (.privateCommand ⟨(0, values (node 0))⟩ : app.PlayerCommand) := by
  change supported.commitCommand 0 (supported.valuePolicy values 0)
    (node 0) _ rfl [] _ = _
  unfold SealedFragment.commitCommand
  simp only [ChoiceEncoding.cachedValue_nil]
  exact FinDist.map_pure _ _

private theorem register_step (value : Value) :
    app.playerStep 0 initial (.privateCommand ⟨(0, value)⟩) =
      FinDist.pure (registered value) := by
  simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind]
  rfl

private theorem second_policy (value : Value) :
    supported.resolvingPolicy none 3 0 (supported.valuePolicy (fun _ => value) 0)
      ((registered value).principalHistory 0) (State.observe app (registered value).native 0) =
        FinDist.pure (.submit (.commitment 0 (0, 0)) : app.PlayerCommand) := rfl

private theorem submit_step (value : Value) :
    app.playerStep 0 (registered value) (.submit (.commitment 0 (0, 0))) =
      FinDist.pure (submitted value) := by
  simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind]
  rfl

private theorem include_step (value : Value) :
    app.environmentPolicyStep (submitted value) (.include (0, 0)) =
      FinDist.pure (included value) := by
  simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.pure_bind]
  rfl

private theorem third_policy (value : Value) :
    supported.resolvingPolicy none 3 0 (supported.valuePolicy (fun _ => value) 0)
      ((included value).principalHistory 0) (State.observe app (included value).native 0) =
        FinDist.pure (.submit (.opening 1 (0, 0) value) : app.PlayerCommand) := rfl

private theorem open_step (value : Value) :
    app.playerStep 0 (included value) (.submit (.opening 1 (0, 0) value)) =
      FinDist.pure (opened value) := by
  simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind]
  rfl

private theorem delivery_step (value : Value) :
    app.environmentPolicyStep (opened value) (.deliver 1 (0, 1)) =
      FinDist.pure (delivered value) := by
  simp only [environmentPolicyStep, advance, EnvironmentPolicyCommand.toAction,
    MessageApplication.step, FinDist.pure_bind]
  rfl

private theorem copy_policy (value : Value) :
    deviator ((delivered value).principalHistory 1) (State.observe app (delivered value).native 1) =
      .privateCommand ⟨(2, value)⟩ := rfl

theorem pending_copy_law (value : Value) :
    supported.resolvingBindingLaw none 3 (fun _ => value) 1 (node 2)
      (fun history view => FinDist.pure (deviator history view))
      (fun history view => FinDist.pure (environment history view)) schedule =
        FinDist.pure (some value) := by
  simp only [SealedFragment.resolvingBindingLaw, schedule, tracePolicies, invoke,
    SealedFragment.resolvingValuePlayers, GameTheory.Profile.update_same,
    GameTheory.Profile.update_of_ne _ _ (show (0 : Player) ≠ 1 by decide)]
  erw [first_policy (fun _ => value)]
  simp only [FinDist.pure_bind]
  erw [register_step value]
  simp only [FinDist.pure_bind]
  erw [second_policy value]
  simp only [FinDist.pure_bind]
  erw [submit_step value]
  simp only [FinDist.pure_bind]
  erw [include_step value]
  simp only [FinDist.pure_bind]
  erw [third_policy value]
  simp only [FinDist.pure_bind]
  erw [open_step value]
  simp only [FinDist.pure_bind]
  erw [delivery_step value]
  simp only [FinDist.pure_bind]
  erw [copy_policy value]
  simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
    FinDist.pure_bind, FinDist.map_pure]
  rfl

theorem extracted_source_copy (value fallback : Value) :
    (compileSourcePolicy core source.core.fresh
      (BuildState.fromInitial (initialState [] (VEnv.empty simpleExpr) (by simp))) rfl 1
      (compilation.extractedSourcePolicy none 3 1 deviator environment schedule fallback)
      (node 2) secondGuard rfl (reads value)).map Subtype.val = FinDist.pure value := by
  have hlaw := compilation.extractedSourcePolicy_law none 3 1 deviator environment schedule fallback
    (fun _ => value) (node 2) secondGuard rfl (reads value) (inputs value)
  have hbinding := supported.resolvingBinding_law none 3 (fun _ => value) 1
    deviator environment schedule (node 2)
  rw [pending_copy_law] at hbinding
  have hvalue := FinDist.mem_support_pure.mp
    (hbinding ▸ (FinDist.mem_support_pure.mpr rfl))
  simpa only [cast_eq, ← hvalue, Option.getD_some] using! hlaw

private theorem binding_copies_assignment (values : Fin graph.nodeCount → Value) :
    supported.resolvingBinding none 3 values 1 deviator environment schedule (node 2) =
      some (values (node 0)) := by
  have hbound := supported.resolvingBinding_read_bound none 3 values 1
    deviator environment schedule (node 2) secondGuard rfl (fun _ => values (node 0))
  have hagrees : ∀ who, who ≠ (1 : Player) → ∀ index,
      supported.knownBefore 1 (node 2) (who, index.val) →
        values index = values (node 0) := by
    intro who hwho index hknown
    obtain ⟨opening, hbefore, hsem⟩ := supported.priorHonestCoordinates_opening 1
      (node 2) index ⟨who, hwho, hknown⟩
    fin_cases opening
    · cases hsem
    · have hindex : index = node 0 := by
        apply Fin.ext
        change index.val = 0
        have hsource := NodeSem.reveal.inj hsem
        change 0 = 0 + index.val at hsource
        simpa only [Nat.zero_add] using hsource.symm
      rw [hindex]
    · change 2 < 2 at hbefore
      omega
    · change 3 < 2 at hbefore
      omega
  rw [hbound hagrees]
  have hlaw := supported.resolvingBinding_law none 3 (fun _ => values (node 0)) 1
    deviator environment schedule (node 2)
  rw [pending_copy_law] at hlaw
  exact (FinDist.mem_support_pure.mp (hlaw ▸ FinDist.mem_support_pure.mpr rfl)).symm

/-- Complete source play reproduces copying an in-flight opening, for every
honest behavioral kernel and fallback, without postulating input agreement. -/
theorem complete_source_copies (profile : SourceBehavioralProfile core) (fallback : Value)
    (cfg : ReachableConfig graph)
    (hcfg : cfg ∈ (compilation.extractedSourceRun none 3 1 deviator environment schedule
      fallback profile).support) :
    cfg.1.nodeValues (ty := BaseTy.option .bool) fallback (node 2) =
      cfg.1.nodeValues (ty := BaseTy.option .bool) fallback (node 0) := by
  have hconsistent := compilation.extractedSourceRun_consistent none 3 1 deviator environment
    schedule fallback profile cfg hcfg (node 2) secondGuard rfl
  change cfg.1.nodeValues (ty := BaseTy.option .bool) fallback (node 2) =
    (supported.resolvingBinding none 3 (cfg.1.nodeValues fallback) 1
      deviator environment schedule (node 2)).getD fallback at hconsistent
  rw [binding_copies_assignment, Option.getD_some] at hconsistent
  exact hconsistent

/-- The whole-source consistency test has a supported realization for every
profile; its support premise is not an empty-event implication. -/
theorem complete_source_copy_exists (profile : SourceBehavioralProfile core) (fallback : Value) :
    ∃ cfg ∈ (compilation.extractedSourceRun none 3 1 deviator environment schedule
      fallback profile).support,
      cfg.1.nodeValues (ty := BaseTy.option .bool) fallback (node 2) =
        cfg.1.nodeValues (ty := BaseTy.option .bool) fallback (node 0) := by
  obtain ⟨cfg, hcfg⟩ := (compilation.extractedSourceRun none 3 1 deviator environment schedule
    fallback profile).support_nonempty
  exact ⟨cfg, hcfg, complete_source_copies profile fallback cfg hcfg⟩

private theorem first_replay (values : Fin graph.nodeCount → Value) :
    supported.resolvingReplay none 3 values 1 deviator environment [.player 0] =
      .step initial (.finish (registered (values (node 0)))) := by
  have hlaw := supported.resolvingReplay_law none 3 values 1 deviator environment [.player 0]
  simp only [tracePolicies, invoke, SealedFragment.resolvingValuePlayers,
    GameTheory.Profile.update_of_ne _ _ (show (0 : Player) ≠ 1 by decide)] at hlaw
  erw [first_policy values] at hlaw
  simp only [FinDist.pure_bind] at hlaw
  erw [register_step] at hlaw
  simp only [FinDist.pure_bind, FinDist.map_pure] at hlaw
  exact (FinDist.mem_support_pure.mp (hlaw ▸ FinDist.mem_support_pure.mpr rfl)).symm

/-- Every assignment has a fresh replay registration and the selected source
policy's kernel, without requiring that policy to choose the assigned value. -/
theorem initial_registration_kernel (values : Fin graph.nodeCount → Value)
    (policy : SourceBehavioralPolicy core 0) (fallback : Value) :
    let cfg := compilation.assignmentRealization none 3 1 deviator environment [.player 0]
      fallback values
    ∃ (decision : Fin graph.nodeCount) (guard : EventGuard simpleExpr)
        (hsem : (graph.nodeRow decision).sem = .commit 0 guard)
        (input : ReadEnv simpleExpr guard.choiceReads),
        decision.val = 0 ∧ ReadEnv.ofStore? cfg.1.store guard.choiceReads = some input ∧
        compilation.compileResolvingPolicy none 3 0 policy
          [] (State.observe app initial.native 0) =
          ((compileSourcePolicy core source.core.fresh
            (BuildState.fromInitial (initialState [] (VEnv.empty simpleExpr) (by simp)))
            rfl 0 policy) decision guard hsem input).map (fun choice =>
              (.privateCommand ⟨(decision.val,
                cast (congrArg simpleExpr.Val (supported.commitType decision 0 guard hsem))
                  choice.1)⟩ : app.PlayerCommand)) := by
  intro cfg
  have hkernel := compilation.assignmentRealization_registration_kernel none 3 1 deviator
    environment [.player 0] fallback values (fun _ => true)
  dsimp only at hkernel
  rw [first_replay] at hkernel
  simp only [PolicyTrace.prefixThrough] at hkernel
  have hcommand : .privateCommand ⟨(0, values (node 0))⟩ ∈
      (supported.resolvingValuePlayers none 3 values 1
        (fun history view => FinDist.pure (deviator history view)) 0
        [] (State.observe app initial.native 0)).support := by
    rw [SealedFragment.resolvingValuePlayers,
      GameTheory.Profile.update_of_ne _ _ (show (0 : Player) ≠ 1 by decide)]
    rw [first_policy, FinDist.mem_support_pure]
  obtain ⟨decision, guard, hsem, input, hindex, _, hreads, hlaw⟩ :=
    hkernel rfl 0 (by decide) 0 _ hcommand policy
  exact ⟨decision, guard, hsem, input, hindex.symm, hreads, hlaw⟩

/-- An assigned nullable quit is realized even when the compared source
policy deterministically chooses a non-quit. Kernel agreement must retain
the resulting zero probability, not infer support from replay alone. -/
theorem zero_probability_assignment (fallback : Value) :
    (compilation.assignmentRealization none 3 1 deviator environment [.player 0]
      fallback (fun _ => none)).1.nodeValues (ty := BaseTy.option .bool) fallback (node 0) = none ∧
    (.privateCommand ⟨(0, none)⟩ : app.PlayerCommand) ∉
      (compilation.compileResolvingPolicy none 3 0
        (compilation.valueSourceProfile (fun _ => some true) 0)
        [] (State.observe app initial.native 0)).support := by
  constructor
  · exact compilation.assignmentRealization_honest none 3 1 deviator environment [.player 0]
      fallback (fun _ => none) 0 (by decide) (node 0) _ rfl
  · simp only [SealedCompilation.compileResolvingPolicy, SealedCompilation.valueSourceProfile,
      compile_backtranslateCommitPolicy]
    rw [first_policy, FinDist.mem_support_pure]
    intro heq
    cases heq

end VegasTests.SealedSourceExtraction
