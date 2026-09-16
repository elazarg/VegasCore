/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReplayApplication
import Vegas.Pending.ReplayHistory

/-! # Replay of unchanged players' compiled commands -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ₀ Γ Δ : VCtx Player L}

/-- Compiled players expose the same command, or privately record potentially
different values at the same logical site. -/
inductive PairedCommands (runtime : GraphRuntime Player L Δ) :
    Command runtime → Command runtime → Prop where
  | same (command) : PairedCommands runtime command command
  | prepare (site : Nat) (left right : Raw L) :
      PairedCommands runtime (.privateCommand (.prepare site left))
        (.privateCommand (.prepare site right))
  | remember (left right : Bool) :
      PairedCommands runtime (.privateCommand (.rememberDisclosure left))
        (.privateCommand (.rememberDisclosure right))

/-- The publication equality needed for replay concerns only a cached resolve
at the current cursor, not private binding choices or remembered intentions. -/
def CachedResultsAgree (runtime : GraphRuntime Player L Δ) (owner : Player)
    (leftHistory rightHistory : List (Entry runtime)) (site : Nat) :
    {Γ : VCtx Player L} → (suffix : Graph Player L Γ Δ) → VEnv L Γ → VEnv L Γ → Prop
  | _, .resolve _ nodeOwner _ _ source checks _, leftIdeal, rightIdeal =>
      nodeOwner = owner → ∀ left right,
        rememberedDisclosure leftHistory site = some left →
        rememberedDisclosure rightHistory site = some right →
        acceptedResult source checks leftIdeal left =
          acceptedResult source checks rightIdeal right
  | _, _, _, _ => True

/-- Branches of an unchanged compiled policy synchronize without equating its
private draws. Guarded disclosure is synchronized by its eventual result. -/
theorem compileAt_pairedCommands
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (owner focal : Player) (suffix : Graph Player L Γ Δ)
    (policy : BehavioralPolicy owner suffix)
    (left right : runtime.application.PolicyExecution)
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (leftPublic : (checkpoint.publicValues : PublicValues Γ) =
      (PublicValues.ofVEnv checkpoint.leftIdeal : PublicValues Γ))
    (rightPublic : (checkpoint.publicValues : PublicValues Γ) =
      (PublicValues.ofVEnv checkpoint.rightIdeal : PublicValues Γ))
    (shape : CacheShape (left.principalHistory owner) (right.principalHistory owner))
    (results : CachedResultsAgree runtime owner (left.principalHistory owner)
      (right.principalHistory owner) checkpoint.pc suffix
      checkpoint.leftIdeal checkpoint.rightIdeal)
    (leftCommand rightCommand : Command runtime)
    (leftSupported : leftCommand ∈ (runtime.compileAt owner whole suffix policy checkpoint.pc
      (left.principalHistory owner)
      (MessageApplication.State.observe runtime.application left.native owner)).support)
    (rightSupported : rightCommand ∈ (runtime.compileAt owner whole suffix policy checkpoint.pc
      (right.principalHistory owner)
      (MessageApplication.State.observe runtime.application right.native owner)).support) :
    PairedCommands runtime leftCommand rightCommand := by
  let leftView := MessageApplication.State.observe runtime.application left.native owner
  let rightView := MessageApplication.State.observe runtime.application right.native owner
  have leftPc : leftView.application.publicState.pc = checkpoint.pc := by
    change left.native.application.publicView.pc = checkpoint.pc
    rw [checkpoint.leftState]; rfl
  have rightPc : rightView.application.publicState.pc = checkpoint.pc := by
    change right.native.application.publicView.pc = checkpoint.pc
    rw [checkpoint.rightState]; rfl
  have leftWho : leftView.application.who = owner := rfl
  have rightWho : rightView.application.who = owner := rfl
  have leftCtx : leftView.application.publicState.Γ = Γ := by
    change left.native.application.publicView.Γ = Γ
    rw [checkpoint.leftState]; rfl
  have rightCtx : rightView.application.publicState.Γ = Γ := by
    change right.native.application.publicView.Γ = Γ
    rw [checkpoint.rightState]; rfl
  dsimp only [leftView] at leftPc leftWho leftCtx
  dsimp only [rightView] at rightPc rightWho rightCtx
  cases suffix with
  | ret =>
      simp only [compileAt, FinDist.mem_support_pure] at leftSupported rightSupported
      subst leftCommand; subst rightCommand; exact .same _
  | sample =>
      simp only [compileAt, leftPc, rightPc, if_true, FinDist.mem_support_pure]
        at leftSupported rightSupported
      subst leftCommand; subst rightCommand; exact .same _
  | bind name nodeOwner fresh tail =>
      by_cases owned : nodeOwner = owner
      · subst nodeOwner
        cases submitted : submittedAt (left.principalHistory owner) checkpoint.pc with
        | true =>
            have rightSubmitted := (shape.submitted checkpoint.pc).symm.trans submitted
            simp only [compileAt, leftPc, rightPc, dif_pos, submitted, rightSubmitted,
              if_true, FinDist.mem_support_pure] at leftSupported rightSupported
            subst leftCommand; subst rightCommand; exact .same _
        | false =>
            have rightSubmitted := (shape.submitted checkpoint.pc).symm.trans submitted
            cases prepared : preparedRaw (left.principalHistory owner) checkpoint.pc with
            | none =>
                have rightPrepared : preparedRaw (right.principalHistory owner) checkpoint.pc =
                    none := by
                  have flag := shape.prepared checkpoint.pc
                  rw [prepared] at flag
                  cases found : preparedRaw (right.principalHistory owner) checkpoint.pc
                  · rfl
                  · simp [found] at flag
                rw [compileAt_bind_fresh runtime whole _ name owner fresh tail policy _ _
                  leftPc leftWho leftCtx prepared submitted] at leftSupported
                rw [compileAt_bind_fresh runtime whole _ name owner fresh tail policy _ _
                  rightPc rightWho rightCtx rightPrepared rightSubmitted] at rightSupported
                rw [FinDist.support_map] at leftSupported rightSupported
                obtain ⟨leftChoice, _, rfl⟩ := leftSupported
                obtain ⟨rightChoice, _, rfl⟩ := rightSupported
                exact .prepare _ _ _
            | some raw =>
                have rightPrepared : ∃ value,
                    preparedRaw (right.principalHistory owner) checkpoint.pc = some value := by
                  apply Option.isSome_iff_exists.mp
                  rw [← shape.prepared, prepared]; rfl
                obtain ⟨rightRaw, rightPrepared⟩ := rightPrepared
                rw [compileAt_bind_prepared runtime whole _ name owner fresh tail policy _ _ raw
                  leftPc prepared submitted, FinDist.mem_support_pure] at leftSupported
                rw [compileAt_bind_prepared runtime whole _ name owner fresh tail policy _ _
                  rightRaw rightPc rightPrepared rightSubmitted, FinDist.mem_support_pure]
                  at rightSupported
                subst leftCommand; subst rightCommand; exact .same _
      · simp only [compileAt, leftPc, rightPc, dif_pos, dif_neg owned,
          FinDist.mem_support_pure] at leftSupported rightSupported
        subst leftCommand; subst rightCommand; exact .same _
  | resolve outputName nodeOwner bindingName fresh source checks tail =>
      by_cases owned : nodeOwner = owner
      · subst nodeOwner
        cases submitted : submittedAt (left.principalHistory owner) checkpoint.pc with
        | true =>
            have rightSubmitted := (shape.submitted checkpoint.pc).symm.trans submitted
            simp only [compileAt, leftPc, rightPc, dif_pos, submitted, rightSubmitted,
              if_true, FinDist.mem_support_pure] at leftSupported rightSupported
            subst leftCommand; subst rightCommand; exact .same _
        | false =>
            have rightSubmitted := (shape.submitted checkpoint.pc).symm.trans submitted
            cases remembered : rememberedDisclosure (left.principalHistory owner)
                checkpoint.pc with
            | none =>
                have rightRemembered : rememberedDisclosure (right.principalHistory owner)
                    checkpoint.pc = none := by
                  have flag := shape.remembered checkpoint.pc
                  rw [remembered] at flag
                  cases found : rememberedDisclosure (right.principalHistory owner) checkpoint.pc
                  · rfl
                  · simp [found] at flag
                rw [compileAt_resolve_fresh runtime whole _ outputName bindingName owner fresh
                  source checks tail policy _ _ leftPc leftWho leftCtx remembered submitted]
                  at leftSupported
                rw [compileAt_resolve_fresh runtime whole _ outputName bindingName owner fresh
                  source checks tail policy _ _ rightPc rightWho rightCtx rightRemembered
                  rightSubmitted] at rightSupported
                rw [FinDist.support_map] at leftSupported rightSupported
                obtain ⟨leftChoice, _, rfl⟩ := leftSupported
                obtain ⟨rightChoice, _, rfl⟩ := rightSupported
                exact .remember _ _
            | some disclose =>
                have rightRemembered : ∃ value,
                    rememberedDisclosure (right.principalHistory owner) checkpoint.pc =
                      some value := by
                  apply Option.isSome_iff_exists.mp
                  rw [← shape.remembered, remembered]; rfl
                obtain ⟨rightDisclose, rightRemembered⟩ := rightRemembered
                have resultEq := results rfl disclose rightDisclose remembered rightRemembered
                rw [compileAt_resolve_result runtime whole outputName bindingName owner fresh
                  source checks tail policy _ left.native checkpoint.leftIdeal checkpoint.bindings
                  checkpoint.leftCandidates checkpoint.pc checkpoint.clock checkpoint.enteredAt
                  disclose (checkpoint.leftState.trans (by rw [leftPublic]))
                  remembered submitted, FinDist.mem_support_pure] at leftSupported
                rw [compileAt_resolve_result runtime whole outputName bindingName owner fresh
                  source checks tail policy _ right.native checkpoint.rightIdeal checkpoint.bindings
                  checkpoint.rightCandidates checkpoint.pc checkpoint.clock checkpoint.enteredAt
                  rightDisclose (checkpoint.rightState.trans (by rw [rightPublic]))
                  rightRemembered rightSubmitted, FinDist.mem_support_pure] at rightSupported
                rw [resultEq] at leftSupported
                exact leftSupported ▸ rightSupported ▸ .same _
      · simp only [compileAt, leftPc, rightPc, dif_pos, dif_neg owned,
          FinDist.mem_support_pure] at leftSupported rightSupported
        subst leftCommand; subst rightCommand; exact .same _

/-- A foreign player cannot alter any of the focal player's candidate slots,
including initial-field handles that do not occur in its preparation view. -/
theorem playerStep_other_candidates (runtime : GraphRuntime Player L Δ)
    (owner focal : Player) (different : owner ≠ focal)
    (execution next : runtime.application.PolicyExecution) (command : Command runtime)
    (supported : next ∈ (runtime.application.playerStep owner execution command).support)
    (slot : Slot) :
    next.native.application.candidates.lookup (focal, slot) =
      execution.native.application.candidates.lookup (focal, slot) := by
  have native : next.native ∈
      ((runtime.application.playerStep owner execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.playerStep_native] at native
  cases command with
  | privateCommand privateCommand =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
      change CommitmentCandidates.lookup
        (runtime.privateStep execution.native.application owner privateCommand).candidates
        (focal, slot) = _
      cases state : execution.native.application
      cases privateCommand with
      | rememberDisclosure => rfl
      | prepare site raw =>
          apply CommitmentCandidates.lookup_prepare_other
          intro same
          exact different (congrArg Prod.fst same).symm
  | submit payload | replay id =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at native
      rw [native]
  | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, FinDist.mem_support_pure] at native
      rw [native]

/-- Paired compiled commands retain the full focal/service input, every focal
candidate, and the unchanged player's cache shape. -/
theorem PairedCommands.playerStep_replay
    {runtime : GraphRuntime Player L Δ} {focal owner : Player}
    (different : owner ≠ focal) {suffix : Graph Player L Γ Δ}
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (shape : CacheShape (left.principalHistory owner) (right.principalHistory owner))
    {leftCommand rightCommand : Command runtime}
    (paired : PairedCommands runtime leftCommand rightCommand)
    (leftSupported : leftNext ∈
      (runtime.application.playerStep owner left leftCommand).support)
    (rightSupported : rightNext ∈
      (runtime.application.playerStep owner right rightCommand).support) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      leftNext.native.application.focalReplayKey focal =
        rightNext.native.application.focalReplayKey focal ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native ∧
      CacheShape (leftNext.principalHistory owner) (rightNext.principalHistory owner) := by
  have inputEq : focalServiceInput runtime focal leftNext =
      focalServiceInput runtime focal rightNext := by
    cases paired with
    | same command =>
        exact nonfocal_sameCommand_focalServiceInput_eq runtime focal owner (Ne.symm different)
          left right leftNext rightNext _ checkpoint.focalServiceInput_eq
          leftSupported rightSupported
    | prepare site leftRaw rightRaw =>
        exact nonfocal_privateSteps_focalServiceInput_eq runtime focal owner (Ne.symm different)
          left right leftNext rightNext (.prepare site leftRaw) (.prepare site rightRaw)
          checkpoint.focalServiceInput_eq leftSupported rightSupported
    | remember leftDisclose rightDisclose =>
        exact nonfocal_privateSteps_focalServiceInput_eq runtime focal owner (Ne.symm different)
          left right leftNext rightNext (.rememberDisclosure leftDisclose)
          (.rememberDisclosure rightDisclose) checkpoint.focalServiceInput_eq
          leftSupported rightSupported
  have key : leftNext.native.application.focalReplayKey focal =
      rightNext.native.application.focalReplayKey focal := by
    apply Prod.ext
    · exact congrArg MessageInterface.View.application (congrArg Prod.snd
        (congrArg Prod.fst inputEq))
    · funext slot
      change leftNext.native.application.candidates.lookup (focal, slot) =
        rightNext.native.application.candidates.lookup (focal, slot)
      rw [playerStep_other_candidates runtime owner focal different left leftNext
        leftCommand leftSupported slot,
        playerStep_other_candidates runtime owner focal different right rightNext
          rightCommand rightSupported slot, checkpoint.leftState, checkpoint.rightState]
      exact checkpoint.focalCandidates slot
  refine ⟨congrArg Prod.fst (congrArg Prod.fst inputEq),
    congrArg Prod.fst (congrArg Prod.snd inputEq), key,
    congrArg Prod.snd (congrArg Prod.snd inputEq), ?_⟩
  rw [runtime.application.playerStep_history_self owner left leftCommand leftNext leftSupported,
    runtime.application.playerStep_history_self owner right rightCommand rightNext rightSupported]
  have phase : left.native.application.publicView.pc =
      right.native.application.publicView.pc := by
    rw [checkpoint.leftState, checkpoint.rightState]
    rfl
  cases paired with
  | same command => exact shape.append_same_command _ _ _ phase
  | prepare site leftRaw rightRaw => exact shape.append_prepare _ _ site leftRaw rightRaw
  | remember leftDisclose rightDisclose =>
      exact shape.append_remember _ _ leftDisclose rightDisclose phase

/-- An actual invocation of an unchanged nonfocal compiled policy preserves
the replay fields and its cache shape. The only value agreement required is
the result of any cached disclosure at the current cursor. -/
theorem FocalReplayCheckpoint.compiled_nonfocal_invoke_replay
    (runtime : GraphRuntime Player L Δ) (whole : Graph Player L Γ₀ Δ)
    (owner focal : Player) (different : owner ≠ focal)
    (suffix : Graph Player L Γ Δ) (policy : BehavioralPolicy owner whole)
    (players : Player → runtime.application.PlayerPolicy)
    (compiled : players owner = runtime.compilePlayerPolicy whole owner policy)
    (environment : runtime.application.EnvironmentPolicy)
    (left right leftNext rightNext : runtime.application.PolicyExecution)
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (walk : Prefix Δ whole suffix checkpoint.pc)
    (leftPublic : (checkpoint.publicValues : PublicValues Γ) =
      (PublicValues.ofVEnv checkpoint.leftIdeal : PublicValues Γ))
    (rightPublic : (checkpoint.publicValues : PublicValues Γ) =
      (PublicValues.ofVEnv checkpoint.rightIdeal : PublicValues Γ))
    (shape : CacheShape (left.principalHistory owner) (right.principalHistory owner))
    (results : CachedResultsAgree runtime owner (left.principalHistory owner)
      (right.principalHistory owner) checkpoint.pc suffix
      checkpoint.leftIdeal checkpoint.rightIdeal)
    (leftSupported : leftNext ∈
      (runtime.application.invoke players environment left (.player owner)).support)
    (rightSupported : rightNext ∈
      (runtime.application.invoke players environment right (.player owner)).support) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      leftNext.native.application.focalReplayKey focal =
        rightNext.native.application.focalReplayKey focal ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native ∧
      CacheShape (leftNext.principalHistory owner) (rightNext.principalHistory owner) := by
  simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion]
    at leftSupported rightSupported
  obtain ⟨leftCommand, leftChosen, leftStep⟩ := leftSupported
  obtain ⟨rightCommand, rightChosen, rightStep⟩ := rightSupported
  rw [compiled, walk.compilePlayerPolicy_eq_suffix owner policy _ _ (by
    change left.native.application.publicView.pc = checkpoint.pc
    rw [checkpoint.leftState]; rfl)] at leftChosen
  rw [compiled, walk.compilePlayerPolicy_eq_suffix owner policy _ _ (by
    change right.native.application.publicView.pc = checkpoint.pc
    rw [checkpoint.rightState]; rfl)] at rightChosen
  exact (compileAt_pairedCommands runtime whole owner focal suffix
    (walk.policyTail owner policy) left right checkpoint leftPublic rightPublic shape results
    leftCommand rightCommand leftChosen rightChosen).playerStep_replay different checkpoint
      shape leftStep rightStep

/-- The deviator's same command preserves the full replay key, including the
initial handles omitted from its explicit preparation catalogue. -/
theorem FocalReplayCheckpoint.focal_playerStep_replay
    (runtime : GraphRuntime Player L Δ) (focal : Player)
    {suffix : Graph Player L Γ Δ}
    {left right leftNext rightNext : runtime.application.PolicyExecution}
    (checkpoint : FocalReplayCheckpoint runtime focal suffix left right)
    (command : Command runtime)
    (leftSupported : leftNext ∈ (runtime.application.playerStep focal left command).support)
    (rightSupported : rightNext ∈ (runtime.application.playerStep focal right command).support) :
    leftNext.principalHistory focal = rightNext.principalHistory focal ∧
      leftNext.environmentHistory = rightNext.environmentHistory ∧
      leftNext.native.application.focalReplayKey focal =
        rightNext.native.application.focalReplayKey focal ∧
      MessageApplication.State.environmentView runtime.application leftNext.native =
        MessageApplication.State.environmentView runtime.application rightNext.native := by
  have inputEq := focal_sameCommand_focalServiceInput_eq runtime focal checkpoint command
    leftSupported rightSupported
  refine ⟨congrArg Prod.fst (congrArg Prod.fst inputEq),
    congrArg Prod.fst (congrArg Prod.snd inputEq), ?_,
    congrArg Prod.snd (congrArg Prod.snd inputEq)⟩
  apply Prod.ext
  · exact congrArg MessageInterface.View.application (congrArg Prod.snd
      (congrArg Prod.fst inputEq))
  · funext slot
    change leftNext.native.application.candidates.lookup (focal, slot) =
      rightNext.native.application.candidates.lookup (focal, slot)
    have leftNative : leftNext.native ∈
        ((runtime.application.playerStep focal left command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨leftNext, leftSupported, rfl⟩
    have rightNative : rightNext.native ∈
        ((runtime.application.playerStep focal right command).map
          MessageInterface.PolicyExecution.native).support := by
      rw [FinDist.support_map]
      exact ⟨rightNext, rightSupported, rfl⟩
    rw [runtime.application.playerStep_native] at leftNative rightNative
    cases command with
    | privateCommand privateCommand =>
        simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at leftNative rightNative
        rw [leftNative, rightNative]
        change CommitmentCandidates.lookup
            (runtime.privateStep left.native.application focal privateCommand).candidates
            (focal, slot) =
          CommitmentCandidates.lookup
            (runtime.privateStep right.native.application focal privateCommand).candidates
            (focal, slot)
        rw [checkpoint.leftState, checkpoint.rightState]
        cases privateCommand with
        | rememberDisclosure => exact checkpoint.focalCandidates slot
        | prepare site raw =>
            change (checkpoint.leftCandidates.prepare focal (.prepared site) raw).lookup
                (focal, slot) =
              (checkpoint.rightCandidates.prepare focal (.prepared site) raw).lookup (focal, slot)
            apply CommitmentCandidates.prepare_lookup_eq_of_known
              (known := fun handle => handle.1 = focal) ?_ focal (.prepared site) raw raw
                (fun _ => rfl) (focal, slot) rfl
            intro handle owned
            obtain ⟨owner, slot⟩ := handle
            dsimp only at owned
            subst owner
            exact checkpoint.focalCandidates slot
    | submit payload | replay id =>
        simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
          FinDist.mem_support_pure] at leftNative rightNative
        rw [leftNative, rightNative]
        change left.native.application.candidates.lookup (focal, slot) =
          right.native.application.candidates.lookup (focal, slot)
        rw [checkpoint.leftState, checkpoint.rightState]
        exact checkpoint.focalCandidates slot
    | wait =>
        simp only [MessageApplication.PlayerCommand.toAction, FinDist.mem_support_pure]
          at leftNative rightNative
        rw [leftNative, rightNative, checkpoint.leftState, checkpoint.rightState]
        exact checkpoint.focalCandidates slot

end Vegas.GraphRuntime
