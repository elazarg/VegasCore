/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessagePolicyCommands
import Vegas.Graph.MessageServiceCompletion
import Interaction.MessageApplicationPolicyInvariant

/-! # Phase freshness of compiled graph-policy histories -/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction Graph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- Every command retained in `who`'s own history was well-formed for its
observed phase, and that observed phase has not passed the current phase. -/
def HistoryFresh (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution : runtime.application.PolicyExecution) : Prop :=
  ∀ entry ∈ execution.principalHistory who,
    Command.AtPhase runtime who entry.beforeView.application.publicState.pc entry.command ∧
      entry.beforeView.application.publicState.pc ≤ execution.native.application.phase

/-- Player commands prepare or submit messages; only environment inclusion or
application commands can advance the graph cursor. -/
theorem playerStep_phase (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution next : runtime.application.PolicyExecution) (command : Command runtime)
    (supported : next ∈ (runtime.application.playerStep who execution command).support) :
    next.native.application.phase = execution.native.application.phase := by
  have nativeMem : next.native ∈
      ((runtime.application.playerStep who execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.playerStep_native] at nativeMem
  cases command with
  | privateCommand action =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
      exact runtime.privateStep_phase _ who action
  | submit payload | replay id | wait =>
      simp only [MessageApplication.PlayerCommand.toAction, MessageApplication.step,
        FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]

theorem playerStep_phase_mono (runtime : GraphRuntime Player L Δ) (who : Player)
    (execution next : runtime.application.PolicyExecution) (command : Command runtime)
    (supported : next ∈ (runtime.application.playerStep who execution command).support) :
    execution.native.application.phase ≤ next.native.application.phase :=
  (runtime.playerStep_phase who execution next command supported).symm.le

theorem environmentPolicyStep_phase_mono (runtime : GraphRuntime Player L Δ)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (supported : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    execution.native.application.phase ≤ next.native.application.phase := by
  have nativeMem : next.native ∈
      ((runtime.application.environmentPolicyStep execution command).map
        MessageInterface.PolicyExecution.native).support := by
    rw [FinDist.support_map]
    exact ⟨next, supported, rfl⟩
  rw [runtime.application.environmentStep_native] at nativeMem
  cases haction : command.toAction with
  | none =>
      simp only [haction, FinDist.mem_support_pure] at nativeMem
      rw [nativeMem]
  | some action =>
      rw [haction] at nativeMem
      exact runtime.application_step_phase_mono _ _ action nativeMem

/-- Freshness is derived for the actual shared policy run when the fixed
player uses its compiled graph policy. Other players and the environment are
unrestricted. -/
theorem runPolicies_historyFresh (runtime : GraphRuntime Player L Δ)
    (graph : Graph Player L Γ Δ) (who : Player)
    (policy : BehavioralPolicy who graph)
    (players : Player → runtime.application.PlayerPolicy)
    (hwho : players who = runtime.compilePlayerPolicy graph who policy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (initial : HistoryFresh runtime who execution)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    HistoryFresh runtime who next := by
  apply runtime.application.runPolicies_execution_invariant
    (HistoryFresh runtime who) players environment ?_ ?_ schedule execution next initial supported
  · intro current actor command after fresh commandMem stepMem
    have phaseMono := runtime.playerStep_phase_mono actor current after command stepMem
    by_cases hactor : actor = who
    · subst actor
      unfold HistoryFresh
      rw [runtime.application.playerStep_history_self who current command after stepMem]
      intro entry entryMem
      simp only [List.mem_append, List.mem_singleton] at entryMem
      rcases entryMem with old | rfl
      · exact ⟨(fresh entry old).1, (fresh entry old).2.trans phaseMono⟩
      · have atPhase : Command.AtPhase runtime who
            current.native.application.publicView.pc command := by
          rw [hwho] at commandMem
          exact runtime.compilePlayerPolicy_command_atPhase graph who policy
            _ _ command commandMem
        simpa using ⟨atPhase, phaseMono⟩
    · unfold HistoryFresh
      have hne : who ≠ actor := fun eq => hactor eq.symm
      rw [runtime.application.playerStep_other_history actor who hne current command after stepMem]
      intro entry entryMem
      exact ⟨(fresh entry entryMem).1, (fresh entry entryMem).2.trans phaseMono⟩
  · intro current command after fresh _ stepMem
    have phaseMono := runtime.environmentPolicyStep_phase_mono current after command stepMem
    unfold HistoryFresh
    rw [runtime.application.environmentStep_principalHistory current command after stepMem]
    intro entry entryMem
    exact ⟨(fresh entry entryMem).1, (fresh entry entryMem).2.trans phaseMono⟩

theorem initial_historyFresh (runtime : GraphRuntime Player L Δ) (who : Player)
    (state : runtime.application.State) :
    HistoryFresh runtime who
      (MessageApplication.PolicyExecution.initial runtime.application state) := by
  change ∀ entry ∈ ([] : List (Entry runtime)), _
  simp

/-- A compiled own history contains no prepared value addressed to a phase
strictly beyond the execution's current public phase. -/
theorem preparedRaw_eq_none_of_future (runtime : GraphRuntime Player L Δ)
    (who : Player) (execution : runtime.application.PolicyExecution)
    (fresh : HistoryFresh runtime who execution) (site : Nat)
    (future : execution.native.application.phase < site) :
    preparedRaw (execution.principalHistory who) site = none := by
  rw [preparedRaw, List.findSome?_eq_none_iff]
  intro entry entryMem
  obtain ⟨atPhase, beforeLe⟩ := fresh entry entryMem
  obtain ⟨before, command⟩ := entry
  change before.application.publicState.pc ≤ execution.native.application.phase at beforeLe
  cases command with
  | privateCommand command =>
      cases command with
      | prepare slot raw =>
          simp only [Command.AtPhase] at atPhase
          simp only
          split
          · rename_i eq
            omega
          · rfl
      | rememberDisclosure => rfl
  | submit payload => cases payload <;> simp
  | replay => simp
  | wait => simp

/-- Compiler-private disclosure memory is likewise empty at a strictly future
phase. -/
theorem rememberedDisclosure_eq_none_of_future (runtime : GraphRuntime Player L Δ)
    (who : Player) (execution : runtime.application.PolicyExecution)
    (fresh : HistoryFresh runtime who execution) (site : Nat)
    (future : execution.native.application.phase < site) :
    rememberedDisclosure (execution.principalHistory who) site = none := by
  rw [rememberedDisclosure, List.findSome?_eq_none_iff]
  intro entry entryMem
  obtain ⟨_, beforeLe⟩ := fresh entry entryMem
  obtain ⟨before, command⟩ := entry
  change before.application.publicState.pc ≤ execution.native.application.phase at beforeLe
  cases command with
  | privateCommand command =>
      cases command with
      | prepare => rfl
      | rememberDisclosure =>
          simp only
          split
          · rename_i eq
            omega
          · rfl
  | submit payload => cases payload <;> simp
  | replay => simp
  | wait => simp

/-- No prescribed submission in actual own history can target a strictly
future phase. -/
theorem submittedAt_eq_false_of_future (runtime : GraphRuntime Player L Δ)
    (who : Player) (execution : runtime.application.PolicyExecution)
    (fresh : HistoryFresh runtime who execution) (site : Nat)
    (future : execution.native.application.phase < site) :
    submittedAt (execution.principalHistory who) site = false := by
  rw [submittedAt, List.any_eq_false]
  intro entry entryMem
  obtain ⟨atPhase, beforeLe⟩ := fresh entry entryMem
  obtain ⟨before, command⟩ := entry
  change before.application.publicState.pc ≤ execution.native.application.phase at beforeLe
  cases command with
  | privateCommand command => cases command <;> simp
  | submit payload =>
      cases payload with
      | commitment submittedSite handle =>
          change submittedSite = before.application.publicState.pc ∧ _ at atPhase
          have ne : submittedSite ≠ site := by omega
          simp [ne]
      | opening submittedSite handle raw =>
          change submittedSite = before.application.publicState.pc at atPhase
          have ne : submittedSite ≠ site := by omega
          simp [ne]
      | withhold submittedSite =>
          change submittedSite = before.application.publicState.pc at atPhase
          have ne : submittedSite ≠ site := by omega
          simp [ne]
      | malformed => simp
  | replay => simp
  | wait => simp

end Vegas.GraphRuntime
