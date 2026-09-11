/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedBlockDeterminism
import Vegas.Compile.WindowedExpiry
import Vegas.Compile.ApplicationRelayHistory

/-! # Cache freshness through sample blocks -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A sample instruction has neither an ordinary submitter nor an expiry
payload, so every one of its three player polls is an unconditional wait. -/
theorem blockPlayer_sample_wait (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (code : SampleCode L)
    (hindex : runtime.image.instructions[history.length / 3]? = some (.sample code))
    (hlookup : runtime.image.lookup code.node = some (.sample code)) :
    runtime.blockPlayer who base history view = FinDist.pure .wait := by
  simp only [blockPlayer, hindex]
  split
  · split
    · rfl
    · unfold relayCommand
      have hdue : runtime.dueExpiry? view.application = none := by
        unfold dueExpiry?
        cases hactivation : view.application.2 with
        | none => simp
        | some activation =>
            simp only [Option.bind_eq_bind, Option.bind_some]
            split
            · rename_i hactive
              have hkey : activation.key = code.node := by
                exact Option.some.inj (hactive.1.symm.trans ‹_ = _›)
              simp [hkey, hlookup, ApplicationInstruction.expiryPayload?]
            · rfl
      rw [hdue]
  · rfl

end Vegas.WindowedApplication

namespace Vegas.ApplicationPlan

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability WindowedApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {state : Vegas.ToEventGraph.BuildState P L Γ}

/-- A windowed wait appends only an erased wait entry, which no generated
instruction recognizes as a cached source command. -/
theorem RemainingUnchangedCachesEmpty.playerStep_wait
    (runtime : WindowedApplication P L) (cacheImage : ApplicationImage P L)
    (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (focal actor : P)
    (execution next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.playerStep actor execution .wait).support)
    (hfresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution execution)) :
    RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution next) := by
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
  subst next
  unfold RemainingUnchangedCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  obtain howner | hempty :=
    (List.forall_iff_forall_mem.mp hfresh) instruction hinstruction
  · exact Or.inl howner
  · right
    apply instruction.cacheEmpty_playerStep cacheImage actor
      (runtime.eraseExecution execution) .wait _
    · simp only [MessageApplication.playerStep, PlayerCommand.toAction,
        MessageApplication.advance, FinDist.pure_bind]
      rw [FinDist.mem_support_pure]
      dsimp only [WindowedApplication.eraseExecution]
      congr 1
      funext other
      by_cases hother : other = actor
      · subst other
        simp only [if_pos, List.map_append, List.map_cons, List.map_nil,
          WindowedApplication.erasePlayerEntry]
        rfl
      · simp only [hother, if_false]
    · exact hempty
    · exact instruction.idleOrExpiry_rejectsCommand cacheImage actor .wait (by simp)

/-- The focal actor may take an arbitrary command: caches assigned to it are
exempt, while every other instruction reads a different principal history. -/
theorem RemainingUnchangedCachesEmpty.playerStep_focal
    (runtime : WindowedApplication P L) (cacheImage : ApplicationImage P L)
    (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (focal : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hnext : next ∈ (runtime.application.playerStep focal execution command).support)
    (hfresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution execution)) :
    RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution next) := by
  unfold RemainingUnchangedCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  by_cases howner : instruction.submitter = some focal
  · exact Or.inl howner
  · right
    have hempty := (List.forall_iff_forall_mem.mp hfresh) instruction hinstruction
    rcases hempty with hempty | hempty
    · exact False.elim (howner hempty)
    · cases instruction with
      | sample code => trivial
      | bind code =>
          have hne : code.owner ≠ focal := by
            intro heq
            apply howner
            simpa [ApplicationInstruction.submitter] using congrArg some heq
          have hhistory := runtime.application.playerStep_other_history
            focal code.owner hne execution command next hnext
          simpa [ApplicationInstruction.CacheEmpty, WindowedApplication.eraseExecution,
            hhistory] using hempty
      | publicChoice code =>
          have hne : code.endpoint.owner ≠ focal := by
            intro heq
            apply howner
            simpa [ApplicationInstruction.submitter] using congrArg some heq
          have hhistory := runtime.application.playerStep_other_history
            focal code.endpoint.owner hne execution command next hnext
          simpa [ApplicationInstruction.CacheEmpty, WindowedApplication.eraseExecution,
            hhistory] using hempty
      | conditional code =>
          have hne : code.endpoint.owner ≠ focal := by
            intro heq
            apply howner
            simpa [ApplicationInstruction.submitter] using congrArg some heq
          have hhistory := runtime.application.playerStep_other_history
            focal code.endpoint.owner hne execution command next hnext
          simpa [ApplicationInstruction.CacheEmpty, WindowedApplication.eraseExecution,
            hhistory] using hempty

/-- Environment invocations do not change any erased principal history. -/
theorem RemainingUnchangedCachesEmpty.environmentPolicyStep
    (runtime : WindowedApplication P L) (cacheImage : ApplicationImage P L)
    (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (focal : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hnext : next ∈
      (runtime.application.environmentPolicyStep execution command).support)
    (hfresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution execution)) :
    RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution next) := by
  unfold RemainingUnchangedCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  obtain howner | hempty :=
    (List.forall_iff_forall_mem.mp hfresh) instruction hinstruction
  · exact Or.inl howner
  · right
    have hhistory := runtime.application.environmentStep_principalHistory
      execution command next hnext
    cases instruction <;>
      simp_all [ApplicationInstruction.CacheEmpty, WindowedApplication.eraseExecution]

/-- A policy segment preserves unchanged-owner cache freshness when every
non-focal player invocation in the segment is known to return `wait`. The
coordinate bounds make this reusable for services with different block widths. -/
theorem runPolicies_waiting_others_preserves_unchangedCaches
    (runtime : WindowedApplication P L) (cacheImage : ApplicationImage P L)
    (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (focal : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (hwait : ∀ actor, actor ≠ focal → ∀ index,
      (execution.principalHistory actor).length ≤ index →
      index < (execution.principalHistory actor).length +
        schedule.countP (fun call => match call with
          | .player who => decide (who = actor)
          | .environment => false) →
      ∀ history view, history.length = index →
        players actor history view = FinDist.pure .wait)
    (hfresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution execution))
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution next) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hfresh
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind,
        Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hmiddleFresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
          (runtime.eraseExecution middle) := by
        cases invocation with
        | player actor =>
            simp only [MessageApplication.invoke, FinDist.support_bind,
              Set.mem_iUnion] at hmiddle
            obtain ⟨command, hcommand, hstep⟩ := hmiddle
            by_cases hactor : actor = focal
            · subst actor
              exact hfresh.playerStep_focal runtime cacheImage deadlineOf plan focal execution
                middle command hstep
            · rw [hwait actor hactor _ (Nat.le_refl _) (by simp)
                (execution.principalHistory actor)
                (State.observe runtime.application execution.native actor) rfl] at hcommand
              rw [FinDist.mem_support_pure] at hcommand
              subst command
              exact hfresh.playerStep_wait runtime cacheImage deadlineOf plan focal actor execution
                middle hstep
        | environment =>
            simp only [MessageApplication.invoke, FinDist.support_bind,
              Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            exact hfresh.environmentPolicyStep runtime cacheImage deadlineOf plan focal execution
              middle command hstep
      apply ih middle
      · intro actor hactor index hlo hhi history view hhistory
        have hlength := runtime.application.runPolicies_principalHistory_length actor players
          environment [invocation] execution middle (by
            simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
        apply hwait actor hactor index
        · omega
        · rw [hlength] at hhi
          convert hhi using 1
          simp only [List.countP_cons, List.countP_nil,
            Nat.zero_add, Nat.add_assoc, Nat.add_comm]
          rfl
        · exact hhistory
      · exact hmiddleFresh
      · exact hnext

/-- One complete aligned sample block preserves unchanged-owner cache
freshness while leaving the focal policy wholly unrestricted. -/
theorem runPolicies_full_sample_block_preserves_unchangedCaches
    (runtime : WindowedApplication P L) (cacheImage : ApplicationImage P L)
    (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state) (roster : List P)
    (hroster : roster.Nodup) (focal : P)
    (bases players : P → runtime.application.PlayerPolicy)
    (hothers : ∀ actor, actor ≠ focal →
      players actor = runtime.blockPlayer actor (bases actor))
    (block : Nat) (code : SampleCode L)
    (execution next : runtime.application.PolicyExecution)
    (hlookup : runtime.image.lookup code.node = some (.sample code))
    (hindex : runtime.image.instructions[block]? = some (.sample code))
    (hplayers : ∀ actor ∈ roster,
      (execution.principalHistory actor).length = 3 * block)
    (hfresh : RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution execution))
    (hnext : next ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (blockInvocations roster) execution).support) :
    RemainingUnchangedCachesEmpty cacheImage deadlineOf plan focal
      (runtime.eraseExecution next) := by
  apply runPolicies_waiting_others_preserves_unchangedCaches runtime cacheImage deadlineOf
    plan focal players (runtime.blockEnvironment roster) (blockInvocations roster)
    execution next
  · intro actor hactor index hlo hhi history view hhistory
    have hcount : (blockInvocations roster).countP (fun call => match call with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 3 else 0 :=
      blockInvocations_player_count roster hroster actor
    have hhi' : index < (execution.principalHistory actor).length +
        (if actor ∈ roster then 3 else 0) := by
      convert hhi using 1
      congr 1
      exact hcount.symm
    by_cases hmem : actor ∈ roster
    · simp only [hmem, ↓reduceIte] at hhi'
      have hbaseLength := hplayers actor hmem
      have hquotient : index / 3 = block := by omega
      rw [hothers actor hactor]
      exact runtime.blockPlayer_sample_wait actor (bases actor) history view code
        (by rw [hhistory, hquotient]; exact hindex) hlookup
    · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi'
      omega
  · exact hfresh
  · exact hnext

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.runPolicies_full_sample_block_preserves_unchangedCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.runPolicies_full_sample_block_preserves_unchangedCaches
