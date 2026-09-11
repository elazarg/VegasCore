/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockCaches

/-! # Cache freshness under windowed reference players

Unlike deviation checkpoints, these lemmas retain freshness for every owner.
They are the cache-preservation layer for the honest windowed execution law.
-/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
variable {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
variable {accounted : CommitmentAccounting pending prog}
variable {nextAccounted : CommitmentAccounting nextPending nextProg}
variable {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
variable {state : BuildState P L Γ} {nextState : BuildState P L Δ}

/-- A recognized current-head command cannot populate any cache in the
generated tail, after transporting the windowed step through activation
erasure. -/
theorem RemainingCachesEmpty.windowed_playerStep_headCommand
    (runtime : WindowedApplication P L)
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (head : ApplicationInstruction P L) (actor : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hinstructions : plan.instructions deadlineOf =
      head :: nextPlan.instructions deadlineOf)
    (hhead : runtime.erasePlayerCommand command = .wait ∨
      ¬ head.RejectsCommand image actor (runtime.erasePlayerCommand command))
    (hstep : next ∈ (runtime.application.playerStep actor execution command).support)
    (hfresh : nextPlan.RemainingCachesEmpty image deadlineOf
      (runtime.eraseExecution execution)) :
    nextPlan.RemainingCachesEmpty image deadlineOf (runtime.eraseExecution next) := by
  unfold RemainingCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  apply instruction.cacheEmpty_playerStep image actor (runtime.eraseExecution execution)
    (runtime.erasePlayerCommand command) (runtime.eraseExecution next)
    (runtime.playerStep_erased_support image actor execution next command hstep)
    ((List.forall_iff_forall_mem.mp hfresh) instruction hinstruction)
  exact head_command_rejects_next plan nextPlan deadlineOf image head actor
    (runtime.erasePlayerCommand command) hinstructions hhead instruction hinstruction

/-- A windowed idle or expiry step preserves every remaining cache. -/
theorem RemainingCachesEmpty.windowed_playerStep_idleOrExpiry
    (runtime : WindowedApplication P L) (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (plan : ApplicationPlan accounted fresh state)
    (actor : P) (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hcommand : image.IdleOrExpiryCommand (runtime.erasePlayerCommand command))
    (hstep : next ∈ (runtime.application.playerStep actor execution command).support)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf
      (runtime.eraseExecution execution)) :
    plan.RemainingCachesEmpty image deadlineOf (runtime.eraseExecution next) := by
  apply plan.remainingCachesEmpty_playerStep_idleOrExpiry image deadlineOf actor
    (runtime.eraseExecution execution) (runtime.eraseExecution next)
    (runtime.erasePlayerCommand command) hcommand
    (runtime.playerStep_erased_support image actor execution next command hstep) hfresh

/-- A windowed environment step preserves every remaining cache. -/
theorem RemainingCachesEmpty.windowed_environmentPolicyStep
    (runtime : WindowedApplication P L) (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (plan : ApplicationPlan accounted fresh state)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hstep : next ∈ (runtime.application.environmentPolicyStep execution command).support)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf
      (runtime.eraseExecution execution)) :
    plan.RemainingCachesEmpty image deadlineOf (runtime.eraseExecution next) := by
  unfold RemainingCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  have hempty := (List.forall_iff_forall_mem.mp hfresh) instruction hinstruction
  have hhistory := runtime.application.environmentStep_principalHistory
    execution command next hstep
  cases instruction <;>
    simp_all [ApplicationInstruction.CacheEmpty, WindowedApplication.eraseExecution]

/-- Relay-only player coordinates under block reference policies, together
with arbitrary environment coordinates, preserve all remaining caches. -/
theorem runPolicies_relay_slots_preserves_referenceCaches
    (runtime : WindowedApplication P L) (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (plan : ApplicationPlan accounted fresh state)
    (bases players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (execution next : runtime.application.PolicyExecution)
    (hplayers : ∀ actor, players actor = runtime.blockPlayer actor (bases actor))
    (hslots : ∀ actor index, (execution.principalHistory actor).length ≤ index →
      index < (execution.principalHistory actor).length + schedule.countP (fun call =>
        match call with
        | .player who => decide (who = actor)
        | .environment => false) → index % 3 = 2)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf
      (runtime.eraseExecution execution))
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    plan.RemainingCachesEmpty image deadlineOf (runtime.eraseExecution next) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hfresh
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hmiddleFresh : plan.RemainingCachesEmpty image deadlineOf
          (runtime.eraseExecution middle) := by
        cases invocation with
        | player actor =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, hcommand, hstep⟩ := hmiddle
            rw [hplayers actor] at hcommand
            exact hfresh.windowed_playerStep_idleOrExpiry runtime image deadlineOf plan actor
              execution middle command
              (blockPlayer_relay_idleOrExpiry runtime image actor (bases actor)
                (execution.principalHistory actor)
                (State.observe runtime.application execution.native actor)
                (hslots actor _ (Nat.le_refl _) (by simp)) command hcommand) hstep
        | environment =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            exact hfresh.windowed_environmentPolicyStep runtime image deadlineOf plan
              execution middle command hstep
      apply ih middle
      · intro actor index hlo hhi
        have hlength := runtime.application.runPolicies_principalHistory_length actor players
          environment [invocation] execution middle (by
            simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
        apply hslots actor index
        · omega
        · rw [hlength] at hhi
          convert hhi using 1
          simp only [List.countP_cons, List.countP_nil,
            Nat.zero_add, Nat.add_assoc, Nat.add_comm]
          rfl
      · exact hmiddleFresh
      · exact hnext

section Source

variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg}

/-- Every player-only polling prefix under the original windowed reference
players preserves all caches in the generated tail. -/
theorem runPolicies_polls_preserves_referenceCaches
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (profile : SourceBehavioralProfile prog)
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat)
    (head : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf =
      head :: nextPlan.instructions deadlineOf)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat)
    (players : P →
      (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (hplayers : ∀ actor,
      players actor =
        (root.windowed deadlineOf binding choice windowOf).blockPlayer actor
          ((root.windowed deadlineOf binding choice windowOf).liftPlayerPolicy
            (root.liftProfile deadlineOf rootProfile actor)))
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (henvironment : Invocation.environment ∉ schedule)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution next :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hfresh : nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution))
    (hnext : next ∈
      ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
        players environment schedule execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution next) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let image := root.image deadlineOf
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hfresh
  | cons invocation rest ih =>
      have hrest : Invocation.environment ∉ rest := fun hmem =>
        henvironment (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | environment => exact False.elim (henvironment List.mem_cons_self)
      | player actor =>
          simp only [MessageApplication.runPolicies, MessageApplication.invoke,
            FinDist.support_bind, Set.mem_iUnion] at hnext
          obtain ⟨middle, ⟨command, hcommand, hstep⟩, hnext⟩ := hnext
          have hmiddleRefines :=
            (runtime.playerStep_refines actor execution middle command
              current.current.graph.1 hrefines hstep).1
          have hmiddleFresh : nextPlan.RemainingCachesEmpty image deadlineOf
              (runtime.eraseExecution middle) := by
            change command ∈ (players actor (execution.principalHistory actor)
              (State.observe runtime.application execution.native actor)).support at hcommand
            rw [hplayers actor] at hcommand
            rcases runtime.blockPlayer_supported actor
              (root.liftProfile deadlineOf rootProfile actor) (execution.principalHistory actor)
              (State.observe runtime.application execution.native actor) command hcommand with
                hsource | hidle
            · have hdispatch := continuation.liftProfileIn_eq_of_refines image deadlineOf
                current (runtime.eraseExecution execution).native hrefines actor
                ((runtime.eraseExecution execution).principalHistory actor)
              change runtime.erasePlayerCommand command ∈
                (root.liftProfileIn image deadlineOf rootProfile actor
                  ((runtime.eraseExecution execution).principalHistory actor)
                  (State.observe image.application
                    (runtime.eraseExecution execution).native actor)).support at hsource
              rw [hdispatch] at hsource
              obtain ⟨_, _, _, hpending⟩ := continuation.instruction_completion
                (deadlineOf := deadlineOf) (current := current)
                execution.native.application.base hrefines
              have hunresolved : execution.native.application.base.memory.done
                  head.address = false := hpending head (by rw [hinstructions]; simp)
              have hhead := liftProfileIn_headCommand plan deadlineOf image profile
                actor ((runtime.eraseExecution execution).principalHistory actor)
                (State.observe image.application (runtime.eraseExecution execution).native actor)
                head (nextPlan.instructions deadlineOf) hinstructions
                (runtime.erasePlayerCommand command) hunresolved hsource
              exact hfresh.windowed_playerStep_headCommand runtime plan nextPlan deadlineOf
                image head actor execution middle command hinstructions hhead hstep
            · exact hfresh.windowed_playerStep_idleOrExpiry runtime image deadlineOf nextPlan
                actor execution middle command (by cases command <;> exact hidle) hstep
          exact ih hrest middle hmiddleRefines hmiddleFresh hnext

/-- A complete block under the reference profile preserves every remaining
cache. The distinguished coordinate is also a reference player; its future
instructions receive the same freshness guarantee as all other instructions. -/
theorem WindowedCheckpoint.block_reference_caches
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (profile : SourceBehavioralProfile prog) (deadlineOf : Nat → Nat)
    (head : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf = head :: nextPlan.instructions deadlineOf)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (hroster : roster.Nodup) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (hreplacement : replacement =
      root.windowedReferencePlayers rootProfile deadlineOf binding choice windowOf focal)
    (blockIndex : Nat)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution next :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex plan profile current execution)
    (hfresh : plan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution))
    (hnext : next ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    nextPlan.RemainingCachesEmpty (root.image deadlineOf) deadlineOf
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution next) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let relays := roster.flatMap fun actor => [Invocation.player actor, .environment]
  have hplayers : ∀ actor, players actor = runtime.blockPlayer actor
      (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)) := by
    intro actor
    simp only [players, windowedPlayers, hreplacement, Function.update_eq_self]
    rfl
  change next ∈ (runtime.application.runPolicies players (runtime.blockEnvironment roster)
    ((polls ++ [.environment, .environment]) ++ relays) execution).support at hnext
  rw [List.append_assoc, MessageApplication.runPolicies_append, FinDist.support_bind] at hnext
  simp only [Set.mem_iUnion] at hnext
  obtain ⟨polled, hpolled, hnext⟩ := hnext
  unfold RemainingCachesEmpty at hfresh
  rw [hinstructions] at hfresh
  have hpolledFresh := runPolicies_polls_preserves_referenceCaches plan nextPlan profile
    checkpoint.continuation deadlineOf head hinstructions binding choice windowOf players hplayers
    (runtime.blockEnvironment roster) polls (by simp [polls]) current execution polled
    checkpoint.refines ((List.forall_cons _ _ _).mp hfresh |>.2) hpolled
  apply runPolicies_relay_slots_preserves_referenceCaches runtime (root.image deadlineOf)
    deadlineOf nextPlan
    (fun actor => runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor))
    players (runtime.blockEnvironment roster) ([.environment, .environment] ++ relays)
    polled next hplayers
  · exact runtime.runPolicies_polls_relay_slots roster hroster players
      (runtime.blockEnvironment roster) blockIndex execution polled
      (fun actor hactor => (checkpoint.historyAlignment hroster actor hactor).1) hpolled
  · exact hpolledFresh
  · exact hnext

end Source

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.RemainingCachesEmpty.windowed_playerStep_headCommand'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.RemainingCachesEmpty.windowed_playerStep_headCommand

/-- info: 'Vegas.ApplicationPlan.runPolicies_relay_slots_preserves_referenceCaches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_relay_slots_preserves_referenceCaches

/-- info: 'Vegas.ApplicationPlan.runPolicies_polls_preserves_referenceCaches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_polls_preserves_referenceCaches

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.block_reference_caches'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.block_reference_caches
