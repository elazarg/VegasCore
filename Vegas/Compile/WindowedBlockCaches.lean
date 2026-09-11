/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyCache
import Vegas.Compile.WindowedCheckpoint
import Vegas.Compile.WindowedSampleCaches
import Vegas.Compile.WindowedBlockProvenance
import Vegas.Compile.WindowedBlockProgress

/-! # Future-cache freshness through generated blocks -/

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

/-- A command recognized by the current generated instruction cannot populate
an unchanged owner's cache in the generated tail. Instructions owned by the
focal replacement are exempt from the invariant. -/
theorem RemainingUnchangedCachesEmpty.playerStep_headCommand
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (head : ApplicationInstruction P L) (focal actor : P)
    (execution next : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hinstructions : plan.instructions deadlineOf =
      head :: nextPlan.instructions deadlineOf)
    (hhead : command = .wait ∨ ¬ head.RejectsCommand image actor command)
    (hstep : next ∈ (image.application.playerStep actor execution command).support)
    (hfresh : RemainingUnchangedCachesEmpty image deadlineOf nextPlan focal execution) :
    RemainingUnchangedCachesEmpty image deadlineOf nextPlan focal next := by
  unfold RemainingUnchangedCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  obtain howner | hempty :=
    (List.forall_iff_forall_mem.mp hfresh) instruction hinstruction
  · exact Or.inl howner
  · right
    apply instruction.cacheEmpty_playerStep image actor execution command next hstep hempty
    exact head_command_rejects_next plan nextPlan deadlineOf image head actor command
      hinstructions hhead instruction hinstruction

/-- Activation erasure transports the actual raw player step to the generated
cache API. This requires no restriction on other retained messages or clocks. -/
theorem RemainingUnchangedCachesEmpty.windowed_playerStep_headCommand
    (runtime : WindowedApplication P L)
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (deadlineOf : Nat → Nat) (image : ApplicationImage P L)
    (head : ApplicationInstruction P L) (focal actor : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hinstructions : plan.instructions deadlineOf =
      head :: nextPlan.instructions deadlineOf)
    (hhead : runtime.erasePlayerCommand command = .wait ∨
      ¬ head.RejectsCommand image actor (runtime.erasePlayerCommand command))
    (hstep : next ∈ (runtime.application.playerStep actor execution command).support)
    (hfresh : RemainingUnchangedCachesEmpty image deadlineOf nextPlan focal
      (runtime.eraseExecution execution)) :
    RemainingUnchangedCachesEmpty image deadlineOf nextPlan focal
      (runtime.eraseExecution next) := by
  apply hfresh.playerStep_headCommand plan nextPlan deadlineOf image head focal actor
    (runtime.eraseExecution execution) (runtime.eraseExecution next)
    (runtime.erasePlayerCommand command) hinstructions hhead
  exact runtime.playerStep_erased_support image actor execution next command hstep

theorem RemainingUnchangedCachesEmpty.windowed_playerStep_idleOrExpiry
    (runtime : WindowedApplication P L) (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (plan : ApplicationPlan accounted fresh state) (focal actor : P)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand)
    (hcommand : image.IdleOrExpiryCommand (runtime.erasePlayerCommand command))
    (hstep : next ∈ (runtime.application.playerStep actor execution command).support)
    (hfresh : RemainingUnchangedCachesEmpty image deadlineOf plan focal
      (runtime.eraseExecution execution)) :
    RemainingUnchangedCachesEmpty image deadlineOf plan focal
      (runtime.eraseExecution next) := by
  unfold RemainingUnchangedCachesEmpty at hfresh ⊢
  apply List.forall_iff_forall_mem.mpr
  intro instruction hinstruction
  obtain howner | hempty := (List.forall_iff_forall_mem.mp hfresh) instruction hinstruction
  · exact Or.inl howner
  · right
    exact instruction.cacheEmpty_playerStep image actor (runtime.eraseExecution execution)
      (runtime.erasePlayerCommand command) (runtime.eraseExecution next)
      (runtime.playerStep_erased_support image actor execution next command hstep) hempty
      (instruction.idleOrExpiry_rejectsCommand image actor _ hcommand)

/-- A block's relay slot only waits or submits a due expiry, independently
of the underlying reference policy. -/
theorem blockPlayer_relay_idleOrExpiry
    (runtime : WindowedApplication P L) (image : ApplicationImage P L) (actor : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (hslot : history.length % 3 = 2) (command : runtime.application.PlayerCommand)
    (hcommand : command ∈ (runtime.blockPlayer actor base history view).support) :
    image.IdleOrExpiryCommand (runtime.erasePlayerCommand command) := by
  unfold WindowedApplication.blockPlayer at hcommand
  cases hindex : runtime.image.instructions[history.length / 3]? with
  | none =>
      simp only [hindex, FinDist.mem_support_pure] at hcommand
      subst command
      trivial
  | some instruction =>
      simp only [hindex, hslot, Nat.lt_irrefl, ↓reduceIte] at hcommand
      split at hcommand
      · rw [FinDist.mem_support_pure] at hcommand
        subst command
        cases hdue : runtime.dueExpiry? view.application with
        | none => trivial
        | some payload =>
            exact runtime.dueExpiry?_deadlineDependent view.application payload hdue
      · rw [FinDist.mem_support_pure] at hcommand
        subst command
        trivial

/-- Relay-only player coordinates and arbitrary environment invocations
preserve every future unchanged-owner cache. The focal commands are unrestricted. -/
theorem runPolicies_idleOrExpiry_others_preserves_unchangedCaches
    (runtime : WindowedApplication P L) (image : ApplicationImage P L)
    (deadlineOf : Nat → Nat) (plan : ApplicationPlan accounted fresh state) (focal : P)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (execution next : runtime.application.PolicyExecution)
    (hsafe : ∀ actor, actor ≠ focal → ∀ index,
      (execution.principalHistory actor).length ≤ index →
      index < (execution.principalHistory actor).length + schedule.countP (fun call =>
        match call with
        | .player who => decide (who = actor)
        | .environment => false) → ∀ history view, history.length = index → ∀ command,
      command ∈ (players actor history view).support →
        image.IdleOrExpiryCommand (runtime.erasePlayerCommand command))
    (hfresh : RemainingUnchangedCachesEmpty image deadlineOf plan focal
      (runtime.eraseExecution execution))
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    RemainingUnchangedCachesEmpty image deadlineOf plan focal
      (runtime.eraseExecution next) := by
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hfresh
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hmiddleFresh : RemainingUnchangedCachesEmpty image deadlineOf plan focal
          (runtime.eraseExecution middle) := by
        cases invocation with
        | player actor =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, hcommand, hstep⟩ := hmiddle
            by_cases hactor : actor = focal
            · subst actor
              exact hfresh.playerStep_focal runtime image deadlineOf plan focal
                execution middle command hstep
            · exact RemainingUnchangedCachesEmpty.windowed_playerStep_idleOrExpiry runtime image
                deadlineOf plan focal actor execution middle command
                (hsafe actor hactor _ (Nat.le_refl _) (by simp)
                  (execution.principalHistory actor)
                  (State.observe runtime.application execution.native actor) rfl command hcommand)
                hstep hfresh
        | environment =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            exact hfresh.environmentPolicyStep runtime image deadlineOf plan focal execution
              middle command hstep
      apply ih middle
      · intro actor hactor index hlo hhi history view hhistory command hcommand
        have hlength := runtime.application.runPolicies_principalHistory_length actor players
          environment [invocation] execution middle (by
            simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
        apply hsafe actor hactor index
        · omega
        · rw [hlength] at hhi
          convert hhi using 1
          simp only [List.countP_cons, List.countP_nil,
            Nat.zero_add, Nat.add_assoc, Nat.add_comm]
          rfl
        · exact hhistory
        · exact hcommand
      · exact hmiddleFresh
      · exact hnext

section Source

variable {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg}

/-- Every actual player-only prefix at a source checkpoint preserves
future unchanged-owner caches. The focal principal may use any raw command;
other principals use the original lifted profile with its block gates. -/
theorem runPolicies_polls_preserves_unchangedCaches
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (profile : SourceBehavioralProfile prog)
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat)
    (head : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf = head :: nextPlan.instructions deadlineOf)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (environment :
      (root.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (henvironment : Invocation.environment ∉ schedule)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution next :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hfresh : RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan focal
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution execution))
    (hnext : next ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      environment schedule execution).support) :
    RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan focal
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution next) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let image := root.image deadlineOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
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
          have hmiddleFresh : RemainingUnchangedCachesEmpty image deadlineOf nextPlan focal
              (runtime.eraseExecution middle) := by
            by_cases hactor : actor = focal
            · subst actor
              exact hfresh.playerStep_focal runtime image deadlineOf nextPlan focal
                execution middle command hstep
            · have hpolicy : players actor = runtime.blockPlayer actor
                  (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)) := by
                simp only [players, windowedPlayers, Function.update_of_ne hactor,
                  windowedReferencePlayers]
                rfl
              change command ∈ (players actor (execution.principalHistory actor)
                (State.observe runtime.application execution.native actor)).support at hcommand
              rw [hpolicy] at hcommand
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
                  image head focal actor execution middle command hinstructions hhead hstep
              · exact RemainingUnchangedCachesEmpty.windowed_playerStep_idleOrExpiry runtime
                  image deadlineOf nextPlan focal actor execution middle command
                  (by cases command <;> exact hidle) hstep hfresh
          exact ih hrest middle hmiddleRefines hmiddleFresh hnext

/-- One entire generated block preserves the remaining unchanged-owner
caches. Initial freshness and alignment come from the actual source checkpoint;
polling, environment steps, and reserved relay slots discharge their own cases. -/
theorem WindowedCheckpoint.block_caches
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (profile : SourceBehavioralProfile prog)
    (deadlineOf : Nat → Nat)
    (head : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf = head :: nextPlan.instructions deadlineOf)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster : List P) (hroster : roster.Nodup) (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (blockIndex : Nat)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution next :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      focal replacement blockIndex plan profile current execution)
    (hnext : next ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan focal
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution next) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let players := root.windowedPlayers rootProfile deadlineOf binding choice windowOf focal
    replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let relays := roster.flatMap fun actor => [Invocation.player actor, .environment]
  change next ∈ (runtime.application.runPolicies players (runtime.blockEnvironment roster)
    ((polls ++ [.environment, .environment]) ++ relays) execution).support at hnext
  rw [List.append_assoc, MessageApplication.runPolicies_append, FinDist.support_bind] at hnext
  simp only [Set.mem_iUnion] at hnext
  obtain ⟨polled, hpolled, hnext⟩ := hnext
  have hfresh := checkpoint.unchangedCaches
  unfold RemainingUnchangedCachesEmpty at hfresh
  rw [hinstructions] at hfresh
  have hpolledFresh := runPolicies_polls_preserves_unchangedCaches plan nextPlan
    profile checkpoint.continuation deadlineOf head hinstructions binding choice windowOf focal
    replacement
    (runtime.blockEnvironment roster) polls (by simp [polls]) current execution polled
    checkpoint.refines ((List.forall_cons _ _ _).mp hfresh |>.2) hpolled
  apply runPolicies_idleOrExpiry_others_preserves_unchangedCaches runtime
    (root.image deadlineOf) deadlineOf nextPlan focal players
    (runtime.blockEnvironment roster) ([.environment, .environment] ++ relays)
    polled next
  · intro actor hactor index hlo hhi history view hhistory command hcommand
    have hpolicy : players actor = runtime.blockPlayer actor
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)) := by
      simp only [players, windowedPlayers, Function.update_of_ne hactor,
        windowedReferencePlayers]
      rfl
    rw [hpolicy] at hcommand
    apply blockPlayer_relay_idleOrExpiry runtime (root.image deadlineOf) actor _ history view
      _ command hcommand
    have hslot := runtime.runPolicies_polls_relay_slots roster hroster players
      (runtime.blockEnvironment roster) blockIndex execution polled
      (fun who hwho => (checkpoint.historyAlignment hroster who hwho).1) hpolled actor
      index hlo hhi
    simpa only [hhistory] using hslot
  · exact hpolledFresh
  · exact hnext

end Source

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.RemainingUnchangedCachesEmpty.playerStep_headCommand'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.ApplicationPlan.RemainingUnchangedCachesEmpty.playerStep_headCommand

/-- info: 'Vegas.ApplicationPlan.runPolicies_polls_preserves_unchangedCaches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_polls_preserves_unchangedCaches

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.block_caches'
depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.block_caches
