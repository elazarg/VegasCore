/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockCaches
import Vegas.Compile.WindowedDeliveryAlignment
import Vegas.Compile.WindowedService

/-! # Future-cache freshness through delivery-enabled blocks -/

noncomputable section

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability WindowedApplication

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {Γ Δ : VCtx P L} {pending nextPending : Finset VarId}
variable {prog : VegasCore P L Γ} {nextProg : VegasCore P L Δ}
variable {accounted : CommitmentAccounting pending prog}
variable {nextAccounted : CommitmentAccounting nextPending nextProg}
variable {fresh : FreshBindings prog} {nextFresh : FreshBindings nextProg}
variable {state : BuildState P L Γ} {nextState : BuildState P L Δ}

/-- At either post-poll player coordinate, the delivery gate emits only a wait
or a due-expiry relay. -/
private theorem deliveryBlockPlayer_tail_idleOrExpiry
    (runtime : WindowedApplication P L) (image : ApplicationImage P L) (actor : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (hslot : history.length % 4 = 2 ∨ history.length % 4 = 3)
    (command : runtime.application.PlayerCommand)
    (hcommand : command ∈
      (runtime.deliveryBlockPlayer actor base history view).support) :
    image.IdleOrExpiryCommand (runtime.erasePlayerCommand command) := by
  unfold WindowedApplication.deliveryBlockPlayer at hcommand
  cases hindex : runtime.image.instructions[history.length / 4]? with
  | none =>
      simp only [hindex, FinDist.mem_support_pure] at hcommand
      subst command
      trivial
  | some instruction =>
      by_cases hactive : runtime.image.activeAddress? view.application.1 =
          some instruction.address
      · rcases hslot with hslot | hslot
        · simp only [hindex, hactive, if_pos, hslot, FinDist.mem_support_pure] at hcommand
          subst command
          trivial
        · simp only [hindex, hactive, if_pos, hslot, FinDist.mem_support_pure] at hcommand
          subst command
          cases hdue : runtime.dueExpiry? view.application with
          | none => trivial
          | some payload =>
              exact runtime.dueExpiry?_deadlineDependent view.application payload hdue
      · simp only [hindex, hactive, if_false, FinDist.mem_support_pure] at hcommand
        subst command
        trivial

section Source

variable {rootContext : VCtx P L} {rootPending : Finset VarId}
variable {rootProg : VegasCore P L rootContext}
variable {rootAccounted : CommitmentAccounting rootPending rootProg}
variable {rootFresh : FreshBindings rootProg} {rootState : BuildState P L rootContext}
variable {root : ApplicationPlan rootAccounted rootFresh rootState}
variable {rootProfile : SourceBehavioralProfile rootProg}

private theorem runPolicies_delivery_polls_preserves_unchangedCaches
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (profile : SourceBehavioralProfile prog)
    (continuation : ProfileContinuation root rootProfile plan profile)
    (deadlineOf : Nat → Nat)
    (head : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf = head :: nextPlan.instructions deadlineOf)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster recipients : List P) (focal : P)
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
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients
        |>.players
        (root.liftProfile deadlineOf rootProfile) focal replacement)
      environment schedule execution).support) :
    RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan focal
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution next) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let image := root.image deadlineOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) focal replacement
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
            · have hpolicy : players actor = runtime.deliveryBlockPlayer actor
                  (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)) := by
                simp only [players, service, WindowedApplication.Service.players,
                  Function.update_of_ne hactor, WindowedApplication.Service.referencePlayers,
                  WindowedApplication.deliveryService]
              change command ∈ (players actor (execution.principalHistory actor)
                (State.observe runtime.application execution.native actor)).support at hcommand
              rw [hpolicy] at hcommand
              rcases runtime.deliveryBlockPlayer_supported actor
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

/-- A complete delivery-service block preserves every unchanged-owner cache
belonging to the generated tail. The focal replacement remains unrestricted. -/
theorem WindowedCheckpoint.delivery_block_caches
    (plan : ApplicationPlan accounted fresh state)
    (nextPlan : ApplicationPlan nextAccounted nextFresh nextState)
    (profile : SourceBehavioralProfile prog)
    (deadlineOf : Nat → Nat)
    (head : ApplicationInstruction P L)
    (hinstructions : plan.instructions deadlineOf = head :: nextPlan.instructions deadlineOf)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (roster recipients : List P) (hroster : roster.Nodup)
    (focal : P)
    (replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)
    (blockIndex : Nat)
    (current : CoupledAt (compileCore prog fresh state).graph state)
    (execution next :
      (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
      focal replacement blockIndex plan profile current execution)
    (hnext : next ∈ ((root.windowed deadlineOf binding choice windowOf).application.runPolicies
      (((root.windowed deadlineOf binding choice windowOf).deliveryService roster recipients)
        |>.players
        (root.liftProfile deadlineOf rootProfile) focal replacement)
      ((root.windowed deadlineOf binding choice windowOf).deliveryBlockEnvironment
        roster recipients)
      (deliveryBlockInvocations roster recipients) execution).support) :
    RemainingUnchangedCachesEmpty (root.image deadlineOf) deadlineOf nextPlan focal
      ((root.windowed deadlineOf binding choice windowOf).eraseExecution next) := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  let service := runtime.deliveryService roster recipients
  let players := service.players (root.liftProfile deadlineOf rootProfile) focal replacement
  let polls := roster.flatMap fun actor => [Invocation.player actor, .player actor]
  let tailSchedule := recipients.map (fun _ => Invocation.environment) ++
    roster.map Invocation.player ++ [.environment, .environment] ++
      roster.flatMap (fun actor => [.player actor, .environment])
  change next ∈ (runtime.application.runPolicies players service.environment
    (deliveryBlockInvocations roster recipients) execution).support at hnext
  have hschedule : deliveryBlockInvocations roster recipients = polls ++ tailSchedule := by
    simp [deliveryBlockInvocations, polls, tailSchedule, List.append_assoc]
  rw [hschedule] at hnext
  rw [MessageApplication.runPolicies_append, FinDist.support_bind] at hnext
  simp only [Set.mem_iUnion] at hnext
  obtain ⟨polled, hpolled, hnext⟩ := hnext
  have hfresh := checkpoint.unchangedCaches
  unfold RemainingUnchangedCachesEmpty at hfresh
  rw [hinstructions] at hfresh
  have hpolledFresh := runPolicies_delivery_polls_preserves_unchangedCaches plan nextPlan profile
    checkpoint.continuation deadlineOf head hinstructions binding choice windowOf roster recipients
    focal replacement
    service.environment polls (by simp [polls]) current execution polled checkpoint.refines
    ((List.forall_cons _ _ _).mp hfresh |>.2) hpolled
  apply runPolicies_idleOrExpiry_others_preserves_unchangedCaches runtime
    (root.image deadlineOf) deadlineOf nextPlan focal players service.environment tailSchedule
    polled next
  · intro actor hactor index hlo hhi history view hhistory command hcommand
    have hpolicy : players actor = runtime.deliveryBlockPlayer actor
        (runtime.liftPlayerPolicy (root.liftProfile deadlineOf rootProfile actor)) := by
      simp only [players, service, WindowedApplication.Service.players,
        Function.update_of_ne hactor, WindowedApplication.Service.referencePlayers,
        WindowedApplication.deliveryService]
    rw [hpolicy] at hcommand
    apply deliveryBlockPlayer_tail_idleOrExpiry runtime (root.image deadlineOf) actor _
      history view _ command hcommand
    have hpolls := ordinaryPolls_player_count roster hroster actor
    change polls.countP (fun call : @Invocation P => match call with
      | .player who => decide (who = actor)
      | .environment => false) = if actor ∈ roster then 2 else 0 at hpolls
    have htotal : polls.countP (fun call : @Invocation P => match call with
        | .player who => decide (who = actor)
        | .environment => false) + tailSchedule.countP (fun call : @Invocation P => match call with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 4 else 0 := by
      rw [← List.countP_append, ← hschedule]
      exact deliveryBlockInvocations_player_count roster recipients hroster actor
    have htailCount : tailSchedule.countP (fun call : @Invocation P => match call with
        | .player who => decide (who = actor)
        | .environment => false) = if actor ∈ roster then 2 else 0 := by
      by_cases hmem : actor ∈ roster
      · rw [if_pos hmem] at htotal hpolls ⊢
        omega
      · rw [if_neg hmem] at htotal hpolls ⊢
        omega
    have hhi' : index < (polled.principalHistory actor).length +
        (if actor ∈ roster then 2 else 0) := by
      convert hhi using 1
      congr 1
      exact htailCount.symm
    by_cases hmem : actor ∈ roster
    · have hmod := runtime.runPolicies_deliveryOrdinary_reaction_slot roster hroster players
        service.environment blockIndex execution polled
        (fun who hwho => (runtime.runPolicies_repeatedDeliveryBlocks_history_alignment
          roster recipients hroster who hwho players service.environment blockIndex
          (root.windowedInitialExecution deadlineOf binding choice windowOf).native execution
          (by
            simpa only [windowedInitialExecution, PolicyExecution.initial, service,
              players, WindowedApplication.Service.players,
              WindowedApplication.Service.referencePlayers,
              WindowedApplication.deliveryService] using checkpoint.reached)).1)
        hpolled actor hmem
      simp only [hmem, ↓reduceIte] at hhi'
      rw [hhistory]
      omega
    · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi'
      omega
  · exact hpolledFresh
  · exact hnext

end Source
end Vegas.ApplicationPlan
