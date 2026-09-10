/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockSettlement
import Interaction.MessageApplicationCounters

/-! # Progress through an owned windowed block -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr} {G : Graph P L}

private theorem latestSubmissionCommand_not_sample
    (runtime : WindowedApplication P L) (who : P)
    (view : runtime.application.EnvironmentObservation) (address : Nat) :
    runtime.application.latestSubmissionCommand who view ≠
      .application (.sample address) := by
  rcases runtime.application.latestSubmissionCommand_cases who view with
    hwait | ⟨id, hinclude⟩
  · rw [hwait]
    simp
  · rw [hinclude]
    simp

private theorem serviceCommand_not_sample
    (runtime : WindowedApplication P L)
    (instruction : ApplicationInstruction P L) (owner : P)
    (howner : instruction.submitter = some owner)
    (view : runtime.application.EnvironmentObservation) (address : Nat) :
    runtime.liftEnvironmentCommand
        (runtime.image.serviceCommand instruction (runtime.eraseEnvironmentView view)) ≠
      .application (.sample address) := by
  cases instruction with
  | sample code => cases howner
  | bind code | publicChoice code | conditional code =>
      simp only [ApplicationImage.serviceCommand,
        MessageApplication.latestSubmissionCommand]
      split
      · simp [liftEnvironmentCommand]
      · split <;> simp [liftEnvironmentCommand]

/-- The command selected at every actual environment slot of an owned block
is non-sampling. This includes normal service, the clock slot, relay slots,
and the inactive gate. -/
theorem blockEnvironment_command_not_sample
    (runtime : WindowedApplication P L) (roster : List P)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (owner : P)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (howner : instruction.submitter = some owner)
    (command : runtime.application.EnvironmentPolicyCommand)
    (hcommand : command ∈ (runtime.blockEnvironment roster
      execution.environmentHistory
      (MessageApplication.State.environmentView runtime.application execution.native)).support) :
    ∀ address, command ≠ .application (.sample address) := by
  simp only [blockEnvironment, hindex, FinDist.mem_support_pure] at hcommand
  subst command
  intro address
  split
  · split
    · exact runtime.serviceCommand_not_sample instruction owner howner _ address
    · split
      · simp
      · split
        · simp
        · simp
    · split
      · simp
      · exact runtime.latestSubmissionCommand_not_sample _ _ address
  · simp

/-- A raw player command cannot change the public source checkpoint. Private
registration only extends preparation; all other player commands only change
the message pool. -/
theorem playerStep_refines (runtime : WindowedApplication P L)
    (who : P) (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.PlayerCommand) (cfg : Config G)
    (hrefines : execution.native.application.base.Refines cfg)
    (hnext : next ∈ (runtime.application.playerStep who execution command).support) :
    next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      next.native.application.base.memory.clock =
        execution.native.application.base.memory.clock := by
  cases command with
  | submit payload | replay id | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.advance,
        PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hrefines, rfl, rfl⟩
  | privateCommand command =>
      cases command with
      | register slot value =>
          simp only [MessageApplication.playerStep, MessageApplication.advance,
            PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
            FinDist.mem_support_pure] at hnext
          subst next
          exact ⟨hrefines.register who slot value, rfl, rfl⟩

/-- Advancing the clock preserves a refined active checkpoint and only moves
time forward. This is the exact effect used by the second block environment
slot. -/
theorem environmentPolicyStep_advance_refines (runtime : WindowedApplication P L)
    (execution next : runtime.application.PolicyExecution) (clock : Nat)
    (cfg : Config G)
    (hrefines : execution.native.application.base.Refines cfg)
    (hnext : next ∈ (runtime.application.environmentPolicyStep execution
      (.application (.advance clock))).support) :
    next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      execution.native.application.base.memory.clock ≤
        next.native.application.base.memory.clock := by
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, application_advance,
    FinDist.map_pure, FinDist.pure_bind, FinDist.mem_support_pure] at hnext
  subst next
  refine ⟨hrefines.advance clock, rfl, ?_⟩
  simp [ApplicationImage.State.advance]

/-- The block clock slot preserves the active source checkpoint in addition
to setting the exact post-window clock. -/
theorem block_clock_step_checkpoint
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (execution : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (cfg : Config G)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hrefines : execution.native.application.base.Refines cfg) :
    ∃ next, runtime.application.runPolicies players (runtime.blockEnvironment roster)
        [.environment] execution = FinDist.pure next ∧
      next.native.application.base.memory.clock =
        max execution.native.application.base.memory.clock
          (activation.since + runtime.windowOf instruction.address + 1) ∧
      next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      runtime.image.activeAddress? next.native.application.base.memory =
        some instruction.address := by
  have hpolicy := runtime.blockEnvironment_advance roster execution.environmentHistory
    (MessageApplication.State.environmentView runtime.application execution.native)
    instruction activation hindex hactive hslot hactivation hkey
  simp only [MessageApplication.runPolicies, MessageApplication.invoke, hpolicy,
    FinDist.pure_bind, MessageApplication.environmentPolicyStep,
    EnvironmentPolicyCommand.toAction, MessageApplication.advance,
    MessageApplication.step, application_advance, FinDist.map_pure]
  refine ⟨_, rfl, ?_, hrefines.advance _, rfl, ?_⟩
  · simp [ApplicationImage.State.advance]
  · simpa [ApplicationImage.State.advance, ApplicationImage.activeAddress?] using hactive

/-- If inclusion leaves the old active address in place, its application
handler rejected (or the identifier was missing), hence the application state
itself is unchanged. -/
theorem includePending_application_eq_of_active
    (runtime : WindowedApplication P L) (state : runtime.application.State)
    (id : MessageId P) (address : Nat)
    (hbefore : runtime.image.activeAddress? state.application.base.memory = some address)
    (hafter : runtime.image.activeAddress?
      (runtime.application.includePending state id).application.base.memory = some address) :
    (runtime.application.includePending state id).application = state.application := by
  cases hlookup : state.pool.lookup id with
  | none => simp [runtime.application.includePending_missing state id hlookup]
  | some message =>
      cases hhandle : runtime.handle state.application message with
      | none =>
          rw [runtime.application.includePending_reject state id message hlookup hhandle]
      | some next =>
          rw [runtime.application.includePending_accept state id message next hlookup hhandle]
            at hafter ⊢
          exact False.elim
            (runtime.handle_eq_none_of_active_preserved state.application next message address
              hbefore hafter hhandle)

/-- Every non-sampling environment command preserves a refined checkpoint as
long as the original active address remains active. Includes in this branch
are necessarily rejected; the only possible public change is a monotone clock
advance. -/
theorem environmentPolicyStep_refines_of_active
    (runtime : WindowedApplication P L)
    (execution next : runtime.application.PolicyExecution)
    (command : runtime.application.EnvironmentPolicyCommand)
    (address : Nat) (cfg : Config G)
    (hrefines : execution.native.application.base.Refines cfg)
    (hbefore : runtime.image.activeAddress?
      execution.native.application.base.memory = some address)
    (hafter : runtime.image.activeAddress?
      next.native.application.base.memory = some address)
    (hnosample : ∀ sampled, command ≠ .application (.sample sampled))
    (hnext : next ∈
      (runtime.application.environmentPolicyStep execution command).support) :
    next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      execution.native.application.base.memory.clock ≤
        next.native.application.base.memory.clock := by
  cases command with
  | wait | deliver who id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      exact ⟨hrefines, rfl, Nat.le_refl _⟩
  | «include» id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hnext
      subst next
      have happ := runtime.includePending_application_eq_of_active execution.native id address
        hbefore hafter
      rw [happ]
      exact ⟨hrefines, rfl, Nat.le_refl _⟩
  | application native =>
      cases native with
      | sample sampled => exact False.elim (hnosample sampled rfl)
      | advance clock =>
          exact runtime.environmentPolicyStep_advance_refines execution next clock cfg
            hrefines hnext

/-- One actual owned-block invocation preserves the source checkpoint whenever
the original address remains active. The environment-policy branch derives
its non-sampling property from the concrete block policy. -/
theorem invoke_refines_of_active
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (execution next : runtime.application.PolicyExecution)
    (invocation : @Invocation P) (instruction : ApplicationInstruction P L)
    (owner : P) (cfg : Config G)
    (hindex : runtime.image.instructions[execution.environmentHistory.length /
      (roster.length + 2)]? = some instruction)
    (howner : instruction.submitter = some owner)
    (hrefines : execution.native.application.base.Refines cfg)
    (hbefore : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hafter : runtime.image.activeAddress?
      next.native.application.base.memory = some instruction.address)
    (hnext : next ∈ (runtime.application.invoke players
      (runtime.blockEnvironment roster) execution invocation).support) :
    next.native.application.base.Refines cfg ∧
      next.native.application.active = execution.native.application.active ∧
      execution.native.application.base.memory.clock ≤
        next.native.application.base.memory.clock := by
  cases invocation with
  | player who =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, _, hstep⟩ := hnext
      obtain ⟨hnextRefines, hactivation, hclock⟩ :=
        runtime.playerStep_refines who execution next command cfg hrefines hstep
      exact ⟨hnextRefines, hactivation, Nat.le_of_eq hclock.symm⟩
  | environment =>
      simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨command, hcommand, hstep⟩ := hnext
      exact runtime.environmentPolicyStep_refines_of_active execution next command
        instruction.address cfg hrefines hbefore hafter
        (runtime.blockEnvironment_command_not_sample roster execution instruction owner
          hindex howner command hcommand) hstep

/-- If an aligned owned-block suffix still has the original address active at
its end, every earlier invocation was in the active branch. Consequently the
whole actual supported suffix preserves the same source configuration and
activation origin, while its public clock is monotone. -/
theorem runPolicies_refines_of_final_active
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation P))
    (execution final : runtime.application.PolicyExecution)
    (instruction : ApplicationInstruction P L) (owner : P) (cfg : Config G)
    (howner : instruction.submitter = some owner)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        schedule.countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hrefines : execution.native.application.base.Refines cfg)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hfinalActive : runtime.image.activeAddress?
      final.native.application.base.memory = some instruction.address)
    (hfinal : final ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) schedule execution).support) :
    final.native.application.base.Refines cfg ∧
      final.native.application.active = execution.native.application.active ∧
      execution.native.application.base.memory.clock ≤
        final.native.application.base.memory.clock := by
  induction schedule generalizing execution final with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hfinal
      subst final
      exact ⟨hrefines, rfl, Nat.le_refl _⟩
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind,
        Set.mem_iUnion] at hfinal
      obtain ⟨middle, hmiddle, hrest⟩ := hfinal
      have hlength := runtime.application.runPolicies_environmentHistory_length players
        (runtime.blockEnvironment roster) [invocation] execution middle (by
          simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
      have hmiddleActive : runtime.image.activeAddress?
          middle.native.application.base.memory = some instruction.address := by
        by_contra hinactive
        have hstutter := runtime.runPolicies_block_inactive roster players rest middle final
          instruction (by
            intro index hlo hhi
            apply hindex index
            · omega
            · simp only [List.countP_cons, List.countP_nil] at hlength ⊢
              omega) hinactive hrest
        have hmemory : final.native.application.base.memory =
            middle.native.application.base.memory := congrArg Prod.fst hstutter
        rw [hmemory] at hfinalActive
        exact hinactive hfinalActive
      have hstep : middle.native.application.base.Refines cfg ∧
          middle.native.application.active = execution.native.application.active ∧
          execution.native.application.base.memory.clock ≤
            middle.native.application.base.memory.clock := by
        cases invocation with
        | player who =>
            simp only [MessageApplication.invoke, FinDist.support_bind,
              Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hcommand⟩ := hmiddle
            obtain ⟨hr, ha, hc⟩ :=
              runtime.playerStep_refines who execution middle command cfg hrefines hcommand
            exact ⟨hr, ha, Nat.le_of_eq hc.symm⟩
        | environment =>
            apply runtime.invoke_refines_of_active roster players execution middle
              .environment instruction owner cfg
            · apply hindex execution.environmentHistory.length
              · exact Nat.le_refl _
              · simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
                omega
            · exact howner
            · exact hrefines
            · exact hactive
            · exact hmiddleActive
            · exact hmiddle
      obtain ⟨hrestRefines, hrestActivation, hrestClock⟩ :=
        ih middle final (by
          intro index hlo hhi
          apply hindex index
          · omega
          · simp only [List.countP_cons, List.countP_nil] at hlength ⊢
            omega) hstep.1 hmiddleActive hfinalActive hrest
      exact ⟨hrestRefines, hrestActivation.trans hstep.2.1,
        Nat.le_trans hstep.2.2 hrestClock⟩

/-- At every still-active supported checkpoint after the actual block clock
slot, a ready binding source has a concrete eligible expiry for any relay.
Refinement, activation origin, overdue timing, consistency, and fresh serial
are all transported from the beginning of the actual prefix. -/
theorem binding_source_relay_eligibility_after_clock
    (runtime : WindowedApplication P L) (roster : List P)
    (players : P → runtime.application.PlayerPolicy)
    {Γ : VCtx P L} {name : VarId} {sourceOwner : P} {ty : L.Ty}
    (guard : L.Expr ((name, ty) :: eraseVCtx (viewVCtx sourceOwner Γ)) L.bool)
    (tail : VegasCore P L ((name, .sealed sourceOwner ty) :: Γ))
    (fallback : SourceDecisionSite.PublicFallback (.here guard tail))
    (fresh : FreshBindings (.commit name sourceOwner guard tail))
    (build : ToEventGraph.BuildState P L Γ) (deadline : Nat)
    (current : ToEventGraph.CoupledAt
      (compileCore (.commit name sourceOwner guard tail) fresh build).graph build)
    (instruction : ApplicationInstruction P L) (activation : Activation Nat)
    (execution middle : runtime.application.PolicyExecution)
    (priorRelays : List (@Invocation P)) (relay : P)
    (howner : instruction.submitter = some sourceOwner)
    (hindex : ∀ index, execution.environmentHistory.length ≤ index →
      index < execution.environmentHistory.length +
        (Invocation.environment :: priorRelays).countP Invocation.isEnvironment →
      runtime.image.instructions[index / (roster.length + 2)]? = some instruction)
    (hslot : execution.environmentHistory.length % (roster.length + 2) = 1)
    (hactive : runtime.image.activeAddress?
      execution.native.application.base.memory = some instruction.address)
    (hactivation : execution.native.application.active = some activation)
    (hkey : activation.key = instruction.address)
    (hcode : runtime.image.lookup activation.key = some (.bind
      (fallback.bindingTimeoutCode fresh build deadline)))
    (hrefines : execution.native.application.base.Refines current.current.graph.1)
    (hconsistent : runtime.Consistent execution.native.application)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hmiddleActive : runtime.image.activeAddress?
      middle.native.application.base.memory = some instruction.address)
    (hmiddle : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) (.environment :: priorRelays) execution).support) :
    let chosen := L.eval fallback.expr current.current.source.erasePubEnv
    ∃ payload resolved,
      runtime.dueExpiry?
        (middle.native.application.base.memory, middle.native.application.active) =
          some payload ∧
      middle.native.pool.lookup (relay, middle.native.pool.nextSerial relay) = none ∧
      runtime.handle middle.native.application
        ⟨(relay, middle.native.pool.nextSerial relay), payload⟩ = some resolved ∧
      ∃ next : ToEventGraph.CoupledAt
          (compileCore (.commit name sourceOwner guard tail) fresh build).graph
          (build.addCommitEvent name sourceOwner guard fresh.1).1,
        next.current.source = current.current.source.cons chosen ∧
        resolved.base.Refines next.current.graph.1 := by
  have hinitialIndex := hindex execution.environmentHistory.length
    (Nat.le_refl _) (by
      simp only [List.countP_cons, Invocation.isEnvironment, ↓reduceIte]
      omega)
  obtain ⟨clocked, hclockLaw, hclock, hclockRefines, hclockActivation,
      hclockActive⟩ := runtime.block_clock_step_checkpoint roster players execution
    instruction activation current.current.graph.1 hinitialIndex hslot hactive
    hactivation hkey hrefines
  have hclockedSupport : clocked ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) [.environment] execution).support := by
    rw [hclockLaw]
    simp
  have hclockedLength := runtime.application.runPolicies_environmentHistory_length players
    (runtime.blockEnvironment roster) [.environment] execution clocked hclockedSupport
  have hmiddleTail : middle ∈ (runtime.application.runPolicies players
      (runtime.blockEnvironment roster) priorRelays clocked).support := by
    rw [show Invocation.environment :: priorRelays =
      [Invocation.environment] ++ priorRelays by rfl,
      MessageApplication.runPolicies_append, hclockLaw, FinDist.pure_bind] at hmiddle
    exact hmiddle
  obtain ⟨hmiddleRefines, hmiddleActivation, hclockMono⟩ :=
    runtime.runPolicies_refines_of_final_active roster players priorRelays clocked middle
      instruction sourceOwner current.current.graph.1 howner (by
        intro index hlo hhi
        apply hindex index
        · omega
        · simp only [List.countP_cons, List.countP_nil,
            Invocation.isEnvironment, ↓reduceIte] at hclockedLength ⊢
          omega) hclockRefines hclockActive hmiddleActive hmiddleTail
  have hmiddleConsistent := runtime.runPolicies_consistent players
    (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hconsistent hmiddle
  have hmiddleFresh := (runtime.application.runPolicies_serialsBeforeNext players
    (runtime.blockEnvironment roster) (.environment :: priorRelays) execution middle
    hserials hmiddle).lookup_nextSerial_eq_none relay
  have hmiddleActivation' : middle.native.application.active = some activation :=
    hmiddleActivation.trans (hclockActivation.trans hactivation)
  have hoverdue : activation.since + runtime.windowOf activation.key <
      middle.native.application.base.memory.clock := by
    rw [hkey]
    omega
  exact runtime.binding_source_relay_eligibility guard tail fallback fresh build deadline
    current middle activation relay hmiddleConsistent hmiddleActivation' hcode
    hmiddleRefines hoverdue hmiddleFresh

/-- The native pool's fresh-next-serial invariant survives any actual policy
prefix, so relay freshness is obtained from reachability rather than assumed
separately at the relay checkpoint. -/
theorem runPolicies_lookup_nextSerial_eq_none
    (runtime : WindowedApplication P L)
    (players : P → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation P))
    (execution next : runtime.application.PolicyExecution)
    (hserials : execution.native.pool.SerialsBeforeNext)
    (hnext : next ∈ (runtime.application.runPolicies players environment schedule
      execution).support) (who : P) :
    next.native.pool.lookup (who, next.native.pool.nextSerial who) = none := by
  exact (runtime.application.runPolicies_serialsBeforeNext players environment schedule
    execution next hserials hnext).lookup_nextSerial_eq_none who

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.runPolicies_refines_of_final_active'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.runPolicies_refines_of_final_active

/-- info: 'Vegas.WindowedApplication.binding_source_relay_eligibility_after_clock'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.binding_source_relay_eligibility_after_clock
