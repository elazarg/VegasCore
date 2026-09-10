/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrderPrefix
import Vegas.Compile.ApplicationPolicyAddresses
import Vegas.Compile.WindowedReplayPrivacy
import Vegas.Compile.WindowedSourceSafety
import Vegas.Compile.WindowedBlockProvenance
import Vegas.Compile.WindowedCheckpoint
import Interaction.MessageApplicationPolicyInvariant

/-! # Completed foreign-message provenance at window boundaries -/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At a completed block boundary, every retained envelope authored by another
principal targets an instruction that has already completed. The focal
principal's unrestricted traffic is deliberately excluded. -/
def ForeignLedgerCompleted (runtime : WindowedApplication P L) (who : P)
    (state : runtime.application.State) : Prop :=
  ∀ message ∈ state.pool.ledger, message.sender ≠ who →
    ∃ address, message.payload.address? = some address ∧
      state.application.base.memory.done address = true

/-- Static message classification used while one emitted block is active.
Foreign traffic must target either an address completed before the block or
the block's own address. Focal traffic remains unrestricted. -/
def ForeignBlockAddressed (who : P) (completed : Nat → Prop) (current : Nat)
    (message : Message P (ApplicationImage.Payload P L)) : Prop :=
  message.sender = who ∨ ∃ address, message.payload.address? = some address ∧
    (completed address ∨ address = current)

/-- Once the current block address is completed, the static within-block
classification yields completed-address provenance for every foreign ledger
entry. -/
theorem ForeignBlockAddressed.completedLedger
    (runtime : WindowedApplication P L) (who : P)
    (completed : Nat → Prop) (current : Nat)
    (state : runtime.application.State)
    (hsafe : state.pool.Satisfies (ForeignBlockAddressed who completed current))
    (hcompleted : ∀ address, completed address →
      state.application.base.memory.done address = true)
    (hcurrent : state.application.base.memory.done current = true) :
    runtime.ForeignLedgerCompleted who state := by
  intro message hledger hforeign
  rcases hsafe.2.1 message hledger with hfocal | ⟨address, haddress, hold | rfl⟩
  · exact False.elim (hforeign hfocal)
  · exact ⟨address, haddress, hcompleted address hold⟩
  · exact ⟨address, haddress, hcurrent⟩

/-- Completed-address provenance makes every retained foreign envelope inert.
This is the boundary form needed by replay privacy; no payload typing or
canonical decoder hypothesis is required. -/
theorem ForeignLedgerCompleted.inert
    (runtime : WindowedApplication P L) (who : P)
    (state : runtime.application.State)
    (hcompleted : runtime.ForeignLedgerCompleted who state) :
    runtime.ForeignLedgerInert who state := by
  intro message hledger hforeign
  obtain ⟨address, haddress, hdone⟩ := hcompleted message hledger hforeign
  have hinactive : runtime.image.activeAddress? state.application.base.memory ≠
      some address := by
    intro hactive
    have hnotDone := runtime.image.activeAddress?_not_done
      state.application.base.memory address hactive
    rw [hdone] at hnotDone
    contradiction
  simp only [WindowedApplication.handle]
  cases hactivation : state.application.active with
  | none => rfl
  | some activation =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      split
      · rw [(runtime.atOrigin activation.since).ordered_handle_reject
          state.application.base message address haddress]
        · rfl
        · simpa only [WindowedApplication.atOrigin,
            ApplicationImage.activeAddress?_withDeadlines] using hinactive
      · rfl

end Vegas.WindowedApplication

namespace Vegas.ApplicationPlan

open EventGraph ToEventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- A supported submission from an unchanged block-gated source policy targets
the actual active address. This covers both a normal lifted source command and
the dedicated expiry relay slot; all padding branches are waits. -/
theorem blockPlayer_submit_address
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh state) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (profile : SourceBehavioralProfile prog)
    (history : List (plan.windowed deadlineOf binding choice windowOf).application.PlayerEntry)
    (view : (plan.windowed deadlineOf binding choice windowOf).application.View)
    (actor : P) (payload : ApplicationImage.Payload P L)
    (hcommand : .submit payload ∈
      ((plan.windowed deadlineOf binding choice windowOf).blockPlayer actor
        ((plan.windowed deadlineOf binding choice windowOf).liftPlayerPolicy
          (plan.liftProfile deadlineOf profile actor)) history view).support) :
    payload.address? = (plan.image deadlineOf).activeAddress?
      ((plan.windowed deadlineOf binding choice windowOf).eraseView view).application := by
  dsimp only [windowed, WindowedApplication.application] at hcommand
  rcases view with ⟨messages, ⟨memory, activation⟩, receipts⟩
  let runtime := plan.windowed deadlineOf binding choice windowOf
  let sourceView : (plan.image deadlineOf).application.View :=
    { messages := messages, application := memory, receipts := receipts }
  unfold WindowedApplication.blockPlayer at hcommand
  dsimp only [windowed, WindowedApplication.application] at hcommand
  cases hindex : getElem?
      (plan.windowed deadlineOf binding choice windowOf).image.instructions
      (history.length / 3) with
  | none =>
      dsimp only [windowed] at hindex
      simp only [hindex, FinDist.mem_support_pure] at hcommand
      contradiction
  | some instruction =>
      dsimp only [windowed] at hindex
      simp only [hindex] at hcommand
      split at hcommand
      · rename_i hactive
        split at hcommand
        · split at hcommand
          · unfold WindowedApplication.liftPlayerPolicy at hcommand
            rw [FinDist.support_map] at hcommand
            obtain ⟨command, hsupported, hcommand⟩ := hcommand
            cases command with
            | privateCommand command => cases hcommand
            | replay id => cases hcommand
            | wait => cases hcommand
            | submit sourcePayload =>
                simp only [WindowedApplication.liftPlayerCommand] at hcommand
                injection hcommand with hpayload
                subst payload
                exact plan.liftProfileIn_submit_address deadlineOf
                  (plan.image deadlineOf) profile [] rfl memory (by simp) actor
                  (history.map runtime.erasePlayerEntry) sourceView rfl _ hsupported
          · simp at hcommand
        · simp only [FinDist.mem_support_pure] at hcommand
          change MessageInterface.PlayerCommand.submit payload =
            runtime.relayCommand (runtime.dueExpiry? (memory, activation))
              MessageInterface.PlayerCommand.wait at hcommand
          cases hdue : runtime.dueExpiry? (memory, activation) with
          | none =>
              rw [hdue] at hcommand
              cases hcommand
          | some expiry =>
              rw [hdue] at hcommand
              injection hcommand with hpayload
              subst payload
              have haddress := runtime.dueExpiry?_address (memory, activation) instruction
                expiry hactive hdue
              have hactiveSource : (plan.image deadlineOf).activeAddress? memory =
                  some instruction.address := by
                simpa only [runtime, windowed,
                  ApplicationImage.activeAddress?_withChoiceTimeouts,
                  ApplicationImage.activeAddress?_withBindingTimeouts] using hactive
              simpa only [WindowedApplication.eraseView] using
                haddress.trans hactiveSource.symm
      · simp at hcommand

/-- When block-history alignment selects a concrete emitted instruction, every
supported submission of the unchanged gated source policy targets that fixed
instruction. Thus the within-block message invariant has a static address. -/
theorem blockPlayer_submit_address_of_index
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (plan : ApplicationPlan accounted fresh state) (deadlineOf : Nat → Nat)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (windowOf : Nat → Nat) (profile : SourceBehavioralProfile prog)
    (history : List (plan.windowed deadlineOf binding choice windowOf).application.PlayerEntry)
    (view : (plan.windowed deadlineOf binding choice windowOf).application.View)
    (actor : P) (instruction : ApplicationInstruction P L)
    (hindex : getElem?
      (plan.windowed deadlineOf binding choice windowOf).image.instructions
      (history.length / 3) = some instruction)
    (payload : ApplicationImage.Payload P L)
    (hcommand : .submit payload ∈
      ((plan.windowed deadlineOf binding choice windowOf).blockPlayer actor
        ((plan.windowed deadlineOf binding choice windowOf).liftPlayerPolicy
          (plan.liftProfile deadlineOf profile actor)) history view).support) :
    payload.address? = some instruction.address := by
  dsimp only [windowed, WindowedApplication.application] at hcommand
  dsimp only [windowed] at hindex
  rcases view with ⟨messages, ⟨memory, activation⟩, receipts⟩
  let runtime := plan.windowed deadlineOf binding choice windowOf
  have hactive : runtime.image.activeAddress? memory =
      some instruction.address := by
    have hsupported := hcommand
    unfold WindowedApplication.blockPlayer at hsupported
    simp only [hindex] at hsupported
    split at hsupported
    · assumption
    · simp at hsupported
  have haddress := plan.blockPlayer_submit_address deadlineOf binding choice windowOf profile
    history { messages := messages, application := (memory, activation), receipts := receipts }
      actor payload hcommand
  have himage : (plan.image deadlineOf).activeAddress? memory =
      runtime.image.activeAddress? memory := by
    simp only [runtime, windowed, ApplicationImage.activeAddress?_withChoiceTimeouts,
      ApplicationImage.activeAddress?_withBindingTimeouts]
  simpa only [WindowedApplication.eraseView] using haddress.trans (himage.trans hactive)

section Block

variable {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
variable {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
variable {state : BuildState P L Γ}
variable (plan : ApplicationPlan accounted fresh state) (deadlineOf : Nat → Nat)
variable (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
variable (choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
variable (windowOf : Nat → Nat) (profile : SourceBehavioralProfile prog) (who : P)
variable (replacement : (plan.windowed deadlineOf binding choice windowOf).application.PlayerPolicy)

/-- During a history-aligned segment, generated nonfocal submissions target
the selected instruction. Replay preserves original authorship and the focal
policy remains unrestricted. Alignment is required only for the finite ranges
of history lengths actually traversed by the segment. -/
theorem runPolicies_foreignBlockAddressed_of_history_bounds
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (instruction : ApplicationInstruction P L)
    (completed : Nat → Prop)
    (execution next :
      (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hindex : ∀ actor index, (execution.principalHistory actor).length ≤ index →
      index < (execution.principalHistory actor).length +
        schedule.countP (fun call => match call with
          | .player principal => decide (principal = actor)
          | .environment => false) →
      (plan.windowed deadlineOf binding choice windowOf).image.instructions[index / 3]? =
        some instruction)
    (hsafe : execution.native.pool.Satisfies
      (WindowedApplication.ForeignBlockAddressed who completed instruction.address))
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement)
      environment schedule execution).support) :
    next.native.pool.Satisfies
      (WindowedApplication.ForeignBlockAddressed who completed instruction.address) := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  let players := plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement
  let safe := WindowedApplication.ForeignBlockAddressed (L := L) who completed instruction.address
  induction schedule generalizing execution with
  | nil =>
      simp only [MessageApplication.runPolicies, FinDist.mem_support_pure] at hnext
      subst next
      exact hsafe
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies, FinDist.support_bind, Set.mem_iUnion] at hnext
      obtain ⟨middle, hmiddle, hnext⟩ := hnext
      have hsafeMiddle : middle.native.pool.Satisfies safe := by
        cases invocation with
        | player actor =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, hcommand, hstep⟩ := hmiddle
            apply runtime.application.playerStep_pool_satisfies safe actor execution middle command
              hsafe ?_ hstep
            intro payload hsubmit
            subst command
            by_cases hactor : actor = who
            · exact Or.inl hactor
            · have hselected := hindex actor _ (Nat.le_refl _) (by simp)
              have haddress := plan.blockPlayer_submit_address_of_index deadlineOf binding choice
                windowOf profile (execution.principalHistory actor)
                (State.observe runtime.application execution.native actor) actor instruction
                hselected payload (by
                  simpa only [windowedPlayers, Function.update_of_ne hactor,
                    windowedReferencePlayers] using hcommand)
              exact Or.inr ⟨instruction.address, haddress, Or.inr rfl⟩
        | environment =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            exact runtime.application.environmentPolicyStep_pool_satisfies safe execution middle
              command hsafe hstep
      apply ih middle ?_ hsafeMiddle hnext
      intro actor index hlo hhi
      have hlength := runtime.application.runPolicies_principalHistory_length actor players
        environment [invocation] execution middle (by
          simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
      apply hindex actor index
      · omega
      · rw [hlength] at hhi
        convert hhi using 1
        simp only [List.countP_cons, List.countP_nil,
          Nat.zero_add, Nat.add_assoc, Nat.add_comm]
        rfl

/-- Every message retained after an actual aligned generated block has either
focal authorship or a prior/current instruction address. No submission-shape
premise is imposed on the focal policy, and no alignment premise quantifies
over unsupported executions. -/
theorem runPolicies_full_block_foreignBlockAddressed
    (roster : List P) (hroster : roster.Nodup) (block : Nat)
    (instruction : ApplicationInstruction P L) (completed : Nat → Prop)
    (execution next :
      (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hindex : (plan.windowed deadlineOf binding choice windowOf).image.instructions[block]? =
      some instruction)
    (hplayers : ∀ actor ∈ roster, (execution.principalHistory actor).length = 3 * block)
    (hsafe : execution.native.pool.Satisfies
      (WindowedApplication.ForeignBlockAddressed who completed instruction.address))
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement)
      ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    next.native.pool.Satisfies
      (WindowedApplication.ForeignBlockAddressed who completed instruction.address) := by
  apply plan.runPolicies_foreignBlockAddressed_of_history_bounds deadlineOf binding choice windowOf
    profile who replacement ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment
      roster) (WindowedApplication.blockInvocations roster) instruction completed execution next
    ?_ hsafe hnext
  intro actor index hlo hhi
  have hcount : (WindowedApplication.blockInvocations roster).countP (fun call => match call with
      | .player principal => decide (principal = actor)
      | .environment => false) = if actor ∈ roster then 3 else 0 :=
    WindowedApplication.blockInvocations_player_count roster hroster actor
  rw [hcount] at hhi
  by_cases hmem : actor ∈ roster
  · simp only [hmem, ↓reduceIte] at hhi
    have hlength := hplayers actor hmem
    have hquotient : index / 3 = block := by omega
    rw [hquotient]
    exact hindex
  · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi
    omega

end Block

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.runPolicies_full_block_foreignBlockAddressed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_full_block_foreignBlockAddressed
