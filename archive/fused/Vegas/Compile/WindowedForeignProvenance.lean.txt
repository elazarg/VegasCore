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

namespace Vegas.ApplicationImage

variable {P : Type} {L : IExpr}

/-- An address belonging to an emitted instruction strictly before the given
block coordinate. Instruction coordinates and node addresses are distinct. -/
def AddressBefore (image : ApplicationImage P L) (blocks address : Nat) : Prop :=
  ∃ index < blocks, ∃ instruction,
    image.instructions[index]? = some instruction ∧ instruction.address = address

@[simp] theorem addressBefore_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (blocks address : Nat) :
    (image.withBindingTimeouts select).AddressBefore blocks address ↔
      image.AddressBefore blocks address := by
  simp [AddressBefore, withBindingTimeouts, List.getElem?_map, Option.map_eq_some_iff]

@[simp] theorem addressBefore_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty))
    (blocks address : Nat) :
    (image.withChoiceTimeouts select).AddressBefore blocks address ↔
      image.AddressBefore blocks address := by
  simp [AddressBefore, withChoiceTimeouts, List.getElem?_map, Option.map_eq_some_iff]

end Vegas.ApplicationImage

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- At a completed block boundary, every foreign envelope known to any observer
targets an instruction that has already completed. The focal principal's
unrestricted traffic is deliberately excluded. -/
def ForeignKnownCompleted (runtime : WindowedApplication P L) (who : P)
    (state : runtime.application.State) : Prop :=
  ∀ observer id message, (state.pool.observe observer).known? id = some message →
    message.sender ≠ who →
    ∃ address, message.payload.address? = some address ∧
      state.application.base.memory.done address = true

/-- Foreign traffic targets the designated set of instruction addresses.
Focal traffic remains unrestricted, including anticipatory submissions. -/
def ForeignAddressed (who : P) (allowed : Nat → Prop)
    (message : Message P (ApplicationImage.Payload P L)) : Prop :=
  message.sender = who ∨ ∃ address, message.payload.address? = some address ∧
    allowed address

/-- When every designated address is completed, every foreign message known
through any retained carrier has completed-address provenance. -/
theorem ForeignAddressed.completedKnown
    (runtime : WindowedApplication P L) (who : P)
    (allowed : Nat → Prop)
    (state : runtime.application.State)
    (hsafe : state.pool.Satisfies (ForeignAddressed who allowed))
    (hcompleted : ∀ address, allowed address →
      state.application.base.memory.done address = true) :
    runtime.ForeignKnownCompleted who state := by
  intro observer id message hknown hforeign
  have hmem := MessagePool.View.known?_mem (state.pool.observe observer) id message hknown
  simp only [MessagePool.observe, List.mem_append] at hmem
  have hsmessage : ForeignAddressed who allowed message := by
    rcases hmem with (hsent | hinbox) | hledger
    · exact hsafe.2.2.2 observer message hsent
    · exact hsafe.2.2.1 observer message hinbox
    · exact hsafe.2.1 message hledger
  rcases hsmessage with hfocal | ⟨address, haddress, hold⟩
  · exact False.elim (hforeign hfocal)
  · exact ⟨address, haddress, hcompleted address hold⟩

/-- A submitted command from a gated reference policy necessarily has an
instruction selected by its actual local history coordinate. -/
theorem blockPlayer_submit_has_index (runtime : WindowedApplication P L) (who : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (payload : ApplicationImage.Payload P L)
    (hcommand : .submit payload ∈ (runtime.blockPlayer who base history view).support) :
    ∃ instruction, runtime.image.instructions[history.length / 3]? = some instruction := by
  cases hindex : runtime.image.instructions[history.length / 3]? with
  | none => simp [blockPlayer, hindex] at hcommand
  | some instruction => exact ⟨instruction, rfl⟩

/-- Completed-address provenance makes every retained foreign envelope inert.
This is the boundary form needed by replay privacy; no payload typing or
canonical decoder hypothesis is required. -/
theorem ForeignKnownCompleted.inert
    (runtime : WindowedApplication P L) (who : P)
    (state : runtime.application.State)
    (hcompleted : runtime.ForeignKnownCompleted who state) :
    runtime.ForeignKnownInert who state := by
  intro observer id message hknown hforeign
  obtain ⟨address, haddress, hdone⟩ :=
    hcompleted observer id message hknown hforeign
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
the designated instruction addresses. Replay preserves original authorship and the focal
policy remains unrestricted. Alignment is required only for the finite ranges
of history lengths actually traversed by the segment. -/
theorem runPolicies_foreignAddressed_of_history_bounds
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (schedule : List (@Invocation P)) (allowed : Nat → Prop)
    (execution next :
      (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hindex : ∀ actor index, (execution.principalHistory actor).length ≤ index →
      index < (execution.principalHistory actor).length +
        schedule.countP (fun call => match call with
          | .player principal => decide (principal = actor)
          | .environment => false) →
      ∀ instruction, getElem?
        (plan.windowed deadlineOf binding choice windowOf).image.instructions (index / 3) =
          some instruction → allowed instruction.address)
    (hsafe : execution.native.pool.Satisfies
      (WindowedApplication.ForeignAddressed who allowed))
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement)
      environment schedule execution).support) :
    next.native.pool.Satisfies
      (WindowedApplication.ForeignAddressed who allowed) := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  let players := plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement
  let safe := WindowedApplication.ForeignAddressed (L := L) who allowed
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
            · have hreference : .submit payload ∈ (runtime.blockPlayer actor
                  (runtime.liftPlayerPolicy (plan.liftProfile deadlineOf profile actor))
                  (execution.principalHistory actor)
                  (State.observe runtime.application execution.native actor)).support := by
                simpa only [windowedPlayers, Function.update_of_ne hactor,
                  windowedReferencePlayers] using hcommand
              obtain ⟨instruction, hselected⟩ := runtime.blockPlayer_submit_has_index actor _ _ _
                payload hreference
              have haddress := plan.blockPlayer_submit_address_of_index deadlineOf binding choice
                windowOf profile (execution.principalHistory actor)
                (State.observe runtime.application execution.native actor) actor instruction
                hselected payload hreference
              exact Or.inr ⟨instruction.address, haddress,
                hindex actor _ (Nat.le_refl _) (by simp) instruction hselected⟩
        | environment =>
            simp only [MessageApplication.invoke, FinDist.support_bind, Set.mem_iUnion] at hmiddle
            obtain ⟨command, _, hstep⟩ := hmiddle
            exact runtime.application.environmentPolicyStep_pool_satisfies safe execution middle
              command hsafe hstep
      apply ih middle ?_ hsafeMiddle hnext
      intro actor index hlo hhi selected hselected
      have hlength := runtime.application.runPolicies_principalHistory_length actor players
        environment [invocation] execution middle (by
          simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle)
      apply hindex actor index ?_ ?_ selected hselected
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
      (WindowedApplication.ForeignAddressed who
        (fun address => completed address ∨ address = instruction.address)))
    (hnext : next ∈ ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
      (plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement)
      ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment roster)
      (WindowedApplication.blockInvocations roster) execution).support) :
    next.native.pool.Satisfies
      (WindowedApplication.ForeignAddressed who
        (fun address => completed address ∨ address = instruction.address)) := by
  apply plan.runPolicies_foreignAddressed_of_history_bounds deadlineOf binding choice windowOf
    profile who replacement ((plan.windowed deadlineOf binding choice windowOf).blockEnvironment
      roster) (WindowedApplication.blockInvocations roster)
    (fun address => completed address ∨ address = instruction.address) execution next
    ?_ hsafe hnext
  intro actor index hlo hhi selected hselected
  have hcount : (WindowedApplication.blockInvocations roster).countP (fun call => match call with
      | .player principal => decide (principal = actor)
      | .environment => false) = if actor ∈ roster then 3 else 0 :=
    WindowedApplication.blockInvocations_player_count roster hroster actor
  rw [hcount] at hhi
  by_cases hmem : actor ∈ roster
  · simp only [hmem, ↓reduceIte] at hhi
    have hlength := hplayers actor hmem
    have hquotient : index / 3 = block := by omega
    rw [hquotient, hindex] at hselected
    cases Option.some.inj hselected
    exact Or.inr rfl
  · simp only [hmem, ↓reduceIte, Nat.add_zero] at hhi
    omega

/-- In a genuine initialized repeated-block run, every retained foreign
message belongs to the emitted instruction prefix. This covers pending and
delivered copies as well as the ledger and sent histories. No invariant on
an intermediate pool is assumed. -/
theorem runPolicies_repeatedBlocks_foreignAddressed
    (environment : (plan.windowed deadlineOf binding choice windowOf).application.EnvironmentPolicy)
    (roster : List P) (hroster : roster.Nodup) (blocks : Nat)
    (execution : (plan.windowed deadlineOf binding choice windowOf).application.PolicyExecution)
    (hreached : execution ∈
      ((plan.windowed deadlineOf binding choice windowOf).application.runPolicies
        (plan.windowedPlayers profile deadlineOf binding choice windowOf who replacement)
        environment
        (List.replicate blocks (WindowedApplication.blockInvocations roster)).flatten
        (plan.windowedInitialExecution deadlineOf binding choice windowOf)).support) :
    execution.native.pool.Satisfies (WindowedApplication.ForeignAddressed who
      ((plan.windowed deadlineOf binding choice windowOf).image.AddressBefore blocks)) := by
  let runtime := plan.windowed deadlineOf binding choice windowOf
  apply plan.runPolicies_foreignAddressed_of_history_bounds deadlineOf binding choice windowOf
    profile who replacement environment
    (List.replicate blocks (WindowedApplication.blockInvocations roster)).flatten
    (runtime.image.AddressBefore blocks)
    (plan.windowedInitialExecution deadlineOf binding choice windowOf) execution ?_ ?_ hreached
  · intro actor index _ hhi instruction hselected
    have hcount : List.countP (fun call => match call with
          | .player principal => decide (principal = actor)
          | .environment => false)
        (List.replicate blocks (WindowedApplication.blockInvocations roster)).flatten ≤
          3 * blocks := by
      clear hreached hhi
      have hone : List.countP (fun call => match call with
          | .player principal => decide (principal = actor)
          | .environment => false) (WindowedApplication.blockInvocations roster) =
            if actor ∈ roster then 3 else 0 :=
        WindowedApplication.blockInvocations_player_count roster hroster actor
      induction blocks with
      | zero => simp
      | succ blocks ih =>
          rw [List.replicate_succ, List.flatten_cons, List.countP_append, hone]
          split <;> omega
    change index < 0 + _ at hhi
    simp only [Nat.zero_add] at hhi
    exact ⟨index / 3, by omega, instruction, hselected, rfl⟩
  · exact MessagePool.Satisfies.empty

end Block

namespace WindowedCheckpoint

/-- At every actual source checkpoint, foreign messages known through any
retained carrier target completed instructions. The prefix provenance is
derived from the initialized runner, not added as an assumption. -/
theorem foreignKnownCompleted
    {rootContext Γ : VCtx P L} {rootPending pending : Finset VarId}
    {rootProg : VegasCore P L rootContext} {prog : VegasCore P L Γ}
    {rootAccounted : CommitmentAccounting rootPending rootProg}
    {accounted : CommitmentAccounting pending prog}
    {rootFresh : FreshBindings rootProg} {fresh : FreshBindings prog}
    {rootState : BuildState P L rootContext} {state : BuildState P L Γ}
    {root : ApplicationPlan rootAccounted rootFresh rootState}
    {rootProfile : SourceBehavioralProfile rootProg} {deadlineOf : Nat → Nat}
    {binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)}
    {choice : (code : PublicChoiceCode P L) → Option (PublicFallbackCode L code.guard.ty)}
    {windowOf : Nat → Nat} {roster : List P} {who : P}
    {replacement : (root.windowed deadlineOf binding choice windowOf).application.PlayerPolicy}
    {blockIndex : Nat} {plan : ApplicationPlan accounted fresh state}
    {profile : SourceBehavioralProfile prog}
    {current : CoupledAt (compileCore prog fresh state).graph state}
    {execution : (root.windowed deadlineOf binding choice windowOf).application.PolicyExecution}
    (checkpoint : WindowedCheckpoint root rootProfile deadlineOf binding choice windowOf
      ((root.windowed deadlineOf binding choice windowOf).blockService roster)
      who replacement blockIndex plan profile current execution)
    (hroster : roster.Nodup) :
    (root.windowed deadlineOf binding choice windowOf).ForeignKnownCompleted who
      execution.native := by
  let runtime := root.windowed deadlineOf binding choice windowOf
  have hpool := root.runPolicies_repeatedBlocks_foreignAddressed deadlineOf binding choice windowOf
    rootProfile who replacement (runtime.blockEnvironment roster) roster hroster blockIndex
    execution checkpoint.reached
  apply WindowedApplication.ForeignAddressed.completedKnown runtime who
    (runtime.image.AddressBefore blockIndex) execution.native hpool
  intro address haddress
  have horiginal : (root.image deadlineOf).AddressBefore blockIndex address := by
    simpa only [runtime, windowed, ApplicationImage.addressBefore_withChoiceTimeouts,
      ApplicationImage.addressBefore_withBindingTimeouts] using haddress
  obtain ⟨index, hindex, instruction, hlookup, hinstruction⟩ := horiginal
  obtain ⟨before, hlength, hroot, hcompleted, _⟩ := checkpoint.completed_instructions
  change (root.instructions deadlineOf)[index]? = some instruction at hlookup
  rw [hroot, List.getElem?_append_left (by omega)] at hlookup
  rw [← hinstruction]
  exact hcompleted instruction (List.mem_of_getElem? hlookup)

end WindowedCheckpoint

end Vegas.ApplicationPlan

/-- info: 'Vegas.ApplicationPlan.runPolicies_full_block_foreignBlockAddressed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_full_block_foreignBlockAddressed

/-- info: 'Vegas.ApplicationPlan.runPolicies_repeatedBlocks_foreignAddressed' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.runPolicies_repeatedBlocks_foreignAddressed

/-- info: 'Vegas.ApplicationPlan.WindowedCheckpoint.foreignKnownCompleted' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.WindowedCheckpoint.foreignKnownCompleted
