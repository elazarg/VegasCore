/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationOrder
import Vegas.Compile.ApplicationBindingTimeouts
import Vegas.Compile.ApplicationPlanAllocation

/-! # Ordered admission with optional timeouts

Binding and public-choice timeout decoration retains instruction addresses, so
it also retains the ordered application's active address.  Consequently each
decorated ordered application has the original execution law for fixed policies
that neither inherit nor submit its new expiry traffic. Other pending traffic,
raw commands, service choices, delivery, inclusion, and replay remain arbitrary.
-/

noncomputable section

namespace Vegas.ApplicationInstruction

open EventGraph

variable {P : Type} {L : IExpr}

@[simp] theorem coveredNodes_withBindingTimeouts
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (instruction : ApplicationInstruction P L) :
    (instruction.withBindingTimeouts select).coveredNodes = instruction.coveredNodes := by
  cases instruction <;> rfl

@[simp] theorem coveredNodes_withChoiceTimeouts
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (instruction : ApplicationInstruction P L) :
    (instruction.withChoiceTimeouts select).coveredNodes = instruction.coveredNodes := by
  cases instruction <;> rfl

@[simp] theorem allocatedAt_withBindingTimeouts
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (initialFields : Nat) (instruction : ApplicationInstruction P L) :
    (instruction.withBindingTimeouts select).AllocatedAt initialFields ↔
      instruction.AllocatedAt initialFields := by
  cases instruction <;> rfl

@[simp] theorem allocatedAt_withChoiceTimeouts
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (initialFields : Nat) (instruction : ApplicationInstruction P L) :
    (instruction.withChoiceTimeouts select).AllocatedAt initialFields ↔
      instruction.AllocatedAt initialFields := by
  cases instruction <;> rfl

end Vegas.ApplicationInstruction

namespace Vegas.ApplicationImage

open EventGraph Interaction Interaction.MessageApplication
  GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

omit [DecidableEq P] in
theorem coveredNodes_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty)) :
    (image.withBindingTimeouts select).instructions.flatMap
        ApplicationInstruction.coveredNodes =
      image.instructions.flatMap ApplicationInstruction.coveredNodes := by
  simp [withBindingTimeouts, List.flatMap_map]

omit [DecidableEq P] in
theorem coveredNodes_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty)) :
    (image.withChoiceTimeouts select).instructions.flatMap
        ApplicationInstruction.coveredNodes =
      image.instructions.flatMap ApplicationInstruction.coveredNodes := by
  simp [withChoiceTimeouts, List.flatMap_map]

omit [DecidableEq P] in
theorem instructions_allocated_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields) :
    ∀ instruction ∈ (image.withBindingTimeouts select).instructions,
      instruction.AllocatedAt initialFields := by
  intro instruction hmem
  simp only [withBindingTimeouts, List.mem_map] at hmem
  obtain ⟨original, horiginal, rfl⟩ := hmem
  exact (ApplicationInstruction.allocatedAt_withBindingTimeouts
    select initialFields original).2 (hallocated original horiginal)

omit [DecidableEq P] in
theorem instructions_allocated_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (initialFields : Nat)
    (hallocated : ∀ instruction ∈ image.instructions,
      instruction.AllocatedAt initialFields) :
    ∀ instruction ∈ (image.withChoiceTimeouts select).instructions,
      instruction.AllocatedAt initialFields := by
  intro instruction hmem
  simp only [withChoiceTimeouts, List.mem_map] at hmem
  obtain ⟨original, horiginal, rfl⟩ := hmem
  exact (ApplicationInstruction.allocatedAt_withChoiceTimeouts
    select initialFields original).2 (hallocated original horiginal)

omit [DecidableEq P] in
theorem activeAddress?_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (memory : Memory P L) :
    (image.withBindingTimeouts select).activeAddress? memory = image.activeAddress? memory := by
  simp [activeAddress?, withBindingTimeouts, List.find?_map, Function.comp_def]

omit [DecidableEq P] in
theorem activeAddress?_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (memory : Memory P L) :
    (image.withChoiceTimeouts select).activeAddress? memory = image.activeAddress? memory := by
  simp [activeAddress?, withChoiceTimeouts, List.find?_map, Function.comp_def]

/-- Ordered admission and the underlying handler both agree away from binding
expiry traffic. -/
theorem ordered_handle_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (state : State P L) (message : Message P (Payload P L))
    (hordinary : message.payload.NotBindingExpiry) :
    (image.withBindingTimeouts select).orderedApplication.handle state message =
      image.orderedApplication.handle state message := by
  have hadmits : (image.withBindingTimeouts select).admitsMessage state.memory message =
      image.admitsMessage state.memory message := by
    unfold admitsMessage admitsAddress
    rw [image.activeAddress?_withBindingTimeouts select]
  change (if (image.withBindingTimeouts select).admitsMessage state.memory message then
      (image.withBindingTimeouts select).handle state message else none) =
    if image.admitsMessage state.memory message then image.handle state message else none
  rw [hadmits]
  split
  · exact image.handle_withBindingTimeouts select state message hordinary
  · rfl

/-- Ordered admission and the underlying handler both agree away from
public-choice expiry traffic. -/
theorem ordered_handle_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (state : State P L) (message : Message P (Payload P L))
    (hordinary : message.payload.NotChoiceExpiry) :
    (image.withChoiceTimeouts select).orderedApplication.handle state message =
      image.orderedApplication.handle state message := by
  have hadmits : (image.withChoiceTimeouts select).admitsMessage state.memory message =
      image.admitsMessage state.memory message := by
    unfold admitsMessage admitsAddress
    rw [image.activeAddress?_withChoiceTimeouts select]
  change (if (image.withChoiceTimeouts select).admitsMessage state.memory message then
      (image.withChoiceTimeouts select).handle state message else none) =
    if image.admitsMessage state.memory message then image.handle state message else none
  rw [hadmits]
  split
  · exact image.handle_withChoiceTimeouts select state message hordinary
  · rfl

theorem ordered_environmentStep_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (state : State P L) (command : EnvironmentCommand) :
    (image.withBindingTimeouts select).orderedApplication.environmentStep state command =
      image.orderedApplication.environmentStep state command := by
  cases command with
  | advance clock => rfl
  | sample address =>
      change (if (image.withBindingTimeouts select).admitsAddress state.memory address then
          (image.withBindingTimeouts select).sample state address else FinDist.pure state) =
        if image.admitsAddress state.memory address then
          image.sample state address else FinDist.pure state
      unfold admitsAddress
      rw [image.activeAddress?_withBindingTimeouts select,
        image.sample_withBindingTimeouts select]

theorem ordered_environmentStep_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (state : State P L) (command : EnvironmentCommand) :
    (image.withChoiceTimeouts select).orderedApplication.environmentStep state command =
      image.orderedApplication.environmentStep state command := by
  cases command with
  | advance clock => rfl
  | sample address =>
      change (if (image.withChoiceTimeouts select).admitsAddress state.memory address then
          (image.withChoiceTimeouts select).sample state address else FinDist.pure state) =
        if image.admitsAddress state.memory address then
          image.sample state address else FinDist.pure state
      unfold admitsAddress
      rw [image.activeAddress?_withChoiceTimeouts select,
        image.sample_withChoiceTimeouts select]

private theorem includePending_ordered_eq_of_handler_agrees
    (left right : ApplicationImage P L)
    (safe : Message P (Payload P L) → Prop)
    (hagrees : ∀ state message, safe message →
      left.orderedApplication.handle state message =
        right.orderedApplication.handle state message)
    (state : right.application.State) (id : MessageId P)
    (hsafe : state.pool.Satisfies safe) :
    left.orderedApplication.includePending state id =
      right.orderedApplication.includePending state id := by
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [left.orderedApplication.includePending_missing state id hlookup,
        right.orderedApplication.includePending_missing state id hlookup]
  | some message =>
      have hmessage : safe message :=
        hsafe.1 message (List.mem_of_find?_eq_some hlookup)
      unfold MessageApplication.includePending MessagePool.includeApplication
      simp only [MessagePool.includePending, hlookup]
      rw [hagrees state.application message hmessage]
      rfl

private theorem playerStep_ordered_eq (left right : ApplicationImage P L)
    (who : P) (execution : right.application.PolicyExecution)
    (command : right.application.PlayerCommand) :
    left.orderedApplication.playerStep who execution command =
      right.orderedApplication.playerStep who execution command := by
  cases command <;> rfl

private theorem environmentPolicyStep_ordered_eq
    (left right : ApplicationImage P L)
    (safe : Message P (Payload P L) → Prop)
    (hagrees : ∀ state message, safe message →
      left.orderedApplication.handle state message =
        right.orderedApplication.handle state message)
    (henvironment : ∀ state command,
      left.orderedApplication.environmentStep state command =
        right.orderedApplication.environmentStep state command)
    (execution : right.application.PolicyExecution)
    (command : right.application.EnvironmentPolicyCommand)
    (hsafe : execution.native.pool.Satisfies safe) :
    left.orderedApplication.environmentPolicyStep execution command =
      right.orderedApplication.environmentPolicyStep execution command := by
  cases command with
  | deliver observer id => rfl
  | «include» id =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind]
      rw [includePending_ordered_eq_of_handler_agrees left right safe hagrees
        execution.native id hsafe]
      rfl
  | application command =>
      simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
        EnvironmentPolicyCommand.toAction, MessageApplication.step]
      rw [henvironment execution.native.application command]
      rfl
  | wait => rfl

private theorem invoke_ordered_eq
    (left right : ApplicationImage P L)
    (safe : Message P (Payload P L) → Prop)
    (hagrees : ∀ state message, safe message →
      left.orderedApplication.handle state message =
        right.orderedApplication.handle state message)
    (henvironment : ∀ state command,
      left.orderedApplication.environmentStep state command =
        right.orderedApplication.environmentStep state command)
    (players : P → right.application.PlayerPolicy)
    (environment : right.application.EnvironmentPolicy)
    (execution : right.application.PolicyExecution) (invocation : @Invocation P)
    (hsafe : execution.native.pool.Satisfies safe) :
    left.orderedApplication.invoke players environment execution invocation =
      right.orderedApplication.invoke players environment execution invocation := by
  cases invocation with
  | player who =>
      simp only [MessageApplication.invoke]
      apply FinDist.bind_congr
      intro command _
      exact playerStep_ordered_eq left right who execution command
  | environment =>
      simp only [MessageApplication.invoke]
      apply FinDist.bind_congr
      intro command _
      exact environmentPolicyStep_ordered_eq left right safe hagrees henvironment
        execution command hsafe

private theorem runPolicies_ordered_eq_of_agrees
    (left right : ApplicationImage P L)
    (safe : Message P (Payload P L) → Prop)
    (hagrees : ∀ state message, safe message →
      left.orderedApplication.handle state message =
        right.orderedApplication.handle state message)
    (henvironment : ∀ state command,
      left.orderedApplication.environmentStep state command =
        right.orderedApplication.environmentStep state command)
    (players : P → right.application.PlayerPolicy)
    (environment : right.application.EnvironmentPolicy)
    (hsubmit : ∀ (execution : right.application.PolicyExecution) (who : P)
      (payload : Payload P L),
      .submit payload ∈ (players who (execution.principalHistory who)
        (MessageApplication.State.observe right.application execution.native who)).support →
      ∀ serial, safe ⟨(who, serial), payload⟩)
    (schedule : List (@Invocation P)) (execution : right.application.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies safe) :
    left.orderedApplication.runPolicies players environment schedule execution =
      right.orderedApplication.runPolicies players environment schedule execution := by
  induction schedule generalizing execution with
  | nil => rfl
  | cons invocation rest ih =>
      simp only [MessageApplication.runPolicies]
      rw [invoke_ordered_eq left right safe hagrees henvironment players environment
        execution invocation hsafe]
      apply FinDist.bind_congr
      intro middle hmiddle
      apply ih middle
      apply right.orderedApplication.runPolicies_pool_satisfies safe players environment
        hsubmit [invocation] execution middle hsafe
      simpa only [MessageApplication.runPolicies, FinDist.bind_pure] using hmiddle

/-- Binding-timeout decoration is conservative for the ordered interpreter on
fixed policies and initial pools without binding-expiry traffic. -/
theorem ordered_runPolicies_withBindingTimeouts (image : ApplicationImage P L)
    (select : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hsubmit : ∀ (execution : image.application.PolicyExecution) (who : P)
      (address : Nat), .submit (.expireBinding address) ∉
        (players who (execution.principalHistory who)
          (MessageApplication.State.observe image.application execution.native who)).support)
    (schedule : List (@Invocation P)) (execution : image.application.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies
      (fun message => message.payload.NotBindingExpiry)) :
    (image.withBindingTimeouts select).orderedApplication.runPolicies
        players environment schedule execution =
      image.orderedApplication.runPolicies players environment schedule execution := by
  refine runPolicies_ordered_eq_of_agrees (image.withBindingTimeouts select) image
    (fun message => message.payload.NotBindingExpiry)
    (fun state message hmessage =>
      image.ordered_handle_withBindingTimeouts select state message hmessage)
    (fun state command => image.ordered_environmentStep_withBindingTimeouts
      select state command) players environment ?_ schedule execution hsafe
  intro current who payload hsupported serial
  cases payload with
  | expireBinding address => exact False.elim (hsubmit current who address hsupported)
  | _ => trivial

/-- Public-choice-timeout decoration is conservative for the ordered
interpreter on fixed policies and initial pools without choice-expiry traffic. -/
theorem ordered_runPolicies_withChoiceTimeouts (image : ApplicationImage P L)
    (select : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hsubmit : ∀ (execution : image.application.PolicyExecution) (who : P)
      (address : Nat), .submit (.expireChoice address) ∉
        (players who (execution.principalHistory who)
          (MessageApplication.State.observe image.application execution.native who)).support)
    (schedule : List (@Invocation P)) (execution : image.application.PolicyExecution)
    (hsafe : execution.native.pool.Satisfies
      (fun message => message.payload.NotChoiceExpiry)) :
    (image.withChoiceTimeouts select).orderedApplication.runPolicies
        players environment schedule execution =
      image.orderedApplication.runPolicies players environment schedule execution := by
  refine runPolicies_ordered_eq_of_agrees (image.withChoiceTimeouts select) image
    (fun message => message.payload.NotChoiceExpiry)
    (fun state message hmessage =>
      image.ordered_handle_withChoiceTimeouts select state message hmessage)
    (fun state command => image.ordered_environmentStep_withChoiceTimeouts
      select state command) players environment ?_ schedule execution hsafe
  intro current who payload hsupported serial
  cases payload with
  | expireChoice address => exact False.elim (hsubmit current who address hsupported)
  | _ => trivial

/-- Enabling both timeout families preserves the ordered reference law when
neither new request is initially retained or submitted. -/
theorem ordered_runPolicies_withTimeouts (image : ApplicationImage P L)
    (binding : (code : BindingCode P L) → Option (PublicFallbackCode L code.ty))
    (choice : (code : PublicChoiceCode P L) →
      Option (PublicFallbackCode L code.guard.ty))
    (players : P → image.application.PlayerPolicy)
    (environment : image.application.EnvironmentPolicy)
    (hbinding : ∀ (execution : image.application.PolicyExecution) (who : P)
      (address : Nat), .submit (.expireBinding address) ∉
        (players who (execution.principalHistory who)
          (MessageApplication.State.observe image.application execution.native who)).support)
    (hchoice : ∀ (execution : image.application.PolicyExecution) (who : P)
      (address : Nat), .submit (.expireChoice address) ∉
        (players who (execution.principalHistory who)
          (MessageApplication.State.observe image.application execution.native who)).support)
    (schedule : List (@Invocation P)) (execution : image.application.PolicyExecution)
    (hsafeBinding : execution.native.pool.Satisfies
      (fun message => message.payload.NotBindingExpiry))
    (hsafeChoice : execution.native.pool.Satisfies
      (fun message => message.payload.NotChoiceExpiry)) :
    ((image.withBindingTimeouts binding).withChoiceTimeouts choice).orderedApplication.runPolicies
        players environment schedule execution =
      image.orderedApplication.runPolicies players environment schedule execution := by
  rw [(image.withBindingTimeouts binding).ordered_runPolicies_withChoiceTimeouts choice
    players environment hchoice schedule execution hsafeChoice]
  exact image.ordered_runPolicies_withBindingTimeouts binding players environment
    hbinding schedule execution hsafeBinding

end Vegas.ApplicationImage

/-- info: 'Vegas.ApplicationImage.ordered_runPolicies_withBindingTimeouts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_runPolicies_withBindingTimeouts

/-- info: 'Vegas.ApplicationImage.ordered_runPolicies_withChoiceTimeouts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_runPolicies_withChoiceTimeouts

/-- info: 'Vegas.ApplicationImage.ordered_runPolicies_withTimeouts' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationImage.ordered_runPolicies_withTimeouts
