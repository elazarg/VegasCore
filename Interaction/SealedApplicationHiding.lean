/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Interaction.SealedApplication
import Interaction.SealedHiding
import Interaction.MessageApplicationPolicies

/-! # Adaptive hiding with public inclusion receipts

The protected owner's unopened values may differ, while its slot occupancy,
all wire traffic, public events, and receipts agree. Validation agrees on
safe traffic, including rejection, so receipt-observing adaptive policies
cannot distinguish the values before the owner is invoked again. Replay is
unrestricted. This is ideal-service hiding, not a cryptographic theorem or
a source-strategy backtranslation.
-/

noncomputable section

namespace Interaction.SealedProgram

open GameTheory.Math.Probability

universe uPrincipal uValue

variable {Principal : Type uPrincipal} {Value : Type uValue}
variable [DecidableEq Principal] [DecidableEq Value]
variable {program : SealedProgram Principal} {hiddenOwner : Principal}

/-- The native hiding invariant retains the shared runtime's public receipts. -/
structure ApplicationRelated (program : SealedProgram Principal) (hiddenOwner : Principal)
    (left right : (program.messageApplication (Value := Value)).State) : Prop where
  native : HidingRelated hiddenOwner (program.eraseReceipts left) (program.eraseReceipts right)
  receipts : left.receipts = right.receipts

variable {left right : (program.messageApplication (Value := Value)).State}

theorem ApplicationRelated.observe_eq (related : ApplicationRelated program hiddenOwner left right)
    (who : Principal) :
    MessageApplication.State.observe _ left who =
      MessageApplication.State.observe _ right who := by
  have hp := related.native.pool
  have he := related.native.events
  simp only [eraseReceipts] at hp he
  simp only [MessageApplication.State.observe, messageApplication, hp, he, related.receipts]

theorem ApplicationRelated.environmentView_eq
    (related : ApplicationRelated program hiddenOwner left right) :
    MessageApplication.State.environmentView _ left =
      MessageApplication.State.environmentView _ right := by
  have hp := related.native.pool
  have he := related.native.events
  simp only [eraseReceipts] at hp he
  simp only [MessageApplication.State.environmentView, messageApplication, hp, he, related.receipts]

private theorem eraseReceipts_includePending
    (program : SealedProgram Principal)
    (state : (program.messageApplication (Value := Value)).State) (id : MessageId Principal) :
    program.eraseReceipts ((program.messageApplication).includePending state id) =
      program.includePending (program.eraseReceipts state) id := by
  have h := program.step_eraseReceipts state (.include id)
  simp only [MessageApplication.step, FinDist.map_pure, nativeAction, step] at h
  apply FinDist.mem_support_pure.mp
  rw [← h]
  exact FinDist.mem_support_pure.mpr rfl

theorem ApplicationRelated.includePending
    (related : ApplicationRelated program hiddenOwner left right) (id : MessageId Principal) :
    ApplicationRelated program hiddenOwner
      ((program.messageApplication).includePending left id)
      ((program.messageApplication).includePending right id) := by
  refine ⟨?_, ?_⟩
  · rw [eraseReceipts_includePending, eraseReceipts_includePending]
    exact related.native.includePending program id
  · have hp : left.pool = right.pool := related.native.pool
    have he : left.application.events = right.application.events := related.native.events
    unfold MessageApplication.includePending MessagePool.includeApplication
    rw [hp]
    cases hincluded : right.pool.includePending id with
    | mk message pool =>
        cases message with
        | none => exact related.receipts
        | some message =>
            have hsafe : MessageSafe hiddenOwner message := by
              have hm : (right.pool.includePending id).message = some message :=
                congrArg (fun result => result.message) hincluded
              have hlookup : right.pool.lookup id = some message := by
                cases hlookup : right.pool.lookup id <;>
                  simp_all [MessagePool.includePending, MessagePool.Result.invalid]
              have hsafe : PoolSafe hiddenOwner right.pool := by
                rw [← hp]
                exact related.native.safe
              exact hsafe.1 message (List.mem_of_find?_eq_some hlookup)
            have hvalid := validateMessage?_eq_of_serviceAgreement program
              left.application.service right.application.service related.native.service
              right.application.events message hsafe
            simp only [messageApplication, he, hvalid]
            cases program.validateMessage? right.application.service
                right.application.events message <;> simp [related.receipts]

private theorem ApplicationRelated.step
    (related : ApplicationRelated program hiddenOwner left right)
    (action : (program.messageApplication (Value := Value)).Action)
    (allowed : AllowedBeforeDisclosure hiddenOwner (program.nativeAction action)) :
    ∃ nextLeft nextRight,
      (program.messageApplication).step left action = FinDist.pure nextLeft ∧
      (program.messageApplication).step right action = FinDist.pure nextRight ∧
      ApplicationRelated program hiddenOwner nextLeft nextRight := by
  cases action with
  | privateCommand who command =>
      exact ⟨_, _, rfl, rfl,
        ⟨related.native.register who command.down.1 command.down.2 allowed, related.receipts⟩⟩
  | submit who payload =>
      exact ⟨_, _, rfl, rfl, ⟨related.native.submit who payload allowed, related.receipts⟩⟩
  | replay who id =>
      exact ⟨_, _, rfl, rfl, ⟨related.native.replay who id, related.receipts⟩⟩
  | deliver who id =>
      exact ⟨_, _, rfl, rfl, ⟨related.native.deliver who id, related.receipts⟩⟩
  | «include» id => exact ⟨_, _, rfl, rfl, related.includePending id⟩
  | environment command => exact nomatch command.down

/-- Joint analyst record, including public receipts and every unprotected
principal's own history. It is not an extra input to any policy. -/
def applicationObservations (program : SealedProgram Principal) (hiddenOwner : Principal)
    (execution : (program.messageApplication (Value := Value)).PolicyExecution) :=
  (MessageApplication.State.environmentView _ execution.native,
    (fun who : { who : Principal // who ≠ hiddenOwner } => execution.principalHistory who),
    execution.environmentHistory)

structure ApplicationPolicyRelated (program : SealedProgram Principal) (hiddenOwner : Principal)
    (left right : (program.messageApplication (Value := Value)).PolicyExecution) : Prop where
  native : ApplicationRelated program hiddenOwner left.native right.native
  principalHistory : ∀ who, who ≠ hiddenOwner →
    left.principalHistory who = right.principalHistory who
  environmentHistory : left.environmentHistory = right.environmentHistory

variable {first second : (program.messageApplication (Value := Value)).PolicyExecution}

theorem ApplicationPolicyRelated.observations_eq
    (related : ApplicationPolicyRelated program hiddenOwner first second) :
    program.applicationObservations hiddenOwner first =
      program.applicationObservations hiddenOwner second := by
  unfold applicationObservations
  refine Prod.ext related.native.environmentView_eq (Prod.ext ?_ related.environmentHistory)
  funext who
  exact related.principalHistory who who.property

theorem ApplicationPolicyRelated.initial
    (related : ApplicationRelated program hiddenOwner left right) :
    ApplicationPolicyRelated program hiddenOwner
      (MessageApplication.PolicyExecution.initial _ left)
      (MessageApplication.PolicyExecution.initial _ right) :=
  ⟨related, fun _ _ => rfl, rfl⟩

private theorem ApplicationPolicyRelated.advance
    (related : ApplicationPolicyRelated program hiddenOwner first second)
    (action : Option (program.messageApplication (Value := Value)).Action)
    (allowed : ∀ a, action = some a →
      AllowedBeforeDisclosure hiddenOwner (program.nativeAction a)) :
    ∃ nextLeft nextRight,
      (program.messageApplication).advance first action = FinDist.pure nextLeft ∧
      (program.messageApplication).advance second action = FinDist.pure nextRight ∧
      ApplicationRelated program hiddenOwner nextLeft.1 nextRight.1 := by
  cases action with
  | none => exact ⟨_, _, rfl, rfl, related.native⟩
  | some action =>
      obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.native.step action (allowed _ rfl)
      refine ⟨(nextLeft, first.nativeTrace ++ [action]),
        (nextRight, second.nativeTrace ++ [action]), ?_, ?_, hrelated⟩
      · simp only [MessageApplication.advance, hl, FinDist.pure_bind]
      · simp only [MessageApplication.advance, hr, FinDist.pure_bind]

private theorem ApplicationPolicyRelated.playerStep
    (related : ApplicationPolicyRelated program hiddenOwner first second)
    (who : Principal) (hne : who ≠ hiddenOwner)
    (command : (program.messageApplication (Value := Value)).PlayerCommand) :
    ∃ nextLeft nextRight,
      (program.messageApplication).playerStep who first command = FinDist.pure nextLeft ∧
      (program.messageApplication).playerStep who second command = FinDist.pure nextRight ∧
      ApplicationPolicyRelated program hiddenOwner nextLeft nextRight := by
  obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.advance
    (command.toAction _ who) (by
      intro action ha
      cases command with
      | privateCommand => cases ha; exact hne
      | submit => cases ha; exact hne
      | replay => cases ha; trivial
      | wait => cases ha)
  refine ⟨{ first with
      native := nextLeft.1
      nativeTrace := nextLeft.2
      principalHistory := fun other =>
        if other = who then first.principalHistory who ++
          [⟨MessageApplication.State.observe _ first.native who, command⟩]
        else first.principalHistory other },
    { second with
      native := nextRight.1
      nativeTrace := nextRight.2
      principalHistory := fun other =>
        if other = who then second.principalHistory who ++
          [⟨MessageApplication.State.observe _ second.native who, command⟩]
        else second.principalHistory other }, ?_, ?_, hrelated, ?_, related.environmentHistory⟩
  · simp only [MessageApplication.playerStep, hl, FinDist.pure_bind]
  · simp only [MessageApplication.playerStep, hr, FinDist.pure_bind]
  · intro other hother
    by_cases heq : other = who
    · subst other
      simp only [if_pos, related.principalHistory who hne, related.native.observe_eq who]
    · simpa only [if_neg heq] using related.principalHistory other hother

private theorem ApplicationPolicyRelated.environmentStep
    (related : ApplicationPolicyRelated program hiddenOwner first second)
    (command : (program.messageApplication (Value := Value)).EnvironmentPolicyCommand) :
    ∃ nextLeft nextRight,
      (program.messageApplication).environmentPolicyStep first command = FinDist.pure nextLeft ∧
      (program.messageApplication).environmentPolicyStep second command = FinDist.pure nextRight ∧
      ApplicationPolicyRelated program hiddenOwner nextLeft nextRight := by
  obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.advance command.toAction (by
    intro action ha
    cases command with
    | application command => exact nomatch command.down
    | deliver | «include» => cases ha; trivial
    | wait => cases ha)
  refine ⟨{ first with
      native := nextLeft.1
      nativeTrace := nextLeft.2
      environmentHistory := first.environmentHistory ++
        [⟨MessageApplication.State.environmentView _ first.native, command⟩] },
    { second with
      native := nextRight.1
      nativeTrace := nextRight.2
      environmentHistory := second.environmentHistory ++
        [⟨MessageApplication.State.environmentView _ second.native, command⟩] },
    ?_, ?_, hrelated, related.principalHistory, ?_⟩
  · simp only [MessageApplication.environmentPolicyStep, hl, FinDist.pure_bind]
  · simp only [MessageApplication.environmentPolicyStep, hr, FinDist.pure_bind]
  · simp only [related.environmentHistory, related.native.environmentView_eq]

/-- The full receipt-bearing observation law is independent of protected
values under arbitrary adaptive policies and replay, for every finite schedule
that does not invoke the protected owner. -/
theorem runApplicationPolicies_hiding
    (players : Principal → (program.messageApplication (Value := Value)).PlayerPolicy)
    (environment : (program.messageApplication (Value := Value)).EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Principal))
    (related : ApplicationPolicyRelated program hiddenOwner first second)
    (hschedule : ∀ who, MessageApplication.Invocation.player who ∈ schedule → who ≠ hiddenOwner) :
    ((program.messageApplication).runPolicies players environment schedule first).map
        (program.applicationObservations hiddenOwner) =
      ((program.messageApplication).runPolicies players environment schedule second).map
        (program.applicationObservations hiddenOwner) := by
  induction schedule generalizing first second with
  | nil => simp only [MessageApplication.runPolicies, FinDist.map_pure, related.observations_eq]
  | cons invocation rest ih =>
      have hrest : ∀ who, MessageApplication.Invocation.player who ∈ rest → who ≠ hiddenOwner :=
        fun who hmem => hschedule who (List.mem_cons_of_mem invocation hmem)
      cases invocation with
      | player who =>
          have hwho := hschedule who (List.mem_cons_self ..)
          simp only [MessageApplication.runPolicies, MessageApplication.invoke,
            FinDist.map_bind, FinDist.bind_bind, related.principalHistory who hwho,
            related.native.observe_eq who]
          apply FinDist.bind_congr
          intro command _
          obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.playerStep who hwho command
          simp only [hl, hr, FinDist.pure_bind]
          exact ih hrelated hrest
      | environment =>
          simp only [MessageApplication.runPolicies, MessageApplication.invoke,
            FinDist.map_bind, FinDist.bind_bind, related.environmentHistory,
            related.native.environmentView_eq]
          apply FinDist.bind_congr
          intro command _
          obtain ⟨nextLeft, nextRight, hl, hr, hrelated⟩ := related.environmentStep command
          simp only [hl, hr, FinDist.pure_bind]
          exact ih hrelated hrest

/-- info: 'Interaction.SealedProgram.runApplicationPolicies_hiding' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms runApplicationPolicies_hiding

end Interaction.SealedProgram
