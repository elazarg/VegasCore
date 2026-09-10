/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.ApplicationPolicyFreshness
import Vegas.Compile.ApplicationDeadlineIndependence

/-! # Cache neutrality of idle and expiry commands

An expiry relay records a real submission in its principal's history.  These
commands, and ordinary waits, lie outside every generated source-choice cache.
They therefore preserve both future-cache freshness and the private
registration fallback used by owner-local readout.  No history is erased or
reconstructed by these lemmas.
-/

noncomputable section

namespace Vegas

open EventGraph ToEventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ApplicationImage

/-- Commands inserted by an idle expiry relay.  This is a command/history
classification, not a claim that an expiry is ready or will be included. -/
def IdleOrExpiryCommand (image : ApplicationImage P L)
    (command : image.application.PlayerCommand) : Prop :=
  match command with
  | .wait => True
  | .submit payload => ¬payload.DeadlineIndependent
  | .privateCommand _ | .replay _ => False

@[simp] theorem idleOrExpiryCommand_wait (image : ApplicationImage P L) :
    image.IdleOrExpiryCommand .wait := trivial

theorem idleOrExpiryCommand_submit (image : ApplicationImage P L)
    (payload : Payload P L) (hdependent : ¬payload.DeadlineIndependent) :
    image.IdleOrExpiryCommand (.submit payload) := hdependent

end ApplicationImage

namespace ApplicationInstruction

/-- Idle and expiry submissions cannot populate any generated instruction's
private-registration or voluntary-submission cache. -/
theorem idleOrExpiry_rejectsCommand
    (image : ApplicationImage P L) (instruction : ApplicationInstruction P L)
    (who : P) (command : image.application.PlayerCommand)
    (hcommand : image.IdleOrExpiryCommand command) :
    instruction.RejectsCommand image who command := by
  cases command with
  | privateCommand command | replay id => contradiction
  | wait =>
      cases instruction <;> simp [ApplicationInstruction.RejectsCommand]
  | submit payload =>
      cases payload with
      | choice address value | binding address value | malformed value =>
          exact False.elim (hcommand trivial)
      | expireChoice address | expireBinding address =>
          cases instruction <;>
            simp [ApplicationInstruction.RejectsCommand,
              ConditionalCode.commandEncoding, ChoiceEncoding.submission,
              ChoiceEncoding.trans,
              BindingCode.encoding, ApplicationImage.choiceEncoding,
              ApplicationImage.conditionalTransport]
      | conditional address payload =>
          cases payload with
          | opening handle value | decline | cleartext value | malformed =>
              exact False.elim (hcommand trivial)
          | expire =>
              cases instruction with
              | sample code => trivial
              | bind code =>
                  intro _
                  constructor <;> rfl
              | publicChoice code =>
                  intro _
                  rfl
              | conditional code =>
                  intro _ disposition
                  cases disposition <;>
                    simp [ConditionalCode.commandEncoding, ChoiceEncoding.submission,
                      ChoiceEncoding.trans, ChoiceEncoding.reindex,
                      ChoiceEncoding.atEndpoint, ApplicationImage.conditionalTransport,
                      ConditionalPublication.addressedChoiceEncoding,
                      ConditionalPublication.choiceEncoding,
                      ConditionalPublication.addressedDefaultChoiceEncoding,
                      ConditionalPublication.defaultChoiceEncoding]

end ApplicationInstruction

namespace ApplicationImage

/-- Recording an idle or expiry command leaves every slot-indexed private
registration cache unchanged. -/
theorem registrationCache_append_idleOrExpiry (image : ApplicationImage P L)
    (slot : Nat) (history : List image.application.PlayerEntry)
    (view : image.application.View) (command : image.application.PlayerCommand)
    (hcommand : image.IdleOrExpiryCommand command) :
    image.registrationCache slot (history ++ [⟨view, command⟩]) =
      image.registrationCache slot history := by
  unfold registrationCache
  apply ChoiceEncoding.cachedValue_append_unrecognized_eq
  cases command with
  | privateCommand command | replay id => contradiction
  | wait | submit payload => rfl

/-- Owner-local reconstruction retains the same store after a real idle or
expiry history entry.  Public memory is fixed by the statement. -/
theorem ownerReadStore_append_idleOrExpiry (image : ApplicationImage P L)
    (who : P) (history : List image.application.PlayerEntry)
    (view : image.application.View) (command : image.application.PlayerCommand)
    (memory : Memory P L) (hcommand : image.IdleOrExpiryCommand command) :
    image.ownerReadStore who (history ++ [⟨view, command⟩]) memory =
      image.ownerReadStore who history memory := by
  funext field
  simp only [ownerReadStore]
  rw [image.registrationCache_append_idleOrExpiry field history view command hcommand]

/-- A relay history entry cannot change the executable owner readout at a
fixed current public view. -/
theorem ownerReadout?_append_idleOrExpiry (image : ApplicationImage P L)
    (who : P) (refs : Finset (FieldRef L))
    (history : List image.application.PlayerEntry)
    (entryView view : image.application.View)
    (command : image.application.PlayerCommand)
    (hcommand : image.IdleOrExpiryCommand command) :
    image.ownerReadout? who refs (history ++ [⟨entryView, command⟩]) view =
      image.ownerReadout? who refs history view := by
  unfold ownerReadout?
  rw [image.ownerReadStore_append_idleOrExpiry who history entryView command
    view.application hcommand]

end ApplicationImage

namespace ApplicationPlan

/-- An actual idle or expiry player step preserves every cache in a remaining
generated plan. -/
theorem remainingCachesEmpty_playerStep_idleOrExpiry
    {Γ : VCtx P L} {pending : Finset VarId} {prog : VegasCore P L Γ}
    {accounted : CommitmentAccounting pending prog} {fresh : FreshBindings prog}
    {state : BuildState P L Γ}
    (image : ApplicationImage P L) (deadlineOf : Nat → Nat)
    (plan : ApplicationPlan accounted fresh state)
    (who : P) (execution next : image.application.PolicyExecution)
    (command : image.application.PlayerCommand)
    (hcommand : image.IdleOrExpiryCommand command)
    (hnext : next ∈ (image.application.playerStep who execution command).support)
    (hfresh : plan.RemainingCachesEmpty image deadlineOf execution) :
    plan.RemainingCachesEmpty image deadlineOf next := by
  apply plan.remainingCachesEmpty_playerStep image deadlineOf who execution command
    next hnext hfresh
  intro instruction _
  exact instruction.idleOrExpiry_rejectsCommand image who command hcommand

end ApplicationPlan

end Vegas

/-- info: 'Vegas.ApplicationInstruction.idleOrExpiry_rejectsCommand' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationInstruction.idleOrExpiry_rejectsCommand

/-- info: 'Vegas.ApplicationPlan.remainingCachesEmpty_playerStep_idleOrExpiry' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.ApplicationPlan.remainingCachesEmpty_playerStep_idleOrExpiry
