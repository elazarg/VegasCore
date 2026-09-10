/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPrivacy

/-! # Paired focal policy inputs for the windowed runtime -/

noncomputable section

namespace Vegas

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace WindowedApplication

/-- The runtime state retained by a focal player's policy input. Other
principal histories, the native trace, and nonfocal private tables are
deliberately unconstrained. -/
structure PolicyAgreement (runtime : WindowedApplication P L) (who : P)
    (left right : runtime.application.PolicyExecution) : Prop where
  state : left.native.application.AgreesFor who right.native.application
  pool : left.native.pool = right.native.pool
  receipts : left.native.receipts = right.native.receipts
  history : left.principalHistory who = right.principalHistory who

namespace PolicyAgreement

variable {runtime : WindowedApplication P L} {who : P}
  {left right : runtime.application.PolicyExecution}

/-- Related executions supply exactly the same native input to the focal raw
policy, without equating hidden application state. -/
theorem input_eq (h : PolicyAgreement runtime who left right) :
    (left.principalHistory who,
      State.observe runtime.application left.native who) =
    (right.principalHistory who,
      State.observe runtime.application right.native who) := by
  apply Prod.ext h.history
  simp only [State.observe, WindowedApplication.application, h.pool, h.receipts,
    h.state.base.memory, h.state.active]

/-- A fixed pure focal policy therefore chooses the same command in related
executions. -/
theorem pure_command_eq (h : PolicyAgreement runtime who left right)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand) :
    command (left.principalHistory who) (State.observe runtime.application left.native who) =
      command (right.principalHistory who)
        (State.observe runtime.application right.native who) := by
  congr 1
  · exact congrArg Prod.fst h.input_eq
  · exact congrArg Prod.snd h.input_eq

/-- Executing the same focal command preserves the precise policy-input
relation. This includes replay: equal message pools select the same retained
original message, so rebroadcasting does not change its author. -/
theorem playerStep (h : PolicyAgreement runtime who left right)
    (command : runtime.application.PlayerCommand)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.playerStep who left command).support)
    (hright : nextRight ∈ (runtime.application.playerStep who right command).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  have hview : State.observe runtime.application left.native who =
      State.observe runtime.application right.native who :=
    congrArg Prod.snd h.input_eq
  cases command with
  | privateCommand privateCommand =>
      cases privateCommand with
      | register slot value =>
          simp only [MessageApplication.playerStep, MessageApplication.advance,
            PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
            FinDist.mem_support_pure] at hleft hright
          subst nextLeft
          subst nextRight
          refine ⟨⟨h.state.base.register slot value, h.state.active⟩,
            h.pool, h.receipts, ?_⟩
          simp only [if_pos, h.history, hview]
  | submit payload =>
      simp only [MessageApplication.playerStep, MessageApplication.advance,
        PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hleft hright
      subst nextLeft
      subst nextRight
      refine ⟨h.state, ?_, h.receipts, ?_⟩
      · simp only [MessagePool.submit, h.pool]
      · simp only [if_pos, h.history, hview]
  | replay id =>
      simp only [MessageApplication.playerStep, MessageApplication.advance,
        PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
        FinDist.mem_support_pure] at hleft hright
      subst nextLeft
      subst nextRight
      refine ⟨h.state, ?_, h.receipts, ?_⟩
      · rw [h.pool]
      · simp only [if_pos, h.history, hview]
  | wait =>
      simp only [MessageApplication.playerStep, MessageApplication.advance,
        PlayerCommand.toAction, FinDist.pure_bind, FinDist.mem_support_pure] at hleft hright
      subst nextLeft
      subst nextRight
      exact ⟨h.state, h.pool, h.receipts, by simp only [if_pos, h.history, hview]⟩

/-- A fixed pure raw focal policy selects the same command from the two actual
histories and observations. Consequently, any supported synchronized focal
invocations preserve policy agreement. The surrounding player rosters and
environment policies may differ away from the focal coordinate. -/
theorem invoke_player_pure (h : PolicyAgreement runtime who left right)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (leftPlayers rightPlayers : P → runtime.application.PlayerPolicy)
    (leftEnvironment rightEnvironment : runtime.application.EnvironmentPolicy)
    (hleftPolicy : leftPlayers who = fun history view => FinDist.pure (command history view))
    (hrightPolicy : rightPlayers who = fun history view => FinDist.pure (command history view))
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.application.invoke leftPlayers leftEnvironment left (.player who)).support)
    (hright : nextRight ∈
      (runtime.application.invoke rightPlayers rightEnvironment right (.player who)).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  have hcommand := h.pure_command_eq command
  simp only [MessageApplication.invoke, hleftPolicy, hrightPolicy,
    FinDist.pure_bind] at hleft hright
  rw [hcommand] at hleft
  exact h.playerStep _ nextLeft nextRight hleft hright

/-- Different private registrations by another actor preserve the focal
policy input. Sent-history entries record the actual distinct commands only
for that other actor. -/
theorem playerStep_register_other (h : PolicyAgreement runtime who left right)
    (actor : P) (hother : actor ≠ who) (leftSlot rightSlot : Nat)
    (leftValue rightValue : TypedValue L)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.playerStep actor left
      (.privateCommand (.register leftSlot leftValue))).support)
    (hright : nextRight ∈ (runtime.application.playerStep actor right
      (.privateCommand (.register rightSlot rightValue))).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  refine ⟨⟨h.state.base.register_other actor hother leftSlot rightSlot
    leftValue rightValue, h.state.active⟩, h.pool, h.receipts, ?_⟩
  simp only [if_neg (Ne.symm hother), h.history]

/-- A nonfocal wait records only the other actor's local entry. -/
theorem playerStep_wait_other (h : PolicyAgreement runtime who left right)
    (actor : P) (hother : actor ≠ who)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.playerStep actor left .wait).support)
    (hright : nextRight ∈ (runtime.application.playerStep actor right .wait).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, FinDist.pure_bind, FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  exact ⟨h.state, h.pool, h.receipts, by simp [Ne.symm hother, h.history]⟩

/-- Equal nonfocal submissions preserve the focal input. The message-pool
serial and payload are equal because the preceding pools agree; only the
other actor's local history is extended. -/
theorem playerStep_submit_other (h : PolicyAgreement runtime who left right)
    (actor : P) (hother : actor ≠ who) (payload : ApplicationImage.Payload P L)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.application.playerStep actor left (.submit payload)).support)
    (hright : nextRight ∈
      (runtime.application.playerStep actor right (.submit payload)).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  simp only [MessageApplication.playerStep, MessageApplication.advance,
    PlayerCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  refine ⟨h.state, ?_, h.receipts, ?_⟩
  · simp [MessagePool.submit, h.pool]
  · simp [Ne.symm hother, h.history]

/-- Synchronized environment waits preserve focal policy agreement. -/
theorem environmentPolicyStep_wait (h : PolicyAgreement runtime who left right)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.environmentPolicyStep left .wait).support)
    (hright : nextRight ∈ (runtime.application.environmentPolicyStep right .wait).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  exact ⟨h.state, h.pool, h.receipts, h.history⟩

/-- Advancing both window clocks by the same public value preserves focal
policy agreement. -/
theorem environmentPolicyStep_advance (h : PolicyAgreement runtime who left right)
    (clock : Nat) (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.environmentPolicyStep left
      (.application (.advance clock))).support)
    (hright : nextRight ∈ (runtime.application.environmentPolicyStep right
      (.application (.advance clock))).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step,
    WindowedApplication.application, WindowedApplication.environmentStep,
    FinDist.map_pure, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  exact ⟨⟨h.state.base.advance clock, h.state.active⟩,
    h.pool, h.receipts, h.history⟩

/-- Actual inclusion preserves the focal policy input when only focal-authored
packets may query a private opening verifier. Other packet forms, including
another principal's opaque binding and expiry, need no authorship restriction. -/
theorem environmentPolicyStep_include (h : PolicyAgreement runtime who left right)
    (id : MessageId P)
    (hauthor : ∀ message, left.native.pool.lookup id = some message →
      message.payload.OpensCommitment → message.sender = who)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (hright : nextRight ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  obtain ⟨hstate, hpool, hreceipts⟩ := runtime.includePending_agrees who left.native right.native
    h.state h.pool h.receipts id hauthor
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  exact ⟨hstate, hpool, hreceipts, h.history⟩

/-- Recipient-local delivery exposes the actual packet without running the
application handler. Equal pools therefore give equal resulting policy inputs,
including when the delivered message was authored by another principal. -/
theorem environmentPolicyStep_deliver (h : PolicyAgreement runtime who left right)
    (recipient : P) (id : MessageId P)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.application.environmentPolicyStep left (.deliver recipient id)).support)
    (hright : nextRight ∈
      (runtime.application.environmentPolicyStep right (.deliver recipient id)).support) :
    PolicyAgreement runtime who nextLeft nextRight := by
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  exact ⟨h.state, by rw [h.pool], h.receipts, h.history⟩

end PolicyAgreement

/-- Different registrations by another actor preserve the focal native state
relation; the registered slots and values may differ on the two sides. -/
theorem State.AgreesFor.privateRegister_other
    {runtime : WindowedApplication P L} {who actor : P} (hne : actor ≠ who)
    {left right : State P L} (h : left.AgreesFor who right)
    (leftSlot rightSlot : Nat) (leftValue rightValue : TypedValue L) :
    (runtime.application.privateStep left actor (.register leftSlot leftValue)).AgreesFor who
      (runtime.application.privateStep right actor (.register rightSlot rightValue)) := by
  exact ⟨h.base.register_other actor hne leftSlot rightSlot leftValue rightValue, h.active⟩

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.playerStep' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.playerStep

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.invoke_player_pure' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.invoke_player_pure

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_include' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_include

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_deliver' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_deliver
