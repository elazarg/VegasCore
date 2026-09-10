/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPrivacy

/-! # Paired focal policy inputs for the windowed runtime -/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

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
