/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveUniformService
import Interaction.ReactiveSelection

/-! # Authorization preserves the uniform response law

The public submission audit is unchanged during a response. Eligibility of
retained candidates is consequently fixed across every raw response. A response
either preserves the candidate set or inserts its newly allocated identifier.
This is a local selection theorem, not a theorem about subsequent service steps.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

theorem authorizedUniform_respond
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (who : Principal) (action : app.Action) :
    app.authorizedUniform condition (execution.respond app who action).environmentRecall
        ((execution.respond app who action).observeEnvironment app) eligible =
      MessageNetwork.uniformPending
        (execution.network.unpublished
          (app.authorizedEligibility condition execution.environmentRecall eligible))
        (execution.respond app who action).network.pending := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | submit material => rfl
      | replay id =>
          cases found : (execution.network.known who).find? (fun message => message.id = id) <;>
            simp only [Execution.respond, MessageNetwork.replay, found] <;> rfl

/-- Every raw response has one of two effects on the selection menu. -/
theorem authorizedUniform_response_eq
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished) (who : Principal) (action : app.Action) :
    app.authorizedUniform condition (execution.respond app who action).environmentRecall
        ((execution.respond app who action).observeEnvironment app) eligible =
      if app.submitsEligible (app.authorizedEligibility condition execution.environmentRecall
          eligible) execution who action then
        MessageNetwork.chooseUniform (insert (who, execution.network.nextSerial who)
          (MessageNetwork.eligibleIds (execution.network.unpublished
            (app.authorizedEligibility condition execution.environmentRecall eligible))
              execution.network.pending))
      else app.authorizedUniform condition execution.environmentRecall
        (execution.observeEnvironment app) eligible := by
  rw [app.authorizedUniform_respond]
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id =>
          change MessageNetwork.chooseUniform _ = MessageNetwork.chooseUniform _
          have same := congrArg MessageNetwork.chooseUniform
            (retained.replay_unpublished_ids
              (app.authorizedEligibility condition execution.environmentRecall eligible) who id)
          cases found : (execution.network.known who).find? (fun message => message.id = id)
          · simp only [Execution.respond, MessageNetwork.replay, found]
            rfl
          · simp only [MessageNetwork.replay, found] at same
            simp only [Execution.respond, MessageNetwork.replay, found]
            exact same
      | submit material =>
          change MessageNetwork.uniformPending _ (execution.network.pending ++ [_]) = _
          unfold MessageNetwork.uniformPending
          rw [MessageNetwork.eligibleIds_append]
          split <;> simp_all only [submitsEligible, MessageNetwork.submit, ↓reduceIte,
            Bool.false_eq_true, authorizedUniform, MessageNetwork.uniformPending]
          rfl

/-- A submitted candidate cannot increase any retained candidate's probability.
This includes unauthorized submissions, silence, and every replay. -/
theorem authorizedUniform_response_regular
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (eligible : Message Principal app.Payload → Bool) (execution : app.Execution)
    (retained : execution.network.PendingOrPublished)
    (serials : execution.network.SerialsBeforeNext) (who : Principal) (action : app.Action) :
    (app.authorizedUniform condition execution.environmentRecall
      (execution.observeEnvironment app) eligible).RegularAt
        (app.authorizedUniform condition (execution.respond app who action).environmentRecall
          ((execution.respond app who action).observeEnvironment app) eligible)
        (some (who, execution.network.nextSerial who)) := by
  rw [app.authorizedUniform_response_eq condition eligible execution retained who action]
  split
  · exact MessageNetwork.chooseUniform_regular_insert _ _ (serials.next_not_eligible _ who)
  · exact FinDist.RegularAt.refl _ _

theorem authorizedUniform_history_regular
    (condition : app.PublicObservation → Message Principal app.Payload → Prop)
    (eligible : Message Principal app.Payload → Bool)
    (initial : FinDist app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (control : app.Control)
    (trace : (app.protocol initial horizon scheduler).Trace (some control))
    (who : Principal) (action : app.Action) :
    (app.authorizedUniform condition control.execution.environmentRecall
      (control.execution.observeEnvironment app) eligible).RegularAt
        (app.authorizedUniform condition
          (control.execution.respond app who action).environmentRecall
          ((control.execution.respond app who action).observeEnvironment app) eligible)
        (some (who, control.execution.network.nextSerial who)) :=
  app.authorizedUniform_response_regular condition eligible control.execution
    (app.pendingOrPublished_history scheduler initial horizon trace)
    (app.serialsBeforeNext_history scheduler initial horizon trace) who action

end Interaction.ReactiveApplication
