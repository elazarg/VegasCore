/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedDeliveryPhase
import Vegas.Compile.WindowedReactionPrivacy
import Vegas.Compile.WindowedOwnedPlayers

/-! # Information agreement through the concrete delivery phase

This is a local bridge from the actual delivery-service environment policy to
the generic delivery/reaction agreement theorem.  All prefix selection and
visited-policy facts remain explicit; no source-wide correspondence is claimed.
-/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}

/-- Equal public application state and equal environment-history length induce
the same delivery-service environment policy. The delivery command reads only
the erased public observation; pending packet contents remain in the shared
pool and are not inspected by the scheduler. -/
theorem deliveryBlockEnvironment_eq
    {left right : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (roster recipients : List P)
    (hlength : left.environmentHistory.length = right.environmentHistory.length) :
    runtime.deliveryBlockEnvironment roster recipients left.environmentHistory
        (State.environmentView runtime.application left.native) =
      runtime.deliveryBlockEnvironment roster recipients right.environmentHistory
        (State.environmentView runtime.application right.native) := by
  have hview :
      State.environmentView runtime.application left.native =
        State.environmentView runtime.application right.native := by
    simp only [State.environmentView,
      WindowedApplication.application, agreement.pool, agreement.receipts,
      agreement.state.base.memory, agreement.state.active]
  simp only [WindowedApplication.deliveryBlockEnvironment, hlength, hview]

/-- A nonfocal reference player in a focal-owned delivery block is
independent of the two agreeing private bases. Ordinary and reaction slots
wait; the relay slot submits the same publicly selected expiry payload. -/
theorem deliveryBlockPlayer_other_eq
    {left right : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (actor : P) (hactor : actor ≠ focal)
    (leftBase rightBase : runtime.application.PlayerPolicy)
    (instruction : ApplicationInstruction P L)
    (howner : instruction.submitter = some focal)
    (hlength : (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hindex : runtime.image.instructions[(left.principalHistory actor).length / 4]? =
      some instruction)
    (hslot : (left.principalHistory actor).length % 4 = 0 ∨
      (left.principalHistory actor).length % 4 = 1 ∨
      (left.principalHistory actor).length % 4 = 2 ∨
      (left.principalHistory actor).length % 4 = 3) :
    runtime.deliveryBlockPlayer actor leftBase (left.principalHistory actor)
        (State.observe runtime.application left.native actor) =
      runtime.deliveryBlockPlayer actor rightBase (right.principalHistory actor)
        (State.observe runtime.application right.native actor) := by
  have hrightIndex : runtime.image.instructions[(right.principalHistory actor).length / 4]? =
      some instruction := by rwa [← hlength]
  have hview := agreement.observe_eq actor
  simp only [WindowedApplication.deliveryBlockPlayer, hindex, hrightIndex]
  rw [hview]
  by_cases hactive : runtime.image.activeAddress?
      (State.observe runtime.application right.native actor).application.1 =
      some instruction.address
  · simp only [hactive, ↓reduceIte]
    rcases hslot with hzero | hone | htwo | hthree
    · have hrightSlot : (right.principalHistory actor).length % 4 = 0 := by
        rwa [← hlength]
      simp only [hzero, hrightSlot, howner, Option.some.injEq, Ne.symm hactor,
        ↓reduceIte]
    · have hrightSlot : (right.principalHistory actor).length % 4 = 1 := by
        rwa [← hlength]
      simp only [hone, hrightSlot, howner, Option.some.injEq, Ne.symm hactor,
        ↓reduceIte]
    · have hrightSlot : (right.principalHistory actor).length % 4 = 2 := by
        rwa [← hlength]
      simp only [htwo, hrightSlot]
    · have hrightSlot : (right.principalHistory actor).length % 4 = 3 := by
        rwa [← hlength]
      simp only [hthree, hrightSlot]
  · simp only [hactive, ↓reduceIte]

/-- Executing the concrete delivery slots for the same selected pending
identifier, followed by the roster reaction round, preserves focal agreement. -/
theorem deliveryPrefix_then_roster_reactions
    {left right leftFinal rightFinal : runtime.application.PolicyExecution}
    (agreement : PolicyAgreement runtime focal left right)
    (players : P → runtime.application.PlayerPolicy)
    (command : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (hfocal : players focal = fun history view => FinDist.pure (command history view))
    (roster recipients : List P) (blockIndex : Nat)
    (instruction : ApplicationInstruction P L) (id : MessageId P)
    (hleftLength : left.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hrightLength : right.environmentHistory.length =
      blockIndex * (recipients.length + roster.length + 2))
    (hindex : runtime.image.instructions[blockIndex]? = some instruction)
    (hleftActive : runtime.image.activeAddress? left.native.application.base.memory =
      some instruction.address)
    (hrightActive : runtime.image.activeAddress? right.native.application.base.memory =
      some instruction.address)
    (hleftInclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction
        (runtime.eraseEnvironmentView
          (State.environmentView runtime.application left.native))) = .include id)
    (hrightInclude : runtime.liftEnvironmentCommand
      (runtime.image.serviceCommand instruction
        (runtime.eraseEnvironmentView
          (State.environmentView runtime.application right.native))) = .include id)
    (starts limits : P → Nat)
    (hothers : ∀ actor history view, actor ≠ focal →
      starts actor ≤ history.length → history.length < limits actor →
      players actor history view = FinDist.pure .wait)
    (hleftRange : ∀ actor,
      starts actor ≤ (left.principalHistory actor).length ∧
        (left.principalHistory actor).length +
          (roster.map Invocation.player).countP (fun call => match call with
            | .player who => decide (who = actor)
            | .environment => false) = limits actor)
    (hrightRange : ∀ actor,
      starts actor ≤ (right.principalHistory actor).length ∧
        (right.principalHistory actor).length +
          (roster.map Invocation.player).countP (fun call => match call with
            | .player who => decide (who = actor)
            | .environment => false) = limits actor)
    (hleft : leftFinal ∈
      ((runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients)
        (recipients.map fun _ => (Invocation.environment : @Invocation P)) left).bind
          fun delivered => runtime.application.runPolicies players
            (runtime.deliveryBlockEnvironment roster recipients)
            (roster.map Invocation.player) delivered).support)
    (hright : rightFinal ∈
      ((runtime.application.runPolicies players
        (runtime.deliveryBlockEnvironment roster recipients)
        (recipients.map fun _ => (Invocation.environment : @Invocation P)) right).bind
          fun delivered => runtime.application.runPolicies players
            (runtime.deliveryBlockEnvironment roster recipients)
            (roster.map Invocation.player) delivered).support) :
    PolicyAgreement runtime focal leftFinal rightFinal := by
  rw [runtime.runPolicies_deliveryPrefix players roster recipients blockIndex instruction id left
    hleftLength hindex hleftActive hleftInclude] at hleft
  rw [runtime.runPolicies_deliveryPrefix players roster recipients blockIndex instruction id right
    hrightLength hindex hrightActive hrightInclude] at hright
  exact agreement.deliveries_then_reactions id recipients command players
    (runtime.deliveryBlockEnvironment roster recipients) hfocal starts limits hothers
    (roster.map Invocation.player) (by simp) hleftRange hrightRange hleft hright

end Vegas.WindowedApplication.PolicyAgreement

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.deliveryPrefix_then_roster_reactions'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.deliveryPrefix_then_roster_reactions

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.deliveryBlockEnvironment_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.deliveryBlockEnvironment_eq

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.deliveryBlockPlayer_other_eq'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.deliveryBlockPlayer_other_eq
