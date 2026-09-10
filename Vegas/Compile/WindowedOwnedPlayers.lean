/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockDeterminism
import Vegas.Compile.WindowedPolicyPrivacy

/-! # Paired player polls in a focal-owned block -/

noncomputable section

namespace Vegas.WindowedApplication

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace PolicyAgreement

variable {runtime : WindowedApplication P L} {focal : P}
  {left right : runtime.application.PolicyExecution}

/-- Agreement exposes the same public native observation to every actor.  Only
the focal actor additionally receives a related local history. -/
theorem observe_eq (agreement : PolicyAgreement runtime focal left right) (actor : P) :
    State.observe runtime.application left.native actor =
      State.observe runtime.application right.native actor := by
  simp only [State.observe, WindowedApplication.application, agreement.pool,
    agreement.receipts, agreement.state.base.memory, agreement.state.active]

/-- When an instruction is not owned by an actor, that actor's gated policy
has the same point-mass law in agreeing executions. Its arbitrary source
policy is unreachable: ordinary polls wait, while the relay poll depends only
on equal public memory and activation. -/
theorem blockPlayer_gated_eq
    (agreement : PolicyAgreement runtime focal left right)
    (actor : P)
    (leftBase rightBase : runtime.application.PlayerPolicy)
    (instruction : ApplicationInstruction P L)
    (hgate : instruction.submitter ≠ some actor)
    (hlength : (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hleftIndex : runtime.image.instructions[(left.principalHistory actor).length / 3]? =
      some instruction) :
    runtime.blockPlayer actor leftBase (left.principalHistory actor)
        (State.observe runtime.application left.native actor) =
      runtime.blockPlayer actor rightBase (right.principalHistory actor)
        (State.observe runtime.application right.native actor) := by
  have hview := agreement.observe_eq actor
  have hrightIndex : runtime.image.instructions[(right.principalHistory actor).length / 3]? =
      some instruction := by
    rwa [← hlength]
  simp only [blockPlayer, hleftIndex, hrightIndex]
  rw [hview]
  by_cases hactive : runtime.image.activeAddress?
      (State.observe runtime.application right.native actor).application.1 =
        some instruction.address
  · simp only [hactive, ↓reduceIte]
    by_cases hslot : (left.principalHistory actor).length % 3 < 2
    · have hrightSlot : (right.principalHistory actor).length % 3 < 2 := by
        rwa [← hlength]
      simp only [hslot, hrightSlot, hgate, ↓reduceIte]
    · have hrightSlot : ¬(right.principalHistory actor).length % 3 < 2 := by
        rwa [← hlength]
      simp only [hslot, hrightSlot, ↓reduceIte]
  · simp only [hactive, ↓reduceIte]

end PolicyAgreement

/-- When an instruction is not owned by an actor, the gated command is either
a wait or the publicly selected expiry payload. -/
theorem blockPlayer_gated_wait_or_submit
    (runtime : WindowedApplication P L) (actor : P)
    (base : runtime.application.PlayerPolicy)
    (history : List runtime.application.PlayerEntry) (view : runtime.application.View)
    (instruction : ApplicationInstruction P L)
    (hgate : instruction.submitter ≠ some actor)
    (hindex : runtime.image.instructions[history.length / 3]? = some instruction) :
    runtime.blockPlayer actor base history view = FinDist.pure .wait ∨
      ∃ payload, runtime.blockPlayer actor base history view = FinDist.pure (.submit payload) := by
  simp only [blockPlayer, hindex]
  split
  · split
    · exact Or.inl rfl
    · cases hdue : runtime.dueExpiry? view.application with
      | none => exact Or.inl (by simp [relayCommand])
      | some payload => exact Or.inr ⟨payload, by simp [relayCommand]⟩
  · exact Or.inl rfl

namespace PolicyAgreement

variable {runtime : WindowedApplication P L} {focal : P}
  {left right : runtime.application.PolicyExecution}

/-- A synchronized player invocation preserves the focal policy input when
every nonfocal actor is gated away from the current instruction. The focal
policy may inspect its complete native history and view, but is fixed and
pure. Other source policies are arbitrary because their command is replaced
by a public wait or expiry submission. -/
theorem invoke_player_gated
    (agreement : PolicyAgreement runtime focal left right)
    (actor : P)
    (replacement : List runtime.application.PlayerEntry → runtime.application.View →
      runtime.application.PlayerCommand)
    (base : P → runtime.application.PlayerPolicy)
    (players : P → runtime.application.PlayerPolicy)
    (hfocal : players focal = fun history view => FinDist.pure (replacement history view))
    (hothers : ∀ candidate, candidate ≠ focal →
      players candidate = runtime.blockPlayer candidate (base candidate))
    (leftEnvironment rightEnvironment : runtime.application.EnvironmentPolicy)
    (instruction : ApplicationInstruction P L)
    (hgate : actor ≠ focal → instruction.submitter ≠ some actor)
    (hlength : (left.principalHistory actor).length =
      (right.principalHistory actor).length)
    (hleftIndex : runtime.image.instructions[(left.principalHistory actor).length / 3]? =
      some instruction)
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈ (runtime.application.invoke players leftEnvironment left
      (.player actor)).support)
    (hright : nextRight ∈ (runtime.application.invoke players rightEnvironment right
      (.player actor)).support) :
    PolicyAgreement runtime focal nextLeft nextRight := by
  by_cases heq : actor = focal
  · subst actor
    exact agreement.invoke_player_pure replacement players players leftEnvironment
      rightEnvironment hfocal hfocal nextLeft nextRight hleft hright
  · have hgateActor := hgate heq
    have hpolicy := agreement.blockPlayer_gated_eq actor (base actor) (base actor)
      instruction hgateActor hlength hleftIndex
    have hleftGate := hothers actor heq
    rw [← hleftGate] at hpolicy
    rcases runtime.blockPlayer_gated_wait_or_submit actor (base actor)
      (left.principalHistory actor) (State.observe runtime.application left.native actor)
      instruction hgateActor hleftIndex with hwait | ⟨payload, hsubmit⟩
    · have hleftPolicy : players actor (left.principalHistory actor)
          (State.observe runtime.application left.native actor) = FinDist.pure .wait := by
        rw [hleftGate]
        exact hwait
      have hrightPolicy : players actor (right.principalHistory actor)
          (State.observe runtime.application right.native actor) = FinDist.pure .wait := by
        rw [← hpolicy]
        exact hleftPolicy
      simp only [MessageApplication.invoke, hleftPolicy, hrightPolicy,
        FinDist.pure_bind] at hleft hright
      exact agreement.playerStep_wait_other actor heq nextLeft nextRight hleft hright
    · have hleftPolicy : players actor (left.principalHistory actor)
          (State.observe runtime.application left.native actor) =
            FinDist.pure (.submit payload) := by
        rw [hleftGate]
        exact hsubmit
      have hrightPolicy : players actor (right.principalHistory actor)
          (State.observe runtime.application right.native actor) =
            FinDist.pure (.submit payload) := by
        rw [← hpolicy]
        exact hleftPolicy
      simp only [MessageApplication.invoke, hleftPolicy, hrightPolicy,
        FinDist.pure_bind] at hleft hright
      exact agreement.playerStep_submit_other actor heq payload nextLeft nextRight hleft hright

end PolicyAgreement

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.PolicyAgreement.invoke_player_gated' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.PolicyAgreement.invoke_player_gated
