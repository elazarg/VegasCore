/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.CommunicationProtocol
import GameTheory.Protocol.BehavioralAssessment

/-! # Bounded communication and public phase accounting

For a base horizon `n` and a roster of length `r`, at most `n * (r + 1)`
transitions suffice. Communication cannot postpone the next game step
indefinitely. This bound is a semantic service restriction, not a consequence
of blockchain timeouts alone.
-/

noncomputable section

namespace Interaction.CommunicationInterface

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} {E : ExecutionProtocol Player} {M : InformationModel E}
  (channel : CommunicationInterface M)

theorem transition_accounting (roster : List Player) (before after : channel.State)
    (joint : ∀ who, Option (channel.Action who))
    (running : ¬ E.terminal before.history.state)
    (legal : IsLegalJoint (channel.active before) (channel.available before) joint)
    (reached : after ∈ (channel.transition roster before joint running legal).support) :
    after.history.trace.length * (roster.length + 1) + before.remaining.length =
      before.history.trace.length * (roster.length + 1) + after.remaining.length + 1 := by
  unfold transition at reached
  split at reached
  next pending =>
      simp only [gameTransition, FinDist.support_bindOnSupport, Set.mem_iUnion] at reached
      obtain ⟨target, realized, same⟩ := reached
      cases FinDist.mem_support_pure.mp same
      simp [advance, History.extend, Trace.length, pending, Nat.add_mul]
      omega
  next actor rest pending =>
      cases FinDist.mem_support_pure.mp reached
      simp [communicate, pending, Nat.add_assoc]

theorem history_accounting (roster : List Player) :
    ∀ {state} (trace : (channel.protocol roster).Trace state),
      trace.length + state.remaining.length =
        state.history.trace.length * (roster.length + 1) + roster.length
  | _, .start => by simp [protocol, initHistory, Trace.length]
  | _, .extend prior joint legal realized => by
      have earlier := history_accounting roster prior
      have step := channel.transition_accounting roster _ _ joint legal.1 legal.2 realized
      simp only [Trace.length]
      omega

theorem bounded (roster : List Player) (bound : Nat) (base : E.BoundedHorizon bound) :
    (channel.protocol roster).BoundedHorizon (bound * (roster.length + 1)) := by
  intro state trace enough
  apply base state.history.state state.history.trace
  have accounting := channel.history_accounting roster trace
  by_contra short
  have less : (state.history.trace.length + 1) * (roster.length + 1) ≤
      bound * (roster.length + 1) := Nat.mul_le_mul_right _ (by omega)
  simp only [Nat.add_mul, Nat.one_mul] at less
  omega

/-- The public phase and remaining roster determine elapsed semantic time.
Equal decision observations therefore cannot occur along one strict extension. -/
theorem decision_antichain (roster : List Player) :
    (channel.informationModel roster).DecisionInformationAntichain :=
  (channel.informationModel roster).decisionInformationAntichain_of_perfectRecall
    (channel.perfectRecall roster)

end Interaction.CommunicationInterface
