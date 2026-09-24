/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactivePacketEvidence
import Interaction.ReactivePolicyInvariant

/-! # Once observed, carried evidence remains observable -/

noncomputable section

namespace Interaction.ReactiveApplication.PacketEvidence

open GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  (evidence : app.PacketEvidence)

theorem observed_respond (execution : app.Execution) (who actor : Principal)
    (action : app.Action) (fact : evidence.Fact)
    (seen : fact ∈ evidence.observe (execution.observe app who)) :
    fact ∈ evidence.observe ((execution.respond app actor action).observe app who) := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => exact seen
  | some transmission =>
      cases transmission with
      | submit material => exact seen
      | replay id =>
          cases found : (execution.network.known actor).find? (fun message => message.id = id) <;>
            simpa only [Execution.respond, MessageNetwork.replay, found,
              PacketEvidence.observe, Execution.observe, MessageNetwork.observe] using seen

theorem observed_environment (execution next : app.Execution) (who : Principal)
    (command : app.Command) (fact : evidence.Fact)
    (seen : fact ∈ evidence.observe (execution.observe app who))
    (reached : next ∈ (execution.environmentStep app command).support) :
    fact ∈ evidence.observe (next.observe app who) := by
  obtain ⟨message, member, decoded⟩ := List.mem_flatMap.mp seen
  refine List.mem_flatMap.mpr ⟨message, ?_, decoded⟩
  cases command with
  | wait =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      exact member
  | activate actor =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨selected, _, rfl⟩ := FinDist.support_map .. ▸ supported
      change message ∈ (execution.network.learn actor selected).leaked who ++
        (execution.network.learn actor selected).ledger
      change message ∈ execution.network.leaked who ++ execution.network.ledger at member
      by_cases same : who = actor
      · subst who
        simp only [MessageNetwork.learn, ↓reduceIte, List.mem_append] at member ⊢
        exact member.imp Or.inl id
      · simpa only [MessageNetwork.learn, ite_eq_right same] using member
  | «include» id =>
      simp only [Execution.environmentStep, FinDist.map_pure] at reached
      cases FinDist.mem_support_pure.mp reached
      cases found : execution.network.lookup id with
      | none =>
          simpa only [Execution.includePending, MessageNetwork.includePending, found,
            Execution.observe, MessageNetwork.observe] using member
      | some packet =>
          change message ∈ execution.network.leaked who ++ execution.network.ledger at member
          change message ∈ (execution.includePending app id).network.leaked who ++
            (execution.includePending app id).network.ledger
          simp only [Execution.includePending, MessageNetwork.includePending, found,
            List.mem_append] at member ⊢
          exact member.imp (fun h => h) Or.inl
  | application command =>
      obtain ⟨updated, supported, rfl⟩ := FinDist.support_map .. ▸ reached
      obtain ⟨_, _, rfl⟩ := FinDist.support_map .. ▸ supported
      exact member

theorem observed_policyInvariant (players : Principal → app.Policy) (who : Principal)
    (fact : evidence.Fact) : app.PolicyInvariant players
      (fun execution => fact ∈ evidence.observe (execution.observe app who)) where
  respond execution actor action seen _ :=
    evidence.observed_respond execution who actor action fact seen
  environment execution next command seen reached :=
    evidence.observed_environment execution next who command fact seen reached

end Interaction.ReactiveApplication.PacketEvidence
