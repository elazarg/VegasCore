/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDecisionWindowSettlement
import Vegas.Pending.ReactiveRevealSettlement

/-! # Padding an accepted decision window

Both Boolean decisions complete at protected inclusion. The following clock
ticks and actual expiry command preserve that completed record and its markers.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

theorem decisionWindow_expiry (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (opening : Option (Handle graph × Raw L))
    (initial : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (owned : ∀ candidate raw, opening = some (candidate, raw) → candidate.1 = owner)
    (roster : List Player) (selected : Fin (roster.count owner) × Bool)
    (valid : selected.2 = true → ∀ candidate raw, opening = some (candidate, raw) →
      initial.application.candidates.lookup candidate = .openable raw)
    (after : State graph)
    (accepted : (runtime.reactiveApplication leaks).handle initial.application
      (runtime.decisionEnvelope leaks owner event opening selected.2 initial) = some after)
    (settled : ¬after.config.cut.Ready event) (ticks : Nat)
    (network : runtime.NetworkPolicy leaks)
    (final : (runtime.reactiveApplication leaks).Execution)
    (reached : final ∈ (runtime.runInteractionPlan leaks
      (runtime.decisionWindowPlayers leaks owner event opening
        (initial.recall owner).length selected) network
      ((roster.map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        (List.replicate ticks .tick ++ [.expire event])) initial).support) :
    final.application = { after with clock := after.clock + ticks } ∧
      final.network.Satisfies (fun message =>
        message.id ∈ final.network.ledger.map Message.id) := by
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨middle, prior, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨application, clean⟩ := runtime.decisionWindow_settlement leaks owner event opening
    roster selected initial serials published owned valid network middle prior
  rw [accepted, Option.getD_some] at application
  have complete : ¬middle.application.config.cut.Ready event := application ▸ settled
  obtain ⟨next, law, state, messages, _, _⟩ := runtime.settled_reveal_expiry leaks
    (runtime.decisionWindowPlayers leaks owner event opening (initial.recall owner).length selected)
    network middle event complete ticks
  rw [law] at continued
  cases (PMF.mem_support_pure_iff _ _).mp continued
  exact ⟨by simpa only [application] using state, by simpa only [messages] using clean⟩

end Vegas.EventGraphRuntime
