/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveOpeningExpiry

/-! # Continuation laws inside an opening window

The policy mixture is conditioned on the owner's actual response recall.
Compatible timing modes share the current operational frame, and protected
inclusion then depends only on whether the mode eventually opens. No new
private state, observation, or execution procedure is introduced.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Timing modes with the same already-opened status describe the same
current network frame. Their future selected slot can still differ. -/
theorem OpeningWindowFrame.relabel (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (selected other : Option (Fin slots)) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (frame : runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
      initial current) (same : openingPassed other visits = openingPassed selected visits) :
    runtime.OpeningWindowFrame leaks owner event candidate raw offset other visits initial current
    where
  application := frame.application
  ledger := frame.ledger
  receipts := frame.receipts
  count := frame.count
  counters := by simpa only [same] using frame.counters
  serials := frame.serials
  packets := frame.packets
  opened := fun opened => frame.opened (same ▸ opened)

/-- The exact behavioral realization at an arbitrary continuation start uses
the posterior inferred from actual private recall, rather than its initial law. -/
theorem openingWindowMixture_continuation (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : FinDist (Option (Fin slots)))
    (network : runtime.NetworkPolicy leaks) (plan : List (ServiceInstruction graph))
    (current : (runtime.reactiveApplication leaks).Execution) :
    let app := runtime.reactiveApplication leaks
    let family := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure (runtime.windowOpening leaks event candidate raw)) app.replayPolicy
    (runtime.runInteractionPlan leaks
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices)
        network plan current) =
      ((app.policyMixture choices family).posterior (current.recall owner)).bind fun selected =>
        runtime.runInteractionPlan leaks
          (runtime.openingWindowPlayers leaks owner event candidate raw offset selected)
            network plan current := by
  intro app family
  have actual := runtime.runInteractionPlan_policyMixture leaks choices family owner
    (fun _ => app.replayPolicy) network plan current
  refine actual.symm.trans ?_
  apply FinDist.bind_congr
  intro selected _
  have players : Function.update (fun _ => app.replayPolicy) owner (family selected) =
      runtime.openingWindowPlayers leaks owner event candidate raw offset selected := by
    funext who past view
    by_cases active : who = owner
    · subst who
      simp only [Function.update_self, openingWindowPlayers, ↓reduceIte]
      rfl
    · simp only [Function.update_of_ne active, openingWindowPlayers, active, ↓reduceIte]
      rfl
  rw [players]

/-- Every remaining timing mode gives the prescribed protected-inclusion
result, from the actual current window state and all its pending replays. -/
theorem openingWindowMixture_continuation_settlement (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (owner : Player) (event : graph.EventId) (candidate : Handle graph) (raw : Raw L)
    (offset : Nat) {slots : Nat} (choices : FinDist (Option (Fin slots))) (visits : Nat)
    (initial current : (runtime.reactiveApplication leaks).Execution)
    (serials : initial.network.SerialsBeforeNext)
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    (remaining : List Player) (complete : visits + remaining.count owner = slots)
    (network : runtime.NetworkPolicy leaks) :
    let app := runtime.reactiveApplication leaks
    let family := fun selected => app.scheduledPolicy offset selected
      (fun _ _ => FinDist.pure (runtime.windowOpening leaks event candidate raw)) app.replayPolicy
    let posterior := (app.policyMixture choices family).posterior (current.recall owner)
    (∀ selected ∈ posterior.support,
      runtime.OpeningWindowFrame leaks owner event candidate raw offset selected visits
        initial current) →
    (runtime.runInteractionPlan leaks
      (runtime.openingWindowMixturePlayers leaks owner event candidate raw offset choices)
        network (remaining.map ServiceInstruction.player ++ [.includeLatest event owner])
          current).map (fun final => final.application) =
      posterior.map (fun selected => if selected.isSome then
        (app.handle initial.application
          (runtime.windowEnvelope leaks owner event candidate raw initial)).getD initial.application
        else initial.application) := by
  intro app family posterior frames
  rw [runtime.openingWindowMixture_continuation, FinDist.map_bind]
  conv_rhs => rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro selected possible
  apply FinDist.eq_pure_of_support_subset_singleton
  intro result supported
  obtain ⟨final, reached, rfl⟩ := FinDist.support_map .. ▸ supported
  rw [runtime.runInteractionPlan_append] at reached
  obtain ⟨before, beforeSupport, included⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ reached)
  have finished := (frames selected possible).run runtime leaks owner event candidate raw offset
    selected visits initial current network remaining before beforeSupport owned (fun _ => valid)
  rw [complete] at finished
  have inclusion : final ∈ (runtime.interactionStep leaks
      (runtime.openingWindowPlayers leaks owner event candidate raw offset selected)
        network (.includeLatest event owner) before).support := by
    simpa only [runInteractionPlan, FinDist.bind_pure] using included
  exact (finished.settle runtime leaks owner event candidate raw offset selected
    initial before serials _ network final inclusion).1

end Vegas.EventGraphRuntime
