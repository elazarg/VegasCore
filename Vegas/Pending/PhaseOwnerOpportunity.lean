/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceContract
import Interaction.ReactiveHistory

/-! # Actual attempt-local activations within the original reaction bound -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseService

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "P" => phaseApplication runtime leaks

/-- Every actual recorded activation episode has an activation within the
original opportunity bound. All earlier histories remain physical histories,
including arbitrary deviations and previous attempt retirements. -/
theorem recorded_activation_within_delay
    (initial : PMF (P).State) (horizon : Nat) (scheduler : (P).Scheduler)
    (delay : graph.EventId → Nat)
    (opportunity : Opportunity runtime leaks initial horizon scheduler delay)
    (control : (P).Control) (trace : ((P).protocol initial horizon scheduler).Trace (some control))
    (coordinate : CommitAttemptEvent graph) (owner : Player) (entered : Nat)
    (actor : graph.actor? coordinate.event = some owner)
    (existsActivation : OwnerActivatedSince runtime leaks control.execution.environmentRecall
      coordinate owner entered) :
    ∃ entry ∈ control.execution.environmentRecall, entry.command = .activate owner ∧
      entry.beforeView.application.attempt = coordinate.attempt ∧
      entry.beforeView.application.native.EventReady coordinate.event ∧
      entry.beforeView.application.native.activatedAt coordinate.event = some entered ∧
      entry.beforeView.application.native.clock ≤ entered + delay coordinate.event := by
  have provenance : ∀ {state} (_history : ((P).protocol initial horizon scheduler).Trace state),
      state.elim True (fun current => ∀ coordinate owner entered,
        graph.actor? coordinate.event = some owner →
        OwnerActivatedSince runtime leaks current.execution.environmentRecall
          coordinate owner entered →
        ∃ entry ∈ current.execution.environmentRecall, entry.command = .activate owner ∧
          entry.beforeView.application.attempt = coordinate.attempt ∧
          entry.beforeView.application.native.EventReady coordinate.event ∧
          entry.beforeView.application.native.activatedAt coordinate.event = some entered ∧
          entry.beforeView.application.native.clock ≤ entered + delay coordinate.event) := by
    intro state history
    induction history with
    | start => trivial
    | @extend source target prior joint legal reached ih =>
        cases source with
        | none =>
            obtain ⟨state, _support, rfl⟩ := PMF.support_map .. ▸ reached
            intro coordinate owner entered actor existsActivation
            obtain ⟨entry, member, _⟩ := existsActivation
            exact (List.not_mem_nil member).elim
        | some current =>
            rcases current with ⟨remaining, acting, execution⟩
            cases acting with
            | some who =>
                cases (PMF.mem_support_pure_iff _ _).mp reached
                simpa only [Option.elim_some, (P).respond_environmentRecall] using ih
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨chosen, _selected, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                    have entries : next.environmentRecall = execution.environmentRecall ++
                        [⟨execution.observeEnvironment P, chosen⟩] := by
                      unfold ReactiveApplication.Execution.environmentStep at supported
                      obtain ⟨updated, _support, rfl⟩ := PMF.support_map .. ▸ supported
                      rfl
                    intro coordinate owner entered actor existsActivation
                    obtain ⟨entry, member, chosenEq, sameAttempt, ready, activated⟩ :=
                      existsActivation
                    rw [entries, List.mem_append, List.mem_singleton] at member
                    have liftEarlier : OwnerActivatedSince runtime leaks
                        execution.environmentRecall coordinate owner entered →
                        ∃ entry ∈ next.environmentRecall, entry.command = .activate owner ∧
                          entry.beforeView.application.attempt = coordinate.attempt ∧
                          entry.beforeView.application.native.EventReady coordinate.event ∧
                          entry.beforeView.application.native.activatedAt coordinate.event =
                            some entered ∧
                          entry.beforeView.application.native.clock ≤
                            entered + delay coordinate.event := by
                      intro earlier
                      obtain ⟨earlier, member, facts⟩ := ih coordinate owner entered actor earlier
                      exact ⟨earlier, entries ▸ List.mem_append_left _ member, facts⟩
                    rcases member with earlier | rfl
                    · exact liftEarlier ⟨entry, earlier, chosenEq, sameAttempt, ready, activated⟩
                    · by_cases timely : execution.application.current.native.clock ≤
                          entered + delay coordinate.event
                      · exact ⟨_, entries ▸ List.mem_append_right _
                          (List.mem_singleton.mpr rfl), chosenEq, sameAttempt, ready, activated,
                          timely⟩
                      · apply liftEarlier
                        have earlier := opportunity ⟨remaining + 1, none, execution⟩ prior
                          coordinate.event owner entered actor ready activated (by
                            change entered + delay coordinate.event <
                              execution.application.current.native.clock
                            omega)
                        change execution.application.attempt = coordinate.attempt at sameAttempt
                        rw [sameAttempt] at earlier
                        exact earlier
  exact provenance trace coordinate owner entered actor existsActivation

end Vegas.EventGraphRuntime.PhaseService
