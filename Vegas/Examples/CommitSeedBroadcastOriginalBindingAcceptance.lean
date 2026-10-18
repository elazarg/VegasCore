/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastFirstLossAcceptance
import Vegas.Examples.CommitSeedBroadcastBindingReceipts

/-! # Original requests persist before their first unaccepted expiry -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem unaccepted_expiry_late (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (moved : next ∈ (execution.environmentStep app
      (.application (.expire (bindingEvent owner)))).support)
    (lost : ¬ next.application.SeedRequest owner (originalCoordinate owner)) :
    27 ≤ execution.environmentRecall.length := by
  classical
  by_contra early
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have stamp := original_timer (family seeds) _ trace original owner request.2.2.1.1
  change execution.application.current.native.activatedAt (bindingEvent owner) = some 0 at stamp
  have timely : execution.application.current.native.WithinDeadline runtime
      (bindingEvent owner) := by
    rw [State.WithinDeadline, stamp]
    change execution.application.current.native.clock - 0 < 6
    rw [Nat.sub_zero, original_clock_index seeds _ trace original]
    have small : execution.environmentRecall.length < 27 := by omega
    generalize countEq : execution.environmentRecall.length = count at small ⊢
    interval_cases count <;> decide
  have nativeMoved : next.application ∈ (execution.application.environment runtime
      (.expire (bindingEvent owner))).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
    obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ moved
    exact supported
  exact lost (PhaseRuntimeState.expiry_request_before_deadline runtime execution.application
    next.application owner (originalCoordinate owner) request timely nativeMoved)

private theorem original_unaccepted_progress (seeds : Seeds) :
    ∀ {state} (_trace : (app.protocol initial horizon (family seeds)).Trace state),
      state.elim True (fun current => ∀ owner,
        (¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
          current.execution) →
        current.execution.application.SeedRequest owner (originalCoordinate owner) ∨
          28 ≤ current.execution.environmentRecall.length) := by
  classical
  intro state trace
  induction trace with
  | start => trivial
  | @extend source target prior joint legal reached ih =>
      let targetTrace := prior.extend joint legal reached
      change target ∈ (app.transition initial horizon (family seeds) source joint).support
        at reached
      cases source with
      | none =>
          obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ reached
          rw [initial, PMF.mem_support_pure_iff] at supported
          subst state
          intro owner _unaccepted
          left
          change initialState.SeedRequest owner (originalCoordinate owner)
          have valid := (PhaseRuntimeState.initial_invariant plan
            (encodeInputs (Env.empty (CellVal simpleExpr)))).1
          apply (initialState.requests_publicView valid owner (originalCoordinate owner)).mp
          exact initial_bindings_ready owner
      | some current =>
          obtain ⟨after, rfl, _recalled⟩ := app.transition_recall_prefix initial horizon
            (family seeds) current target joint reached
          intro owner unaccepted
          have earlierUnaccepted : ¬ PhaseService.BindingAccepted runtime leaks
              (originalCoordinate owner) owner current.execution := by
            intro accepted
            exact unaccepted (bindingAccepted_transition seeds current after prior targetTrace
              (originalCoordinate owner) owner accepted joint reached)
          have previous := ih owner earlierUnaccepted
          rcases current with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              rcases previous with request | late
              · exact Or.inl (respond_request runtime leaks execution actor _ owner
                  (originalCoordinate owner) request)
              · right
                rwa [app.respond_environmentRecall]
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _selected, moved⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
                  cases Option.some.inj same
                  rcases previous with request | late
                  · by_cases retained : next.application.SeedRequest owner
                        (originalCoordinate owner)
                    · exact Or.inl retained
                    · have alternatives := unaccepted_request_retained_or_expiry seeds
                        (remaining + 1) execution next prior (originalCoordinate owner) owner
                          request command supported unaccepted
                      obtain preserved | expiry := alternatives
                      · exact (retained preserved).elim
                      · have expiryMoved := supported
                        rw [expiry] at expiryMoved
                        have lower := unaccepted_expiry_late seeds (remaining + 1) execution next
                          prior owner request expiryMoved retained
                        right
                        rw [app.environmentStep_environmentRecall execution next command supported,
                          List.length_append, List.length_singleton]
                        omega
                  · right
                    change 28 ≤ execution.environmentRecall.length at late
                    rw [app.environmentStep_environmentRecall execution next command supported,
                      List.length_append, List.length_singleton]
                    omega

/-- Before the first original expiry, the absence of an actual accepting
receipt keeps the original binding genuinely requested, even with a pending
raw packet and arbitrary foreign responses. -/
theorem original_request_of_unaccepted_before_expiry (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player)
    (unaccepted : ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      current.execution)
    (early : current.execution.environmentRecall.length < 28) :
    current.execution.application.SeedRequest owner (originalCoordinate owner) := by
  obtain request | late := original_unaccepted_progress seeds trace owner unaccepted
  · exact request
  · omega

end Vegas.Examples.CommitSeedBroadcast
