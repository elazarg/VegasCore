/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingFirstLossAcceptance
import Interaction.ReactiveReceipts

/-! # Original requests before their first unaccepted expiry -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem bindingAccepted_transition (seeds : Seeds) (before after : app.Control)
    (prior : (app.protocol initial horizon (family seeds)).Trace (some before))
    (trace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks coordinate owner before.execution)
    (joint : Player → Option app.Action)
    (moved : some after ∈
      (app.transition initial horizon (family seeds) (some before) joint).support) :
    PhaseService.BindingAccepted runtime leaks coordinate owner after.execution := by
  obtain ⟨message, input, authored, tag, named, receipt⟩ := accepted
  obtain ⟨next, same, recalled⟩ := app.transition_recall_prefix initial horizon (family seeds)
    before (some after) joint moved
  cases Option.some.inj same
  have output : message ∈ app.outputs (before.execution.recall owner) := by
    rw [← app.history_inputRecall initial horizon (family seeds) prior owner]
    exact List.mem_filter.mpr ⟨input, decide_eq_true authored⟩
  obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
  have laterOutput : message ∈ app.outputs (after.execution.recall owner) :=
    List.mem_filterMap.mpr ⟨entry, (recalled owner).subset member, emitted⟩
  rw [← app.history_inputRecall initial horizon (family seeds) trace owner] at laterOutput
  obtain ⟨next, same, receipts⟩ := app.transition_receipts_prefix initial horizon (family seeds)
    before (some after) joint moved
  cases Option.some.inj same
  exact ⟨message, (List.mem_filter.mp laterOutput).1, authored, tag, named, receipts.subset receipt⟩

/-- Actual accepting packets and their true receipts persist along the same
raw initialized trace, including normalization and every later reset. -/
theorem bindingAccepted_prefix (seeds : Seeds) (before after : app.Control)
    (prior : (app.protocol initial horizon (family seeds)).Trace (some before))
    (trace : (app.protocol initial horizon (family seeds)).Trace (some after))
    (kept : TracePrefix prior trace) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (accepted : PhaseService.BindingAccepted runtime leaks coordinate owner before.execution) :
    PhaseService.BindingAccepted runtime leaks coordinate owner after.execution := by
  have along : ∀ {state} {later : (app.protocol initial horizon (family seeds)).Trace state},
      TracePrefix prior later → ∃ current : app.Control, state = some current ∧
        PhaseService.BindingAccepted runtime leaks coordinate owner current.execution := by
    intro state later retained
    induction retained with
    | refl => exact ⟨before, rfl, accepted⟩
    | @extend source target earlier retained joint legal realized ih =>
        obtain ⟨current, rfl, valid⟩ := ih
        have moved : target ∈ (app.transition initial horizon (family seeds)
            (some current) joint).support := realized
        obtain ⟨next, same, _recalled⟩ := app.transition_recall_prefix initial horizon
          (family seeds) current target joint moved
        subst target
        exact ⟨next, rfl, bindingAccepted_transition seeds current next earlier
          (earlier.extend joint legal realized) coordinate owner valid joint moved⟩
  obtain ⟨current, same, valid⟩ := along kept
  cases Option.some.inj same
  exact valid
private theorem unaccepted_expiry_late (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (app.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (owner : Player)
    (request : execution.application.SeedRequest owner (originalCoordinate owner))
    (moved : next ∈ (execution.environmentStep app
      (.application (.expire (bindingEvent owner)))).support)
    (lost : ¬ next.application.SeedRequest owner (originalCoordinate owner)) :
    20 ≤ execution.environmentRecall.length := by
  classical
  by_contra early
  have original : execution.application.attempt = originalAttempt := request.1.symm
  have binding : bindingEvent owner = aliceBinding ∨ bindingEvent owner = bobBinding := by
    fin_cases owner
    · exact Or.inl rfl
    · exact Or.inr rfl
  have stamp := original_timer (family seeds) _ trace original (bindingEvent owner) binding
    request.2.2.1.1
  change execution.application.current.native.activatedAt (bindingEvent owner) = some 0 at stamp
  have timely : execution.application.current.native.WithinDeadline runtime
      (bindingEvent owner) := by
    rw [State.WithinDeadline, stamp]
    change execution.application.current.native.clock - 0 < 6
    rw [Nat.sub_zero, original_clock_index seeds _ trace original]
    have small : execution.environmentRecall.length < 20 := by omega
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
          21 ≤ current.execution.environmentRecall.length) := by
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
          rw [initial_eq_pure, PMF.mem_support_pure_iff] at supported
          subst state
          intro owner _unaccepted
          left
          change initialState.SeedRequest owner (originalCoordinate owner)
          have valid := (PhaseRuntimeState.initial_invariant plan
            (encodeInputs (Env.empty (CellVal simpleExpr)))).1
          apply (initialState.requests_publicView valid owner (originalCoordinate owner)).mp
          have readyOwner : ready owner (bindingEvent owner)
              (initialExecution.observeEnvironment app) = true := by
            fin_cases owner
            · change ready alice aliceBinding (initialExecution.observeEnvironment app) = true
              exact initial_bindings_ready.1
            · change ready bob bobBinding (initialExecution.observeEnvironment app) = true
              exact initial_bindings_ready.2
          change decide (PhaseRuntimeState.requests initialState.publicView owner
            ⟨initialState.attempt, bindingEvent owner⟩) = true at readyOwner
          rw [initialState_attempt] at readyOwner
          exact of_decide_eq_true readyOwner
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
                    change 21 ≤ execution.environmentRecall.length at late
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
    (early : current.execution.environmentRecall.length < 21) :
    current.execution.application.SeedRequest owner (originalCoordinate owner) := by
  obtain request | late := original_unaccepted_progress seeds trace owner unaccepted
  · exact request
  · omega

end Vegas.Examples.CommitSeedSignalling
