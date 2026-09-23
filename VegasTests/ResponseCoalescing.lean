/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.PendingMenus
import Vegas.Pending.ResponseBudget
import Vegas.Pending.NativeResponseSampling

/-! # Coalescing the actual pending-menu service

The three initial owner calls form one response. Their packets retain their
separate binding meanings, and the following wire call remains a boundary.
Every initialized response history has a multiple of three own action records,
so the two-call root used by the split-protocol impossibility is unreachable.
-/

noncomputable section

namespace VegasTests.ResponseCoalescing

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime
open PendingMenus

private abbrev arena := runtime.responseProtocol (FinDist.pure input) [] 1 wire ordering

/-- A concrete canonical information model using exactly the original native view. -/
def model : InformationModel arena :=
  runtime.responseInformation (FinDist.pure input) [] 1 wire ordering (fun _ _ => 3)
    (runtime.responseBudget_empty_roster (FinDist.pure input) 1 wire ordering)

example : arena.WellFoundedPlay :=
  runtime.response_terminates (FinDist.pure input) [] 1 wire ordering

example : arena.BoundedHorizon (runtime.nativeRemaining [] 1 none) :=
  runtime.response_bounded (FinDist.pure input) [] 1 wire ordering

example : responseLength () (graph := graph) [.player (), .wire, .player ()] = 1 := rfl

private def response : PlayerResponse graph 3 :=
  ⟨[first, second, bindingAction () 0 .int (.success 0) 2], rfl⟩

/-- The whole batch precedes the same wire slot; all three packet identities
and all private records survive the coalescing. -/
theorem response_before_wire :
    runtime.responseTransition (FinDist.pure input) [] 1 wire ordering
      (some ⟨5, orderedControl.plan.drop 1, initial⟩) (fun _ => some response.1) =
      FinDist.pure (some ⟨5, orderedControl.plan.drop 4,
        runtime.takeActions () initial response.1⟩) := rfl

theorem response_keeps_competing_packets :
    let after := runtime.takeActions () initial response.1
    after.native.pool.lookup ((), 0) =
        some ⟨((), 0), .commitment 0 ((), .prepared 0)⟩ ∧
      after.native.pool.lookup ((), 1) =
        some ⟨((), 1), .commitment 0 ((), .prepared 1)⟩ ∧
      after.native.pool.lookup ((), 2) =
        some ⟨((), 2), .commitment 0 ((), .prepared 2)⟩ ∧
      (after.principalHistory ()).length = 3 := ⟨rfl, rfl, rfl, rfl⟩

private def records : NativeProtocolState runtime → Nat
  | none => 0
  | some control => (control.execution.principalHistory ()).length

theorem response_records_multiple : ∀ {state} (_trace : arena.Trace state), records state % 3 = 0
  | _, .start => rfl
  | _, .extend (source := before) prior joint legal reached => by
      have earlier := response_records_multiple prior
      cases before with
      | none =>
          obtain ⟨draw, _, rfl⟩ := FinDist.support_map .. ▸ reached
          rfl
      | some control =>
          rcases control with ⟨epochs, plan, execution⟩
          cases plan with
          | nil =>
              cases epochs with
              | zero => cases FinDist.mem_support_pure.mp reached; exact earlier
              | succ epochs =>
                  obtain ⟨chosen, _, rfl⟩ := FinDist.support_map .. ▸ reached
                  exact earlier
          | cons instruction rest =>
              cases instruction with
              | player who =>
                  cases who
                  obtain ⟨actions, selected⟩ := LegalOption.exists_eq_some_of_active (joint ())
                    (ExecutionProtocol.legalOption_of_legal legal ()) rfl
                  have available := legal.2 ()
                  rw [selected] at available
                  have count := runtime.responseBudget_empty_roster (FinDist.pure input) 1
                    wire ordering ⟨_, prior⟩ () (runtime.nativeInput () execution)
                    (by simp [nativeObserve, nativeActor, nativeInput])
                  have length : actions.length = 3 := available.2.trans count.symm
                  change _ ∈ (runtime.responseTransition _ _ _ _ _ _ joint).support at reached
                  simp only [responseTransition, selected, Option.getD_some,
                    FinDist.mem_support_pure] at reached
                  subst_vars
                  change ((runtime.takeActions () execution actions).principalHistory ()).length %
                    3 = 0
                  rw [runtime.takeActions_history_length, length]
                  change (execution.principalHistory ()).length % 3 = 0 at earlier
                  omega
              | wire | grant event | includeLatest event owner
              | sample event | tick | expire event =>
                  obtain ⟨next, supported, rfl⟩ := FinDist.support_map .. ▸ reached
                  obtain ⟨middle, _, rfl⟩ := FinDist.support_map .. ▸ supported
                  exact earlier

/-- The internal two-action cut is absent from the coalesced history tree. -/
theorem contested_unreachable (history : arena.History) (control : NativeControl runtime)
    (stateEq : history.state = some control) : control.execution ≠ contested := by
  intro same
  have multiple := response_records_multiple history.trace
  rw [stateEq] at multiple
  change (control.execution.principalHistory ()).length % 3 = 0 at multiple
  rw [same] at multiple
  change 2 % 3 = 0 at multiple
  norm_num at multiple

end VegasTests.ResponseCoalescing
