/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ResponseProtocol

/-! # Response histories expand to actual native histories

Each response expands to exactly its constituent legal owner actions, with
no environment step inserted or removed. Consequently every coalesced state
has an initialized native history with the same execution and service suffix.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
  (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)

theorem native_actions_history (who : Player) (actions : List (PlayerAction graph))
    (history : (runtime.nativeProtocol inputs roster reactionRounds wire order).History)
    (epochs : Nat) (rest : List (ServiceInstruction graph)) (execution : NativeExecution runtime)
    (stateEq : history.state = some ⟨epochs,
      List.replicate actions.length (.player who) ++ rest, execution⟩) :
    ∃ after : (runtime.nativeProtocol inputs roster reactionRounds wire order).History,
      (runtime.nativeProtocol inputs roster reactionRounds wire order).ReachesWithin
        actions.length history after ∧
      after.state = some ⟨epochs, rest, runtime.takeActions who execution actions⟩ := by
  induction actions generalizing history execution with
  | nil => exact ⟨history, .refl 0 history, stateEq⟩
  | cons action actions ih =>
      let joint : Player → Option (PlayerAction graph) := fun observer =>
        if observer = who then some action else none
      have legal : (runtime.nativeProtocol inputs roster reactionRounds wire order).Legal
          history.state joint := by
        rw [stateEq]
        refine ⟨by simp [nativeProtocol, nativeTerminal, NativeControl.Terminal], ?_⟩
        intro observer
        by_cases same : observer = who
        · subst observer
          simp [joint, nativeProtocol, nativeActor, List.replicate_succ]
        · simp [joint, same, Ne.symm same, nativeProtocol, nativeActor, List.replicate_succ]
      have law : (runtime.nativeProtocol inputs roster reactionRounds wire order).step history.state
          ⟨joint, legal⟩ = FinDist.pure (some ⟨epochs,
            List.replicate actions.length (.player who) ++ rest,
            runtime.takeAction who execution action⟩) := by
        change runtime.nativeTransition inputs roster reactionRounds wire order
          history.state joint = _
        rw [stateEq]
        simp only [nativeTransition, List.length_cons, List.replicate_succ,
          List.cons_append, nativeInstructionStep, joint, ↓reduceIte, Option.getD_some,
          actionStep, FinDist.map_pure]
      have supported : some ⟨epochs, List.replicate actions.length (.player who) ++ rest,
          runtime.takeAction who execution action⟩ ∈
          ((runtime.nativeProtocol inputs roster reactionRounds wire order).step history.state
            ⟨joint, legal⟩).support := by rw [law]; exact FinDist.mem_support_pure.mpr rfl
      obtain ⟨after, path, endpoint⟩ := ih (history.extend legal supported)
        (runtime.takeAction who execution action) rfl
      exact ⟨after, .step joint legal supported path, endpoint⟩

theorem response_step_native_history
    (history : (runtime.nativeProtocol inputs roster reactionRounds wire order).History)
    (joint : Player → Option (List (PlayerAction graph)))
    (legal : (runtime.responseProtocol inputs roster reactionRounds wire order).Legal
      history.state joint)
    (after : NativeProtocolState runtime)
    (reached : after ∈ (runtime.responseTransition inputs roster reactionRounds wire order
      history.state joint).support) :
    ∃ next : (runtime.nativeProtocol inputs roster reactionRounds wire order).History,
      next.state = after := by
  have environment (inactive : runtime.nativeActor history.state = none)
      (law : runtime.responseTransition inputs roster reactionRounds wire order
        history.state joint =
        runtime.nativeTransition inputs roster reactionRounds wire order history.state
          (fun _ => none)) :
      ∃ next : (runtime.nativeProtocol inputs roster reactionRounds wire order).History,
        next.state = after := by
    have nativeLegal : (runtime.nativeProtocol inputs roster reactionRounds wire order).Legal
        history.state (fun _ => none) := by
      refine ⟨legal.1, fun who => ?_⟩
      change ¬ runtime.nativeActor history.state = some who
      rw [inactive]
      simp
    rw [law] at reached
    exact ⟨history.extend nativeLegal reached, rfl⟩
  cases stateEq : history.state with
  | none => exact environment (by rw [stateEq]; rfl) (by rw [stateEq]; rfl)
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil => exact environment (by rw [stateEq]; rfl) (by rw [stateEq]; rfl)
      | cons instruction rest =>
          cases instruction with
          | player who =>
              have active :
                  (runtime.responseProtocol inputs roster reactionRounds wire order).active
                    history.state who := by
                change runtime.nativeActor history.state = _
                rw [stateEq]
                rfl
              obtain ⟨actions, selected⟩ := LegalOption.exists_eq_some_of_active (joint who)
                (ExecutionProtocol.legalOption_of_legal legal who) active
              have length : actions.length = responseLength who (.player who :: rest) := by
                have available := legal.2 who
                rw [selected] at available
                simpa only [responseProtocol, Set.mem_ofPred_eq, stateEq, responseCount]
                  using available.2
              have expanded := responseLength_prefix who (.player who :: rest)
              have starting : history.state = some ⟨epochs,
                  List.replicate actions.length (.player who) ++
                    (.player who :: rest).drop actions.length, execution⟩ := by
                rw [length, expanded]
                exact stateEq
              obtain ⟨next, _, endpoint⟩ := runtime.native_actions_history inputs roster
                reactionRounds wire order who actions history epochs _ execution starting
              have target := reached
              rw [stateEq] at target
              simp only [responseTransition, selected, Option.getD_some,
                FinDist.mem_support_pure] at target
              exact ⟨next, by rw [endpoint, length]; exact target.symm⟩
          | wire | grant event | includeLatest event owner | sample event | tick | expire event =>
              exact environment (by rw [stateEq]; rfl) (by rw [stateEq]; rfl)

/-- Every legal coalesced history has a native realization. This includes
all off-path response lists, wire choices, and private setup draws. -/
theorem response_history_native :
    ∀ {state}
      (_trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state),
      ∃ history : (runtime.nativeProtocol inputs roster reactionRounds wire order).History,
        history.state = state
  | _, .start => ⟨(runtime.nativeProtocol inputs roster reactionRounds wire order).initHistory, rfl⟩
  | _, .extend prior joint legal reached => by
      obtain ⟨history, same⟩ := response_history_native prior
      apply runtime.response_step_native_history inputs roster reactionRounds wire order
        history joint
      · rwa [same]
      · rwa [same]

theorem response_history_counters {state : NativeProtocolState runtime}
    (trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state) :
    runtime.nativeCounters state := by
  obtain ⟨history, same⟩ :=
    runtime.response_history_native inputs roster reactionRounds wire order trace
  rw [← same]
  exact runtime.native_history_counters inputs roster reactionRounds wire order history.trace

end Vegas.EventGraphRuntime
