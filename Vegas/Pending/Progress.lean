/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.StepLaw
import Interaction.MessageApplicationLaws

/-! # Progress under the ideal clock service

A graph has a finite bound on the number of application ticks needed to finish.
Each tick either consumes a waiting unit or completes a phase. This is a
completion property, not timely inclusion: ticking without serving players can
force their failures. Preserving prescribed play needs a separate service
condition protecting their submission opportunities.

The application tick includes execution of expiry and chance transitions. A
transaction runtime must implement that progress service; observing a block
height alone does not execute an application transition.
-/

noncomputable section
namespace Vegas

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

/-- Worst-case ticks from entry to a graph phase, including every later phase. -/
def Graph.tickBudget (deadline : Nat → Nat) : {Γ Δ : VCtx Player L} →
    Graph Player L Γ Δ → Nat → Nat
  | _, _, .ret _, _ => 0
  | _, _, .sample _ _ _ next, pc => 1 + next.tickBudget deadline (pc + 1)
  | _, _, .bind _ _ _ next, pc =>
      max 1 (deadline pc) + next.tickBudget deadline (pc + 1)
  | _, _, .resolve _ _ _ _ _ _ next, pc =>
      max 1 (deadline pc) + next.tickBudget deadline (pc + 1)

namespace GraphRuntime

variable {Δ : VCtx Player L}

/-- Remaining ticks, accounting for time already spent in the current phase. -/
def State.ticksRemaining (runtime : GraphRuntime Player L Δ) : State Player L Δ → Nat
  | .running graph _ _ _ _ pc clock enteredAt =>
      match graph with
      | .ret _ => 0
      | .sample _ _ _ next => 1 + next.tickBudget runtime.deadline (pc + 1)
      | .bind _ _ _ next =>
          max 1 (runtime.deadline pc - (clock - enteredAt)) +
            next.tickBudget runtime.deadline (pc + 1)
      | .resolve _ _ _ _ _ _ next =>
          max 1 (runtime.deadline pc - (clock - enteredAt)) +
            next.tickBudget runtime.deadline (pc + 1)

/-- A phase starts no later than the current application clock. -/
def State.ClockOrdered : State Player L Δ → Prop
  | .running _ _ _ _ _ _ clock enteredAt => enteredAt ≤ clock

theorem State.initial_clockOrdered {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) (input : VEnv L Γ) :
    (State.initial graph input).ClockOrdered := Nat.le_refl _

theorem State.ticksRemaining_entry (runtime : GraphRuntime Player L Δ)
    {Γ : VCtx Player L} (graph : Graph Player L Γ Δ)
    (ideal : VEnv L Γ) (values : Graph.PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L)) (pc clock : Nat) :
    (State.running graph ideal values bindings candidates pc clock clock).ticksRemaining runtime =
      graph.tickBudget runtime.deadline pc := by
  cases graph <;> simp [State.ticksRemaining, Graph.tickBudget]

theorem State.ticksRemaining_eq_zero_iff (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) :
    state.ticksRemaining runtime = 0 ↔ state.outcome?.isSome = true := by
  cases state with
  | running graph =>
      cases graph <;> simp [State.ticksRemaining, State.outcome?]

/-- A supported tick maintains clock order and strictly reduces the budget
unless execution was already terminal. -/
theorem tick_progress (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ) (ordered : state.ClockOrdered)
    (supported : next ∈ (runtime.tick state).support) :
    next.ClockOrdered ∧
      next.ticksRemaining runtime ≤ state.ticksRemaining runtime - 1 := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret payoffs =>
          simp only [tick, FinDist.mem_support_pure] at supported
          subst next
          simp only [State.ClockOrdered] at ordered ⊢
          exact ⟨by omega, by simp [State.ticksRemaining]⟩
      | sample name fresh law tail =>
          simp only [tick, FinDist.support_map, Set.mem_image] at supported
          obtain ⟨value, _, rfl⟩ := supported
          refine ⟨Nat.le_refl _, ?_⟩
          rw [State.ticksRemaining_entry]
          simp [State.ticksRemaining]
      | bind name owner fresh tail =>
          simp only [tick] at supported
          split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst next
            refine ⟨Nat.le_refl _, ?_⟩
            change (State.running tail _ _ _ _ _ (clock + 1) (clock + 1)).ticksRemaining
              runtime ≤ _
            rw [State.ticksRemaining_entry]
            simp only [State.ticksRemaining]
            omega
          · rename_i notExpired
            simp only [FinDist.mem_support_pure] at supported
            subst next
            simp only [State.ClockOrdered] at ordered ⊢
            refine ⟨by omega, ?_⟩
            simp only [State.ticksRemaining]
            omega
      | resolve outputName owner bindingName fresh source checks tail =>
          simp only [tick] at supported
          split at supported
          · simp only [FinDist.mem_support_pure] at supported
            subst next
            refine ⟨Nat.le_refl _, ?_⟩
            change (State.running tail _ _ _ _ _ (clock + 1) (clock + 1)).ticksRemaining
              runtime ≤ _
            rw [State.ticksRemaining_entry]
            simp only [State.ticksRemaining]
            omega
          · rename_i notExpired
            simp only [FinDist.mem_support_pure] at supported
            subst next
            simp only [State.ClockOrdered] at ordered ⊢
            refine ⟨by omega, ?_⟩
            simp only [State.ticksRemaining]
            omega

/-- Private preparation cannot change the graph phase or consume clock time. -/
theorem privateStep_progress (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L) :
    (runtime.privateStep state who command).ClockOrdered = state.ClockOrdered ∧
      (runtime.privateStep state who command).ticksRemaining runtime =
        state.ticksRemaining runtime := by
  cases state
  cases command <;> exact ⟨rfl, rfl⟩

/-- An accepted packet completes one phase, regardless of its decoded value.
Rejection is handled as a stutter by the message runner. -/
theorem handle_progress (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ) (message : Message Player (Payload Player L))
    (accepted : runtime.handle state message = some next) :
    next.ClockOrdered ∧ next.ticksRemaining runtime < state.ticksRemaining runtime := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
          cases graph with
          | ret => simp [handle] at accepted
          | sample => simp [handle] at accepted
          | bind name owner fresh tail =>
              cases payload with
              | commitment site candidate =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  refine ⟨Nat.le_refl _, ?_⟩
                  change (State.running tail _ _ _ _ _ clock clock).ticksRemaining runtime < _
                  rw [State.ticksRemaining_entry]
                  simp only [State.ticksRemaining]
                  omega
              | opening | withhold | malformed => simp [handle] at accepted
          | resolve output owner binding fresh source checks tail =>
              have progress (result : PublicationResult (L.Val _)) :
                  let after := advanceResolve tail ideal values bindings candidates pc clock result
                  let before := State.running
                    (.resolve output owner binding fresh source checks tail)
                    ideal values bindings candidates pc clock enteredAt
                  after.ClockOrdered ∧
                    after.ticksRemaining runtime < before.ticksRemaining runtime := by
                refine ⟨Nat.le_refl _, ?_⟩
                change (State.running tail _ _ _ _ _ clock clock).ticksRemaining runtime < _
                rw [State.ticksRemaining_entry]
                simp only [State.ticksRemaining]
                omega
              cases payload with
              | commitment | malformed => simp [handle] at accepted
              | opening site candidate raw =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases typed : raw.as? (R.result _) with
                  | none => rw [typed] at accepted; contradiction
                  | some encoded =>
                      rw [typed] at accepted
                      cases accepted
                      exact progress _
              | withhold site =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  exact progress _

/-- Only application ticks count as progress-service invocations. -/
def isTick (runtime : GraphRuntime Player L Δ) : runtime.application.Action → Bool
  | .environment .tick => true
  | _ => false

/-- Arbitrary packet operations cannot replenish the completion budget. -/
theorem step_progress (runtime : GraphRuntime Player L Δ)
    (state next : runtime.application.State) (action : runtime.application.Action)
    (ordered : state.application.ClockOrdered)
    (supported : next ∈ (runtime.application.step state action).support) :
    next.application.ClockOrdered ∧
      next.application.ticksRemaining runtime ≤
        state.application.ticksRemaining runtime - (if runtime.isTick action then 1 else 0) := by
  cases action with
  | environment command =>
      cases command
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨application, happened, rfl⟩ := supported
      exact runtime.tick_progress _ _ ordered happened
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      obtain ⟨hclock, hbudget⟩ := runtime.privateStep_progress state.application who command
      refine ⟨hclock.mpr ordered, ?_⟩
      change (runtime.privateStep state.application who command).ticksRemaining runtime ≤
        state.application.ticksRemaining runtime - 0
      rw [hbudget, Nat.sub_zero]
  | submit | replay | deliver =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      exact ⟨ordered, by simp [isTick]⟩
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      apply runtime.application.includePending_application_invariant
        (fun application => application.ClockOrdered ∧
          application.ticksRemaining runtime ≤ state.application.ticksRemaining runtime)
        ?_ state id ⟨ordered, Nat.le_refl _⟩
      intro before message after hbefore accepted
      have progress := runtime.handle_progress before after message accepted
      exact ⟨progress.1, Nat.le_trans (Nat.le_of_lt progress.2) hbefore.2⟩

/-- Enough actual progress ticks force completion despite arbitrary intervening
submissions, deliveries, malformed packets, replay, or private preparation. -/
theorem run_progress (runtime : GraphRuntime Player L Δ)
    (actions : List runtime.application.Action) (state next : runtime.application.State)
    (ordered : state.application.ClockOrdered)
    (supported : next ∈ (runtime.application.run actions state).support) :
    next.application.ClockOrdered ∧
      next.application.ticksRemaining runtime ≤
        state.application.ticksRemaining runtime - actions.countP runtime.isTick := by
  induction actions generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil, FinDist.mem_support_pure] at supported
      subst next
      exact ⟨ordered, by simp⟩
  | cons action rest ih =>
      simp only [MessageApplication.run_cons, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, hmiddle, hnext⟩ := supported
      have first := runtime.step_progress state middle action ordered hmiddle
      have tail := ih middle first.1 hnext
      refine ⟨tail.1, ?_⟩
      have hfirst := first.2
      have htail := tail.2
      simp only [List.countP_cons]
      cases ticked : runtime.isTick action <;>
        simp only [ticked, Bool.false_eq_true, ↓reduceIte] at hfirst ⊢
      all_goals omega

theorem run_completed_of_ticks (runtime : GraphRuntime Player L Δ)
    (actions : List runtime.application.Action) (state next : runtime.application.State)
    (ordered : state.application.ClockOrdered)
    (enough : state.application.ticksRemaining runtime ≤ actions.countP runtime.isTick)
    (supported : next ∈ (runtime.application.run actions state).support) :
    next.application.outcome?.isSome = true := by
  apply (State.ticksRemaining_eq_zero_iff runtime next.application).mp
  have progress := (runtime.run_progress actions state next ordered supported).2
  omega

end GraphRuntime
end Vegas
