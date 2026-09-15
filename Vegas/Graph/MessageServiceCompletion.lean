/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Graph.MessageService
import Vegas.Graph.MessageProgress
import Vegas.Graph.MessageServiceCursor
import Vegas.Graph.MessagePolicyHistory
import Interaction.MessageApplicationPolicyLaws

/-! # Graph-phase invariants for bounded service

The public program counter supplies the ordinal used by the concrete service.
These elementary laws isolate the part of completion which is independent of
player and wire policy: native actions never move that ordinal backwards, and
one effective application tick either leaves a terminal state alone or moves
time forward at the current phase.
-/

noncomputable section
namespace Vegas.GraphRuntime

open GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
variable {Γ Δ : VCtx Player L}

/-- A runtime state is at a genuine typed suffix of the original graph, and
its public ordinal is exactly the length of that prefix. -/
def State.Follows (whole : Graph Player L Γ Δ) (base : Nat)
    (state : State Player L Δ) : Prop :=
  ∃ (target : VCtx Player L) (suffix : Graph Player L target Δ) (length : Nat)
      (ideal : VEnv L target) (values : Graph.PublicValues target)
      (bindings : Bindings Player)
      (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat),
    ∃ _walk : Prefix Δ whole suffix length,
      state = .running suffix ideal values bindings candidates (base + length) clock enteredAt

theorem State.running_follows (graph : Graph Player L Γ Δ)
    (ideal : VEnv L Γ) (values : Graph.PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (base clock enteredAt : Nat) :
    (State.running graph ideal values bindings candidates base clock enteredAt).Follows
      graph base := by
  exact ⟨Γ, graph, 0, ideal, values, bindings, candidates, clock, enteredAt,
    Prefix.refl graph, by simp⟩

theorem State.initial_follows (graph : Graph Player L Γ Δ) (input : VEnv L Γ) :
    (State.initial graph input).Follows graph 0 := by
  unfold State.initial
  exact State.running_follows graph _ _ _ _ 0 0 0

theorem State.follows_phase (whole : Graph Player L Γ Δ) (base : Nat)
    (state : State Player L Δ) (follows : state.Follows whole base) :
    ∃ length, state.publicView.pc = base + length := by
  rcases follows with ⟨_, _, length, _, _, _, _, _, _, _, rfl⟩
  exact ⟨length, rfl⟩

/-- At the base ordinal, a following state is still at the original graph
head; positive prefixes necessarily have a larger public counter. -/
theorem State.follows_at_base (whole : Graph Player L Γ Δ) (base : Nat)
    (state : State Player L Δ) (follows : state.Follows whole base)
    (atBase : state.publicView.pc = base) :
    ∃ (ideal : VEnv L Γ) (values : Graph.PublicValues Γ)
        (bindings : Bindings Player)
        (candidates : CommitmentCandidates Player Slot (Raw L)) (clock enteredAt : Nat),
      state = .running whole ideal values bindings candidates base clock enteredAt := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases walk with
  | refl => exact ⟨ideal, values, bindings, candidates, clock, enteredAt, by simp⟩
  | sample rest | bind rest | resolve rest =>
      simp [State.publicView] at atBase

/-- If execution has already passed a binding head, the same state follows
the binding tail at the successor base ordinal. -/
theorem State.follows_bind_tail_of_lt {name : VarId} {owner : Player} {payload : L.Ty}
    {fresh} {tail : Graph Player L ((name, .sealed owner
      (IExpr.ResultTypes.result payload)) :: Γ) Δ}
    (base : Nat) (state : State Player L Δ)
    (follows : state.Follows (.bind name owner fresh tail) base)
    (passed : base < state.publicView.pc) :
    state.Follows tail (base + 1) := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases walk with
  | refl => simp [State.publicView] at passed
  | bind rest =>
      refine ⟨target, suffix, _, ideal, values, bindings, candidates, clock,
        enteredAt, rest, ?_⟩
      congr 1
      omega

theorem State.follows_sample_tail_of_lt {name : VarId} {payload : L.Ty}
    {fresh law} {tail : Graph Player L ((name, .pub payload) :: Γ) Δ}
    (base : Nat) (state : State Player L Δ)
    (follows : state.Follows (.sample name fresh law tail) base)
    (passed : base < state.publicView.pc) :
    state.Follows tail (base + 1) := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases walk with
  | refl => simp [State.publicView] at passed
  | sample rest =>
      refine ⟨target, suffix, _, ideal, values, bindings, candidates, clock,
        enteredAt, rest, ?_⟩
      congr 1
      omega

theorem State.follows_resolve_tail_of_lt {output binding : VarId} {owner : Player}
    {payload : L.Ty} {fresh source checks}
    {tail : Graph Player L ((output, .pub (IExpr.ResultTypes.result payload)) :: Γ) Δ}
    (base : Nat) (state : State Player L Δ)
    (follows : state.Follows
      (.resolve output owner binding fresh source checks tail) base)
    (passed : base < state.publicView.pc) :
    state.Follows tail (base + 1) := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases walk with
  | refl => simp [State.publicView] at passed
  | resolve rest =>
      refine ⟨target, suffix, _, ideal, values, bindings, candidates, clock,
        enteredAt, rest, ?_⟩
      congr 1
      omega

/-- Number of effective phases in a remaining typed graph. -/
def remainingPhases : {Γ Δ : VCtx Player L} → Graph Player L Γ Δ → Nat
  | _, _, .ret _ => 0
  | _, _, .sample _ _ _ next => remainingPhases next + 1
  | _, _, .bind _ _ _ next => remainingPhases next + 1
  | _, _, .resolve _ _ _ _ _ _ next => remainingPhases next + 1

/-- The public ordinal of a runtime state. -/
def State.phase : State Player L Δ → Nat
  | .running _ _ _ _ _ pc _ _ => pc

def State.endPhase : State Player L Δ → Nat
  | .running graph _ _ _ _ pc _ _ => pc + remainingPhases graph

@[simp] theorem State.phase_running {Γ : VCtx Player L}
    (graph : Graph Player L Γ Δ) (ideal : VEnv L Γ)
    (values : Graph.PublicValues Γ) (bindings : Bindings Player)
    (candidates : CommitmentCandidates Player Slot (Raw L))
    (pc clock enteredAt : Nat) :
    (State.running graph ideal values bindings candidates pc clock enteredAt).phase = pc := rfl

@[simp] theorem State.publicView_pc (state : State Player L Δ) :
    state.publicView.pc = state.phase := by
  cases state
  rfl

@[simp] theorem State.phase_initial (graph : Graph Player L Γ Δ) (input : VEnv L Γ) :
    (State.initial graph input).phase = 0 := rfl

@[simp] theorem State.endPhase_initial (graph : Graph Player L Γ Δ) (input : VEnv L Γ) :
    (State.initial graph input).endPhase = remainingPhases graph := by
  simp [State.initial, State.endPhase]

theorem State.phase_eq_endPhase_iff (state : State Player L Δ) :
    state.phase = state.endPhase ↔ state.outcome?.isSome = true := by
  cases state with
  | running graph =>
      cases graph <;> simp [State.phase, State.endPhase, remainingPhases, State.outcome?]

/-- Private candidate preparation does not move the public ordinal. -/
theorem privateStep_phase (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L) :
    (runtime.privateStep state who command).phase = state.phase := by
  cases state
  cases command <;> rfl

theorem privateStep_endPhase (runtime : GraphRuntime Player L Δ)
    (state : State Player L Δ) (who : Player) (command : PrivateCommand L) :
    (runtime.privateStep state who command).endPhase = state.endPhase := by
  cases state
  cases command <;> rfl

theorem privateStep_follows (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (base : Nat) (state : State Player L Δ)
    (who : Player) (command : PrivateCommand L) (follows : state.Follows whole base) :
    (runtime.privateStep state who command).Follows whole base := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases command <;>
    exact ⟨target, suffix, length, _, values, bindings, _, clock, enteredAt, walk, rfl⟩

/-- An accepted application packet advances exactly one graph phase. -/
theorem handle_phase (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ) (message : Message Player (Payload Player L))
    (accepted : runtime.handle state message = some next) :
    next.phase = state.phase + 1 := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
          cases graph with
          | ret => simp [handle] at accepted
          | sample => simp [handle] at accepted
          | bind name owner fresh tail =>
              cases payload <;> simp only [handle] at accepted
              · split_ifs at accepted
                cases accepted
                rfl
              all_goals contradiction
          | resolve output owner binding fresh source checks tail =>
              cases payload with
              | commitment | malformed => simp [handle] at accepted
              | opening site candidate raw =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases typed : raw.as? _ with
                  | none => rw [typed] at accepted; contradiction
                  | some encoded => rw [typed] at accepted; cases accepted; rfl
              | withhold site =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  rfl

theorem handle_endPhase (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ) (message : Message Player (Payload Player L))
    (accepted : runtime.handle state message = some next) :
    next.endPhase = state.endPhase := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases message with
      | mk id payload =>
          cases graph with
          | ret => simp [handle] at accepted
          | sample => simp [handle] at accepted
          | bind name owner fresh tail =>
              cases payload <;> simp only [handle] at accepted
              · split_ifs at accepted
                cases accepted
                simp [State.endPhase, remainingPhases, advanceBind]
                omega
              all_goals contradiction
          | resolve output owner binding fresh source checks tail =>
              cases payload with
              | commitment | malformed => simp [handle] at accepted
              | opening site candidate raw =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases typed : raw.as? _ with
                  | none => rw [typed] at accepted; contradiction
                  | some encoded =>
                      rw [typed] at accepted
                      cases accepted
                      simp [State.endPhase, remainingPhases, advanceResolve]
                      omega
              | withhold site =>
                  simp only [handle] at accepted
                  split_ifs at accepted
                  cases accepted
                  simp [State.endPhase, remainingPhases, advanceResolve]
                  omega

/-- Effective packet inclusion moves to the next typed suffix of the original
graph; rejected inclusion is handled as a stutter by the message application. -/
theorem handle_follows (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (base : Nat)
    (state next : State Player L Δ) (message : Message Player (Payload Player L))
    (follows : state.Follows whole base)
    (accepted : runtime.handle state message = some next) :
    next.Follows whole base := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases message with
  | mk id payload =>
      cases suffix with
      | ret => simp [handle] at accepted
      | sample => simp [handle] at accepted
      | bind name owner fresh tail =>
          rename_i payloadTy
          cases payload with
          | commitment site candidate =>
            simp only [handle] at accepted
            split_ifs at accepted
            cases accepted
            simp only [State.Follows, advanceBind]
            let stored : L.Val (IExpr.ResultTypes.result payloadTy) :=
              match candidates.lookup candidate with
              | .openable raw => (raw.as? (IExpr.ResultTypes.result payloadTy)).getD
                  ((IExpr.ResultTypes.valueEquiv payloadTy).symm .failure)
              | .fresh =>
                  (IExpr.ResultTypes.valueEquiv payloadTy).symm .failure
              | .unopenable =>
                  (IExpr.ResultTypes.valueEquiv payloadTy).symm .failure
            let nextValues : Graph.PublicValues
                ((name, .sealed owner (IExpr.ResultTypes.result payloadTy)) :: target) :=
              Graph.PublicValues.consSealed values
            refine ⟨_, tail, length + 1, VEnv.cons stored ideal,
              nextValues, (name, candidate) :: bindings,
              candidates.accept candidate, clock, clock, ?_, ?_⟩
            · exact walk.trans (.bind (.refl tail))
            · simp only [State.running.injEq, heq_eq_eq, and_self, and_true, true_and]
              refine ⟨VEnv.cons_ext rfl rfl, ?_, by omega⟩
              rfl
          | opening | withhold | malformed => simp [handle] at accepted
      | resolve output owner binding fresh source checks tail =>
          rename_i payloadTy
          cases payload with
          | commitment | malformed => simp [handle] at accepted
          | opening site candidate raw =>
              simp only [handle] at accepted
              split_ifs at accepted
              cases typed : raw.as? _ with
              | none => rw [typed] at accepted; contradiction
              | some encoded =>
                  rw [typed] at accepted
                  cases accepted
                  simp only [State.Follows, advanceResolve]
                  let result := Graph.acceptedProposal checks values
                    (IExpr.ResultTypes.valueEquiv payloadTy encoded)
                  let stored := (IExpr.ResultTypes.valueEquiv payloadTy).symm result
                  refine ⟨_, tail, length + 1, VEnv.cons stored ideal,
                    (Graph.PublicValues.consPublic (name := output) stored values),
                    bindings, candidates,
                    clock, clock, ?_, ?_⟩
                  · exact walk.trans (.resolve (.refl tail))
                  · simp [result, stored, Nat.add_assoc]
          | withhold site =>
              simp only [handle] at accepted
              split_ifs at accepted
              cases accepted
              simp only [State.Follows, advanceResolve]
              let stored := (IExpr.ResultTypes.valueEquiv payloadTy).symm
                (PublicationResult.failure)
              refine ⟨_, tail, length + 1, VEnv.cons stored ideal,
                (Graph.PublicValues.consPublic (name := output) stored values),
                bindings, candidates,
                clock, clock, ?_, ?_⟩
              · exact walk.trans (.resolve (.refl tail))
              · simp [stored, Nat.add_assoc]

/-- A progress tick never decreases the phase, and a nonterminal tick either
advances its phase or increments the application clock in place. -/
theorem tick_phase_mono (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ)
    (supported : next ∈ (runtime.tick state).support) :
    state.phase ≤ next.phase := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph <;>
        simp only [tick] at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        exact Nat.le_refl _
      · simp only [FinDist.support_map, Set.mem_image] at supported
        obtain ⟨value, _, rfl⟩ := supported
        simp
      all_goals
        split at supported <;>
          simp only [FinDist.mem_support_pure] at supported <;>
          subst next <;> simp [advanceBindFailure, advanceResolve]

theorem tick_endPhase (runtime : GraphRuntime Player L Δ)
    (state next : State Player L Δ)
    (supported : next ∈ (runtime.tick state).support) :
    next.endPhase = state.endPhase := by
  cases state with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph <;> simp only [tick] at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        rfl
      · simp only [FinDist.support_map, Set.mem_image] at supported
        obtain ⟨value, _, rfl⟩ := supported
        simp [State.endPhase, remainingPhases]
        omega
      all_goals
        split at supported <;>
          simp only [FinDist.mem_support_pure] at supported <;>
          subst next <;>
          simp [State.endPhase, remainingPhases, advanceBindFailure, advanceResolve]
      all_goals omega

/-- Progress ticks also preserve the genuine typed-suffix witness. -/
theorem tick_follows (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (base : Nat)
    (state next : State Player L Δ) (follows : state.Follows whole base)
    (supported : next ∈ (runtime.tick state).support) :
    next.Follows whole base := by
  rcases follows with
    ⟨target, suffix, length, ideal, values, bindings, candidates, clock,
      enteredAt, walk, rfl⟩
  cases suffix with
  | ret =>
      simp only [tick, FinDist.mem_support_pure] at supported
      subst next
      exact ⟨_, _, length, ideal, values, bindings, candidates, clock + 1,
        enteredAt, walk, rfl⟩
  | sample name fresh law tail =>
      simp only [tick, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨value, _, rfl⟩ := supported
      refine ⟨_, tail, length + 1, VEnv.cons value ideal,
        (Graph.PublicValues.consPublic (name := name) value values), bindings,
        candidates, clock + 1, clock + 1, ?_, ?_⟩
      · exact walk.trans (.sample (.refl tail))
      · simp [Nat.add_assoc]
  | bind name owner fresh tail =>
      rename_i payloadTy
      simp only [tick] at supported
      split at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        let failed := (IExpr.ResultTypes.valueEquiv payloadTy).symm
          (PublicationResult.failure)
        refine ⟨_, tail, length + 1, VEnv.cons failed ideal,
          (Graph.PublicValues.consSealed (name := name) (owner := owner) values),
          bindings, candidates, clock + 1, clock + 1, ?_, ?_⟩
        · exact walk.trans (.bind (.refl tail))
        · simp [advanceBindFailure, failed, Nat.add_assoc]
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        exact ⟨_, _, length, ideal, values, bindings, candidates, clock + 1,
          enteredAt, walk, rfl⟩
  | resolve output owner binding fresh source checks tail =>
      rename_i payloadTy
      simp only [tick] at supported
      split at supported
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        let failed := (IExpr.ResultTypes.valueEquiv payloadTy).symm
          (PublicationResult.failure)
        refine ⟨_, tail, length + 1, VEnv.cons failed ideal,
          (Graph.PublicValues.consPublic (name := output) failed values),
          bindings, candidates, clock + 1, clock + 1, ?_, ?_⟩
        · exact walk.trans (.resolve (.refl tail))
        · simp [advanceResolve, failed, Nat.add_assoc]
      · simp only [FinDist.mem_support_pure] at supported
        subst next
        exact ⟨_, _, length, ideal, values, bindings, candidates, clock + 1,
          enteredAt, walk, rfl⟩

/-- Every native application action preserves or advances the graph ordinal. -/
theorem application_step_phase_mono (runtime : GraphRuntime Player L Δ)
    (state next : runtime.application.State) (action : runtime.application.Action)
    (supported : next ∈ (runtime.application.step state action).support) :
    state.application.phase ≤ next.application.phase := by
  cases action with
  | environment command =>
      cases command
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨application, happened, rfl⟩ := supported
      exact runtime.tick_phase_mono _ _ happened
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      change state.application.phase ≤
        (runtime.privateStep state.application who command).phase
      rw [runtime.privateStep_phase]
  | submit | replay | deliver =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      exact Nat.le_refl _
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      apply runtime.application.includePending_application_invariant
        (fun application => state.application.phase ≤ application.phase)
        ?_ state id (Nat.le_refl _)
      intro before message after hbefore accepted
      have hphase := runtime.handle_phase before after message accepted
      omega

theorem application_step_endPhase (runtime : GraphRuntime Player L Δ)
    (state next : runtime.application.State) (action : runtime.application.Action)
    (supported : next ∈ (runtime.application.step state action).support) :
    next.application.endPhase = state.application.endPhase := by
  cases action with
  | environment command =>
      cases command
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨application, happened, rfl⟩ := supported
      exact runtime.tick_endPhase _ _ happened
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      change (runtime.privateStep state.application who command).endPhase =
        state.application.endPhase
      exact runtime.privateStep_endPhase _ _ _
  | submit | replay | deliver =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      rfl
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      apply runtime.application.includePending_application_invariant
        (fun application => application.endPhase = state.application.endPhase)
        ?_ state id rfl
      intro before message after hbefore accepted
      exact (runtime.handle_endPhase before after message accepted).trans hbefore

theorem application_step_follows (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (base : Nat)
    (state next : runtime.application.State) (action : runtime.application.Action)
    (follows : state.application.Follows whole base)
    (supported : next ∈ (runtime.application.step state action).support) :
    next.application.Follows whole base := by
  cases action with
  | environment command =>
      cases command
      simp only [MessageApplication.step, FinDist.support_map, Set.mem_image] at supported
      obtain ⟨application, happened, rfl⟩ := supported
      exact runtime.tick_follows whole base _ _ follows happened
  | privateCommand who command =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      exact runtime.privateStep_follows whole base _ who command follows
  | submit | replay | deliver =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      exact follows
  | «include» id =>
      simp only [MessageApplication.step, FinDist.mem_support_pure] at supported
      subst next
      apply runtime.application.includePending_application_invariant
        (fun application => application.Follows whole base)
        ?_ state id follows
      intro before message after hbefore accepted
      exact runtime.handle_follows whole base before after message hbefore accepted

/-- Monotonicity extends to arbitrary native action lists. -/
theorem application_run_phase_mono (runtime : GraphRuntime Player L Δ)
    (actions : List runtime.application.Action)
    (state next : runtime.application.State)
    (supported : next ∈ (runtime.application.run actions state).support) :
    state.application.phase ≤ next.application.phase := by
  induction actions generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil, FinDist.mem_support_pure] at supported
      subst next
      exact Nat.le_refl _
  | cons action rest ih =>
      simp only [MessageApplication.run_cons, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨middle, hmiddle, hnext⟩ := supported
      exact (runtime.application_step_phase_mono state middle action hmiddle).trans
        (ih middle hnext)

theorem application_run_endPhase (runtime : GraphRuntime Player L Δ)
    (actions : List runtime.application.Action)
    (state next : runtime.application.State)
    (supported : next ∈ (runtime.application.run actions state).support) :
    next.application.endPhase = state.application.endPhase := by
  induction actions generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil, FinDist.mem_support_pure] at supported
      subst next
      rfl
  | cons action rest ih =>
      simp only [MessageApplication.run_cons, FinDist.support_bind,
        Set.mem_iUnion] at supported
      obtain ⟨middle, hmiddle, hnext⟩ := supported
      exact (ih middle hnext).trans
        (runtime.application_step_endPhase state middle action hmiddle)

theorem application_run_follows (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (base : Nat)
    (actions : List runtime.application.Action)
    (state next : runtime.application.State)
    (follows : state.application.Follows whole base)
    (supported : next ∈ (runtime.application.run actions state).support) :
    next.application.Follows whole base := by
  induction actions generalizing state with
  | nil =>
      simp only [MessageApplication.run_nil, FinDist.mem_support_pure] at supported
      subst next
      exact follows
  | cons action rest ih =>
      simp only [MessageApplication.run_cons, FinDist.support_bind, Set.mem_iUnion] at supported
      obtain ⟨middle, hmiddle, hnext⟩ := supported
      exact ih middle (runtime.application_step_follows whole base state middle
        action follows hmiddle) hnext

/-- In particular, the actual shared policy runner is phase-monotone for
arbitrary player and environment policies. -/
theorem runPolicies_phase_mono (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    execution.native.application.phase ≤ next.native.application.phase := by
  obtain ⟨suffix, _htrace, hrun⟩ :=
    runtime.application.runPolicies_native_support players environment schedule
      execution next supported
  exact runtime.application_run_phase_mono suffix execution.native next.native hrun

theorem runPolicies_endPhase (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    next.native.application.endPhase = execution.native.application.endPhase := by
  obtain ⟨suffix, _htrace, hrun⟩ :=
    runtime.application.runPolicies_native_support players environment schedule
      execution next supported
  exact runtime.application_run_endPhase suffix execution.native next.native hrun

theorem runPolicies_follows (runtime : GraphRuntime Player L Δ)
    (whole : Graph Player L Γ Δ) (base : Nat)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (follows : execution.native.application.Follows whole base)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support) :
    next.native.application.Follows whole base := by
  obtain ⟨suffix, _htrace, hrun⟩ :=
    runtime.application.runPolicies_native_support players environment schedule
      execution next supported
  exact runtime.application_run_follows whole base suffix execution.native next.native
    follows hrun

/-- Any policy run which reaches its fixed end ordinal is terminal.  The
premise is deliberately an inequality: phase monotonicity and end-ordinal
preservation rule out overshooting for executions originating in a graph. -/
theorem runPolicies_completed_of_endPhase_le_phase
    (runtime : GraphRuntime Player L Δ)
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@MessageApplication.Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (supported : next ∈ (runtime.application.runPolicies players environment
      schedule execution).support)
    (reached : execution.native.application.endPhase ≤
      next.native.application.phase) :
    next.native.application.outcome?.isSome = true := by
  have hend := runtime.runPolicies_endPhase players environment schedule
    execution next supported
  have hphaseEnd : next.native.application.phase =
      next.native.application.endPhase := by
    rw [hend]
    have bounded : next.native.application.phase ≤
        next.native.application.endPhase := by
      cases next.native.application with
      | running graph =>
          simp [State.phase, State.endPhase]
    omega
  exact (State.phase_eq_endPhase_iff next.native.application).mp hphaseEnd

end Vegas.GraphRuntime
