/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeResponse
import Vegas.Pending.NativeProtocolTermination

/-! # Native service with uninterrupted responses as strategic actions

One response consumes the maximal consecutive run of calls to its owner.
Every environment instruction and intervening player is a boundary. The
information model retains the original native input; its menu requires a
proof that the response capacity is determined by that input. A hidden
service suffix is never supplied to a policy to discharge that obligation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def responseLength (who : Player) : List (ServiceInstruction graph) → Nat
  | .player actor :: rest => if actor = who then responseLength who rest + 1 else 0
  | _ => 0

theorem responseLength_le (who : Player) (plan : List (ServiceInstruction graph)) :
    responseLength who plan ≤ plan.length := by
  induction plan with
  | nil => exact Nat.le_refl _
  | cons instruction rest ih =>
      cases instruction <;> simp only [responseLength, List.length_cons]
      all_goals first | omega | split <;> omega

/-- Expanding a response recovers exactly the consumed prefix. It cannot
swallow a wire, clock, application instruction, or another player's call. -/
theorem responseLength_prefix (who : Player) (plan : List (ServiceInstruction graph)) :
    List.replicate (responseLength who plan) (.player who) ++
        plan.drop (responseLength who plan) = plan := by
  induction plan with
  | nil => rfl
  | cons instruction rest ih =>
      cases instruction with
      | player actor =>
          by_cases same : actor = who
          · subst actor
            simp only [responseLength, ↓reduceIte, List.replicate_succ, List.drop_succ_cons,
              List.cons_append, ih]
          · simp only [responseLength, ite_eq_right same, List.replicate_zero, List.drop_zero,
              List.nil_append]
      | wire | grant event | includeLatest event owner | sample event | tick | expire event => rfl

def responseCount (runtime : EventGraphRuntime graph) : NativeProtocolState runtime → Nat
  | some ⟨_, .player who :: rest, _⟩ => responseLength who (.player who :: rest)
  | _ => 0

def responseTransition (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (state : NativeProtocolState runtime) (joint : Player → Option (List (PlayerAction graph))) :
    FinDist (NativeProtocolState runtime) :=
  match state with
  | some ⟨epochs, .player who :: rest, execution⟩ =>
      FinDist.pure (some ⟨epochs,
        (.player who :: rest).drop (responseLength who (.player who :: rest)),
        runtime.takeActions who execution ((joint who).getD [])⟩)
  | _ => runtime.nativeTransition inputs roster reactionRounds wire order state (fun _ => none)

def responseProtocol (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ExecutionProtocol Player where
  State := NativeProtocolState runtime
  Action _ := List (PlayerAction graph)
  init := none
  active state who := runtime.nativeActor state = some who
  available state _ := {actions | actions.length = runtime.responseCount state}
  terminal := runtime.nativeTerminal
  step state joint :=
    runtime.responseTransition inputs roster reactionRounds wire order state joint.1
  progress state _ := by
    refine ⟨fun who => if runtime.nativeActor state = some who then
      some (List.replicate (runtime.responseCount state) PlayerAction.wait) else none, ?_⟩
    intro who
    by_cases acts : runtime.nativeActor state = some who <;> simp [acts]

theorem response_singleMover (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (state : NativeProtocolState runtime) {first second : Player}
    (firstActs : (runtime.responseProtocol inputs roster reactionRounds wire order).active
      state first)
    (secondActs : (runtime.responseProtocol inputs roster reactionRounds wire order).active
      state second) : first = second := Option.some.inj (firstActs.symm.trans secondActs)

def responseSignals (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    InfoSignals (runtime.responseProtocol inputs roster reactionRounds wire order) where
  PublicSignal := Unit
  PrivateSignal _ := NativeInfo graph
  initialPublic := ()
  initialPrivate _ := none
  publicSignal _ := ()
  privateSignal who event := runtime.nativeObserve who event.target
  InfoState _ := NativeInfo graph
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

theorem response_info (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) (who : Player) :
    ∀ {state}
      (trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state),
      (runtime.responseSignals inputs roster reactionRounds wire order).infoOf who trace =
        runtime.nativeObserve who state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

/-- The response budget must be computable from the original native input at
every legal response entry, including off-path histories. -/
def ResponseBudgetAdequate (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (budget : Player → NativeInput graph → Nat) : Prop :=
  ∀ (history : (runtime.responseProtocol inputs roster reactionRounds wire order).History)
    (who : Player) (input : NativeInput graph),
    runtime.nativeObserve who history.state = some input →
      budget who input = runtime.responseCount history.state

def responseInformation (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (budget : Player → NativeInput graph → Nat)
    (adequate : runtime.ResponseBudgetAdequate inputs roster reactionRounds wire order budget) :
    InformationModel (runtime.responseProtocol inputs roster reactionRounds wire order) where
  toInfoSignals := runtime.responseSignals inputs roster reactionRounds wire order
  menu who info := {choice | match info, choice with
    | none, none => True
    | some input, some actions => actions.length = budget who input
    | _, _ => False}
  menu_adequate := by
    intro who state trace choice
    rw [runtime.response_info inputs roster reactionRounds wire order who trace]
    have active := runtime.nativeObserve_isSome who state
    cases observed : runtime.nativeObserve who state with
    | none => cases choice <;> simp_all [LegalOption, responseProtocol]
    | some input =>
        have count := adequate ⟨state, trace⟩ who input observed
        cases choice <;> simp_all [LegalOption, responseProtocol]

theorem responseRemaining_step (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy)
    (before after : NativeProtocolState runtime)
    (joint : Player → Option (List (PlayerAction graph)))
    (running : ¬ runtime.nativeTerminal before)
    (reached : after ∈
      (runtime.responseTransition inputs roster reactionRounds wire order before joint).support) :
    runtime.nativeRemaining roster reactionRounds after <
      runtime.nativeRemaining roster reactionRounds before := by
  cases before with
  | none =>
      have consumed := runtime.nativeRemaining_step inputs roster reactionRounds wire order
        none after (fun _ => none) running reached
      omega
  | some control =>
      rcases control with ⟨epochs, plan, execution⟩
      cases plan with
      | nil =>
          have consumed := runtime.nativeRemaining_step inputs roster reactionRounds wire order
            (some ⟨epochs, [], execution⟩) after (fun _ => none) running reached
          omega
      | cons instruction rest =>
          cases instruction with
          | player who =>
              cases FinDist.mem_support_pure.mp reached
              have bound := responseLength_le who (ServiceInstruction.player who :: rest)
              simp only [responseLength, ↓reduceIte, List.length_cons] at bound
              simp only [nativeRemaining, List.length_drop, List.length_cons,
                responseLength, ↓reduceIte]
              omega
          | wire | grant event | includeLatest event owner | sample event | tick | expire event =>
              have consumed := runtime.nativeRemaining_step inputs roster reactionRounds wire order
                _ after (fun _ => none) running reached
              omega

theorem response_terminates (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.responseProtocol inputs roster reactionRounds wire order).WellFoundedPlay := by
  apply wellFoundedPlay_of_rank (runtime.nativeRemaining roster reactionRounds)
  intro before after transition
  obtain ⟨joint, legal, reached⟩ := transition
  exact runtime.responseRemaining_step inputs roster reactionRounds wire order
    before after joint legal.1 reached

theorem response_history_bound (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    ∀ {state}
      (trace : (runtime.responseProtocol inputs roster reactionRounds wire order).Trace state),
      trace.length + runtime.nativeRemaining roster reactionRounds state ≤
        runtime.nativeRemaining roster reactionRounds none
  | _, .start => by simp only [Trace.length, responseProtocol, Nat.zero_add, le_refl]
  | _, .extend prior joint legal reached => by
      have priorBound :=
        runtime.response_history_bound inputs roster reactionRounds wire order prior
      have decreases := runtime.responseRemaining_step inputs roster reactionRounds wire order
        _ _ joint legal.1 reached
      simp only [Trace.length]
      omega

theorem response_bounded (runtime : EventGraphRuntime graph)
    (inputs : FinDist graph.Inputs) (roster : List Player) (reactionRounds : Nat)
    (wire : runtime.application.WirePolicy) (order : runtime.ServiceOrderPolicy) :
    (runtime.responseProtocol inputs roster reactionRounds wire order).BoundedHorizon
      (runtime.nativeRemaining roster reactionRounds none) := by
  intro state trace enough
  have bound := runtime.response_history_bound inputs roster reactionRounds wire order trace
  exact (runtime.nativeRemaining_zero roster reactionRounds state).mp (by omega)

end Vegas.EventGraphRuntime
