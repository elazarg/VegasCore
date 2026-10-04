/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveAuditCollection
import Interaction.ReactiveNormalHistory
import Interaction.ReactiveResponseMenu

/-! # Reconstructing the traffic audit from existing service recall

The final reactive state already retains the scheduler's public observations.
Consecutive observations, followed by the final public view, recover exactly
the transmission records of the complete protocol history. Activation changes
only private knowledge; every other service operation emits no network input.

This is a readout of existing state, not extra memory or an observation exposed
to players. It allows terminal audit utilities to use the checked state-based
private-alias equilibrium theorem. Implementing an authentic partial audit of
this ideal record remains a separate service obligation.
-/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] (app : ReactiveApplication Principal)

def trafficBetween (before after : app.EnvironmentView) : List app.TrafficRecord :=
  (after.network.inputs.drop before.network.inputs.length).map fun input =>
    ⟨before.application, before.network.ledger, input⟩

omit [DecidableEq Principal] in
theorem trafficBetween_self (view : app.EnvironmentView) :
    app.trafficBetween view view = [] := by
  simp [trafficBetween]

/-- Read adjacent public snapshots; the final view closes the last interval. -/
def trafficViews : List app.EnvironmentView → app.EnvironmentView → List app.TrafficRecord
  | [], _ => []
  | before :: rest, final =>
      app.trafficBetween before (rest.head?.getD final) ++ trafficViews rest final

omit [DecidableEq Principal] in
theorem trafficViews_append (past : List app.EnvironmentView)
    (current final : app.EnvironmentView) :
    app.trafficViews (past ++ [current]) final =
      app.trafficViews past current ++ app.trafficBetween current final := by
  induction past with
  | nil => simp [trafficViews]
  | cons before past ih =>
      cases past with
      | nil => simp [trafficViews]
      | cons next tail => simpa [trafficViews, List.append_assoc] using ih

def executionTraffic (execution : app.Execution) : List app.TrafficRecord :=
  app.trafficViews (execution.environmentRecall.map EnvironmentEntry.beforeView)
    (execution.observeEnvironment app)

def stateTraffic : app.ProtocolState → List app.TrafficRecord
  | none => []
  | some control => app.executionTraffic control.execution

/-- Service operations change delivery and application state, but do not
invent player transmissions. -/
theorem environmentStep_inputs (execution next : app.Execution) (command : app.Command)
    (moved : next ∈ (execution.environmentStep app command).support) :
    next.network.inputs = execution.network.inputs := by
  cases command with
  | wait =>
      simp only [Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rfl
  | activate who =>
      simp only [Execution.environmentStep, PMF.map_comp] at moved
      obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ moved
      rfl
  | application operation =>
      simp only [Execution.environmentStep, PMF.map_comp] at moved
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ moved
      rfl
  | «include» id =>
      simp only [Execution.environmentStep, PMF.pure_map] at moved
      cases (PMF.mem_support_pure_iff _ _).mp moved
      simp only [Execution.includePending, MessageNetwork.includePending]
      cases execution.network.lookup id <;> rfl

private theorem transition_traffic_inputs
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    before.elim [] (fun control => control.execution.network.inputs) ++
        (app.trafficStep before after).map TrafficRecord.input =
      after.elim [] (fun control => control.execution.network.inputs) := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          clear reached
          rcases (joint who).getD ⟨none⟩ with ⟨transmission⟩
          cases transmission with
          | none => simp [trafficStep, Execution.respond]
          | some transmission =>
              cases transmission with
              | submit submission => simp [trafficStep, Execution.respond, MessageNetwork.submit]
              | replay id =>
                  simp only [trafficStep, Execution.respond, MessageNetwork.replay]
                  split <;> simp
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              simp [trafficStep]
          | succ remaining =>
              obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp
                (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
              rw [app.trafficStep_environment execution next command moved remaining]
              simpa using (app.environmentStep_inputs execution next command moved).symm

private theorem trafficAudit_inputs
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {state : app.ProtocolState} (trace : (app.protocol initial horizon scheduler).Trace state),
      (app.trafficAudit initial horizon scheduler trace).map TrafficRecord.input =
        state.elim [] (fun control => control.execution.network.inputs)
  | _, .start => rfl
  | _, .extend prior joint _legal reached => by
      rw [trafficAudit, List.map_append, trafficAudit_inputs initial horizon scheduler prior]
      exact app.transition_traffic_inputs initial horizon scheduler _ _ joint reached

private def trafficReady : app.ProtocolState → Prop
  | none => True
  | some control => control.actor.isSome →
      ∃ past, control.execution.environmentRecall.map EnvironmentEntry.beforeView =
        past ++ [control.execution.observeEnvironment app]

private theorem traffic_transition
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (before after : app.ProtocolState) (joint : Principal → Option app.Action)
    (ready : app.trafficReady before)
    (reached : after ∈ (app.transition initial horizon scheduler before joint).support) :
    app.stateTraffic after = app.stateTraffic before ++ app.trafficStep before after ∧
      app.trafficReady after := by
  cases before with
  | none =>
      obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ reached
      exact ⟨rfl, by simp [trafficReady]⟩
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          cases (PMF.mem_support_pure_iff _ _).mp reached
          obtain ⟨past, remembered⟩ := ready (by simp)
          refine ⟨?_, by simp [trafficReady]⟩
          simp only [stateTraffic, executionTraffic, app.respond_environmentRecall, remembered,
            trafficViews_append, trafficBetween_self, List.append_nil]
          rfl
      | none =>
          cases remaining with
          | zero =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              refine ⟨?_, ready⟩
              simp [trafficStep]
          | succ remaining =>
              obtain ⟨command, _, supported⟩ := Set.mem_iUnion₂.mp
                (PMF.support_bind .. ▸ reached)
              obtain ⟨next, moved, rfl⟩ := PMF.support_map .. ▸ supported
              have recorded : next.environmentRecall = execution.environmentRecall ++
                  [⟨execution.observeEnvironment app, command⟩] := by
                obtain ⟨raw, _, rfl⟩ := PMF.support_map .. ▸ moved
                rfl
              have noTraffic := app.trafficStep_environment execution next command moved remaining
              have sameInputs := app.environmentStep_inputs execution next command moved
              refine ⟨?_, ?_⟩
              · rw [noTraffic, List.append_nil]
                simp only [stateTraffic, executionTraffic, recorded, List.map_append,
                  List.map_cons, List.map_nil, trafficViews_append]
                have empty : app.trafficBetween (execution.observeEnvironment app)
                    (next.observeEnvironment app) = [] := by
                  simp [trafficBetween, Execution.observeEnvironment, MessageNetwork.publicView,
                    sameInputs]
                rw [empty, List.append_nil]
              · cases command with
                | wait => simp [trafficReady, Command.actor?]
                | «include» id => simp [trafficReady, Command.actor?]
                | application operation => simp [trafficReady, Command.actor?]
                | activate who =>
                    intro _active
                    refine ⟨execution.environmentRecall.map EnvironmentEntry.beforeView, ?_⟩
                    rw [recorded, List.map_append]
                    congr 1
                    simp only [Execution.environmentStep, PMF.map_comp] at moved
                    obtain ⟨selected, _, rfl⟩ := PMF.support_map .. ▸ moved
                    rfl

private theorem traffic_invariant
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler) :
    ∀ {state : app.ProtocolState} (trace : (app.protocol initial horizon scheduler).Trace state),
      app.trafficAudit initial horizon scheduler trace = app.stateTraffic state ∧
        app.trafficReady state
  | _, .start => ⟨rfl, trivial⟩
  | _, .extend prior joint _legal reached => by
      have ih := traffic_invariant initial horizon scheduler prior
      obtain ⟨law, ready⟩ := app.traffic_transition initial horizon scheduler _ _ joint ih.2 reached
      exact ⟨by rw [trafficAudit, ih.1, law], ready⟩

/-- The history audit factors through the actual final state at every legal
prefix, including a response with no subsequent service operation. -/
theorem trafficAudit_eq_stateTraffic
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state : app.ProtocolState} (trace : (app.protocol initial horizon scheduler).Trace state) :
    app.trafficAudit initial horizon scheduler trace = app.stateTraffic state :=
  (app.traffic_invariant initial horizon scheduler trace).1

/-- Every input of an actual execution has exactly its corresponding audit
record. This includes rebroadcasts, with their original multiplicity and order. -/
theorem stateTraffic_inputs
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {state : app.ProtocolState} (trace : (app.protocol initial horizon scheduler).Trace state) :
    (app.stateTraffic state).map TrafficRecord.input =
      state.elim [] (fun control => control.execution.network.inputs) := by
  rw [← app.trafficAudit_eq_stateTraffic initial horizon scheduler trace]
  exact app.trafficAudit_inputs initial horizon scheduler trace

/-- Actual transmissions append their records to the state readout as well as
to the history readout. No obedience or eventual settlement is required. -/
theorem stateTraffic_transition
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (history : (app.protocol initial horizon scheduler).History)
    (joint : Principal → Option app.Action) (next : app.ProtocolState)
    (reached : next ∈ (app.transition initial horizon scheduler history.state joint).support) :
    app.stateTraffic next = app.stateTraffic history.state ++
      app.trafficStep history.state next :=
  (app.traffic_transition initial horizon scheduler history.state next joint
    (app.traffic_invariant initial horizon scheduler history.trace).2 reached).1

omit [DecidableEq Principal] in
/-- Ineffective private response representations leave the entire traffic
audit unchanged, so audit utility may use the existing state-payoff SE lift. -/
theorem stateTraffic_normalization (normal : app.SubmissionNormalization)
    (state : app.ProtocolState) :
    app.stateTraffic (normal.state state) = app.stateTraffic state := by
  cases state <;> rfl

namespace ResponseMenu

variable {app} (menu : app.ResponseMenu)

theorem trafficAudit_eq_stateTraffic
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    (history : (menu.protocol initial horizon scheduler).History) :
    menu.trafficAudit initial horizon scheduler history = app.stateTraffic history.state :=
  app.trafficAudit_eq_stateTraffic initial horizon scheduler _

end ResponseMenu

end Interaction.ReactiveApplication
