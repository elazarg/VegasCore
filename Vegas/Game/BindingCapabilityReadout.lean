/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.BindingFrameSettlement

/-! # Full typed readout of a private capability reconstruction

A private reconstruction that remembers candidates and responses, but changes
no typed field value, preserves the complete typed source readout. The owner
may retain a different raw capability; every field's actual value agrees.
Consequently arbitrary typed source utility and the joint actual terminal
audit settlement agree on such frames.

This is a kernel for replacing unusable private binding material by canonical
failure. It assumes a preserved concrete frame and explicitly excludes typed
value overrides. Closure under raw continuations until a forbidden capability
packet or public miss is a separate obligation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingMemory.Frame

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {memory : BindingMemory runtime leaks} {owner : Player}
  {original repaired : (runtime.reactiveApplication leaks).Execution}

/-- Candidate reconstruction alone cannot change any typed field, including
private bindings and initial parameters. Every field is visible to an owner,
and the frame preserves that owner's observation or reconstructs it without
overriding its typed values. -/
theorem store_eq_of_no_value_overrides
    (frame : Frame runtime leaks memory owner original repaired)
    (noValues : ∀ field, memory.shadow.values field = none) :
    original.application.config.store = repaired.application.config.store := by
  have shadowStore (store : Store graph.layout) : memory.shadow.store store = store := by
    funext field
    simp only [BindingShadow.store, noValues, Option.getD_none]
    cases store field <;> rfl
  have seen (observer : Player) (field : graph.Field)
      (visible : graph.fieldVisibleTo observer field) :
      original.application.config.store field = repaired.application.config.store field := by
    by_cases own : observer = owner
    · subst observer
      have stored := congrFun (congrArg
        (fun view : (runtime.reactiveApplication leaks).PlayerView =>
          view.application.observation.store) frame.observed) field
      change memory.shadow.store (graph.playerObserve owner repaired.application.config).store
          field = (graph.playerObserve owner original.application.config).store field at stored
      rw [shadowStore] at stored
      simpa only [playerObserve, playerStore_of_visible, visible] using stored.symm
    · have stored := congrFun (congrArg
        (fun view : PlayerView graph => view.observation.store) (frame.views observer own)) field
      simpa only [State.playerView, playerObserve, playerStore_of_visible, visible] using stored
  funext field
  have observable : ∃ observer, graph.fieldVisibleTo observer field := by
    cases layout : graph.layout field with
    | publicData payload | publication payload =>
        refine ⟨owner, ?_⟩
        change (graph.layout field).VisibleTo owner
        rw [layout]
        trivial
    | privateInput observer payload | binding observer payload =>
        refine ⟨observer, ?_⟩
        change (graph.layout field).VisibleTo observer
        rw [layout]
        rfl
  obtain ⟨observer, visible⟩ := observable
  exact seen observer field visible

end Vegas.EventGraphRuntime.BindingMemory.Frame

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Enforcement
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The complete typed source readout agrees, with no restriction on future
private binding values in utility. Unfinished readouts agree as well. -/
theorem bindingCapabilityFrame_sourceReadout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Control)
    (frame : memory.Frame (runtime setup) leaks owner original.execution repaired.execution)
    (noValues : ∀ field, memory.shadow.values field = none) :
    sourceReadout setup leaks (some original) = sourceReadout setup leaks (some repaired) := by
  have observations := congrArg (PublicView.observation (graph := graph setup)) frame.publicView
  have orders := congrArg EventGraph.PublicObservation.completionOrder observations
  have completed := EventGraph.cut_eq_of_completionOrder_eq
    original.execution.application.config repaired.execution.application.config orders
  have terminal : original.execution.application.config.cut.Terminal ↔
      repaired.execution.application.config.cut.Terminal := by
    unfold EventOrder.Cut.Terminal
    rw [completed]
  have stores := frame.store_eq_of_no_value_overrides noValues
  unfold sourceReadout
  simp only [Option.bind_some]
  by_cases done : original.execution.application.config.cut.Terminal
  · rw [ite_eq_left done, ite_eq_left (terminal.mp done), stores]
  · rw [ite_eq_right done, ite_eq_right (fun h => done (terminal.mpr h))]

/-- Arbitrary utility of the full terminal source state is preserved by a
candidate-only frame. No parameter/public-outcome factorization is required. -/
theorem bindingCapabilityFrame_baseUtility
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Control)
    (frame : memory.Frame (runtime setup) leaks owner original.execution repaired.execution)
    (noValues : ∀ field, memory.shadow.values field = none) :
    baseUtility setup leaks utility (some original) =
      baseUtility setup leaks utility (some repaired) := by
  unfold baseUtility
  rw [bindingCapabilityFrame_sourceReadout setup leaks owner memory original repaired frame
    noValues]

/-- The actual audit receives equal traffic and equal final records. Thus
both expected utility and the same sampled payoff vector agree, including
any earlier charges, for arbitrary full typed source utility. -/
theorem bindingCapabilityFrame_auditedSettlement
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (trafficAudit : SettledRecord (graph setup) →
      List (application setup leaks).TrafficRecord → PMF (Player → Bool))
    (deposit : Player → ℝ) (owner : Player) (memory : BindingMemory (runtime setup) leaks)
    (original repaired : (application setup leaks).Control)
    (frame : memory.Frame (runtime setup) leaks owner original.execution repaired.execution)
    (noValues : ∀ field, memory.shadow.values field = none) :
    let base := baseUtility setup leaks utility
    let observe := (runtime setup).serviceAuditObservation leaks
    let audit := (runtime setup).serviceAudit leaks trafficAudit
    TerminalAudit.utility base observe audit deposit (some original) =
        TerminalAudit.utility base observe audit deposit (some repaired) ∧
      TerminalAudit.settlement base observe audit deposit (some original) =
        TerminalAudit.settlement base observe audit deposit (some repaired) := by
  intro base observe audit
  have baseEq := bindingCapabilityFrame_baseUtility setup leaks utility owner memory original
    repaired frame noValues
  have observed := BindingMemory.Frame.serviceAuditObservation_eq original repaired frame
  change base (some original) = base (some repaired) at baseEq
  change observe (some original) = observe (some repaired) at observed
  constructor
  · funext who
    simp only [TerminalAudit.utility, TerminalAudit.charge, baseEq, observed]
  · simp only [TerminalAudit.settlement, baseEq, observed]

/-- A supported candidate-only coupling preserves the joint full typed source
readout and realized audited payoff vector, rather than just their marginals.
The supplied frame is an operational obligation, not a continuation theorem. -/
theorem bindingCapabilityFrame_joint_settlement_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (utility : State L setup.program.terminalCtx → Player → ℝ)
    (trafficAudit : SettledRecord (graph setup) →
      List (application setup leaks).TrafficRecord → PMF (Player → Bool))
    (deposit : Player → ℝ) (owner : Player)
    (coupled : PMF ((application setup leaks).Control ×
      (application setup leaks).Control × BindingMemory (runtime setup) leaks))
    (framed : ∀ pair ∈ coupled.support,
      pair.2.2.Frame (runtime setup) leaks owner pair.1.execution pair.2.1.execution)
    (noValues : ∀ pair ∈ coupled.support, ∀ field, pair.2.2.shadow.values field = none) :
    let base := baseUtility setup leaks utility
    let settle := TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      ((runtime setup).serviceAudit leaks trafficAudit) deposit
    coupled.bind (fun pair => (settle (some pair.1)).map
      (fun payoffs => (sourceReadout setup leaks (some pair.1), payoffs))) =
      coupled.bind (fun pair => (settle (some pair.2.1)).map
        (fun payoffs => (sourceReadout setup leaks (some pair.2.1), payoffs))) := by
  intro base settle
  apply bind_congr_on_support _
  intro pair supported
  have readout := bindingCapabilityFrame_sourceReadout setup leaks owner pair.2.2 pair.1 pair.2.1
    (framed pair supported) (noValues pair supported)
  have settlement := (bindingCapabilityFrame_auditedSettlement setup leaks utility trafficAudit
    deposit owner pair.2.2 pair.1 pair.2.1 (framed pair supported) (noValues pair supported)).2
  change settle (some pair.1) = settle (some pair.2.1) at settlement
  change (settle (some pair.1)).map _ = (settle (some pair.2.1)).map _
  rw [readout, settlement]

end Vegas
