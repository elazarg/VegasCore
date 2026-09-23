/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Expr.Simple
import Vegas.Pending.ReactivePolicy
import Vegas.Pending.ReactiveService
import Vegas.Pending.ReactiveSafety

/-! # Binding and private recall in the one-message protocol -/

noncomputable section

namespace VegasTests.ReactiveRuntime

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

private abbrev order : EventOrder where
  eventCount := 1
  predecessors _ := ∅
  predecessor_lt := by simp

private abbrev inputs : Fin 0 → EventGraph.EventField Bool simpleExpr := Fin.elim0
private abbrev outputs : Fin 1 → EventGraph.EventField Bool simpleExpr :=
  fun _ => .binding false .bool

private abbrev graph : EventGraph Bool simpleExpr where
  inputCount := 0
  order := order
  inputLayout := inputs
  outputLayout := outputs
  nodes _ := EventGraph.EventCode.bind
    (layout := EventGraph.fieldLayout inputs outputs) false .bool
  reads_available := by
    intro event field member
    exact False.elim (Finset.notMem_empty field member)
  payoffs := []

private def runtime : EventGraphRuntime graph where
  deadline _ := 2

private def leaks : MessageNetwork.ObservationRule Bool (Payload graph) :=
  fun _ _ => FinDist.pure ∅

private abbrev app := runtime.reactiveApplication leaks
private abbrev candidate : Handle graph := (false, .prepared 0)

private def initial : app.Execution :=
  ReactiveApplication.Execution.initial app
    (State.initial (graph := graph) (fun input => nomatch input))

private def submitted (bit : Bool) : app.Execution :=
  initial.respond app false (runtime.reactiveBinding leaks false 0 .bool (.success bit) 0)

/-- One decision both fixes the hidden meaning and emits the public envelope. -/
theorem single_activation (bit : Bool) :
    (submitted bit).application.bindingResult candidate .bool = .success bit ∧
      (submitted bit).network.pending = [⟨(false, 0), .commitment 0 candidate⟩] ∧
      ((submitted bit).recall false).length = 1 ∧
      (submitted bit).environmentRecall = [] ∧
      (submitted bit).application.remembered 0 = none := by
  refine ⟨?_, rfl, rfl, rfl, rfl⟩
  exact runtime.reactiveBinding_result leaks false 0 .bool (.success bit) 0 initial rfl

/-- Reading a packet later cannot make a submitted handle mutable. -/
theorem replacement_fails (bit replacement : Bool) :
    ((submitted bit).respond app false
      (runtime.reactiveBinding leaks false 0 .bool (.success replacement)
        0)).application.bindingResult
        candidate .bool = .success bit := by
  cases bit <;> cases replacement <;> rfl

/-- Omitting opening material is irrevocable for that handle. -/
theorem late_opening_fails :
    let failed := initial.respond app false (runtime.reactiveBinding leaks false 0 .bool
      .failure 0)
    let next := failed.respond app false (runtime.reactiveBinding leaks false 0 .bool
      (.success true) 0)
    next.application.candidates.lookup candidate = .unopenable := rfl

/-- Neither the private bit nor its own recall becomes a scheduler observation. -/
theorem binding_hidden :
    (submitted false).observeEnvironment app = (submitted true).observeEnvironment app :=
  runtime.reactiveBinding_observation leaks false 0 .bool (.success false) (.success true)
    0 initial

private def granted : app.Execution :=
  { initial with application := { initial.application with serviceGrant := some 0 } }

private def chooseBit (law : FinDist Bool) : graph.BehavioralPolicy false :=
  fun _ _ _ => law.map PublicationResult.success

/-- The actual graph-policy compiler consumes the source random law at the
first activation and returns a complete submission action. -/
theorem compiler_samples_on_activation (law : FinDist Bool) :
    runtime.compileReactivePolicy leaks false (chooseBit law) [] (granted.observe app false) =
      law.map (fun bit => runtime.reactiveDecision leaks false 0 (.success bit)
        (granted.observe app false).application) := by
  have actor : graph.actor? 0 = some false := rfl
  simp [compileReactivePolicy, reactiveAlreadySubmitted, granted, initial,
    ReactiveApplication.Execution.initial, ReactiveApplication.Execution.observe,
    app, reactiveApplication, State.publicView, PublicView.EventReady, State.initial,
    EventGraph.Config.initial, EventGraph.normalizePolicy, chooseBit,
    FinDist.map_comp, Function.comp_def, actor]

private theorem first_slot :
    reactiveFreshSlot (granted.observe app false).application = some 0 := by
  unfold reactiveFreshSlot
  split
  · congr 1
    exact (Nat.find_eq_zero _).mpr rfl
  · rename_i impossible
    exact False.elim (impossible ⟨0, rfl⟩)

private def firstAction (bit : Bool) : app.Action :=
  runtime.reactiveDecision leaks false 0 (.success bit) (granted.observe app false).application

private def firstResponse (bit : Bool) : app.Execution :=
  granted.respond app false (firstAction bit)

private theorem first_action (bit : Bool) : firstAction bit =
    ⟨⟨some ⟨0, .success bit⟩, []⟩,
      some (.submit ⟨.commitment 0 candidate, some ⟨.bool, bit⟩⟩)⟩ := by
  change ReactiveApplication.Action.mk (app := app) _
    ((reactiveFreshSlot (granted.observe app false).application).map _) = _
  rw [first_slot]
  rfl

/-- The compiled action preserves the sampled intention privately and emits
one binding packet, with no application scratch-table writes. -/
theorem compiler_sends_and_remembers (bit : Bool) :
    (firstResponse bit).application.bindingResult candidate .bool = .success bit ∧
      (firstResponse bit).network.pending = [⟨(false, 0), .commitment 0 candidate⟩] ∧
      ((firstResponse bit).recall false).map (fun entry => entry.action.memory.intention) =
        [some ⟨0, .success bit⟩] ∧
      (firstResponse bit).application.remembered 0 = none := by
  unfold firstResponse
  rw [first_action]
  cases bit <;> exact ⟨rfl, rfl, rfl, rfl⟩

/-- Re-activating the owner before inclusion does not resample or send a
competing commitment, even when the next source policy law is different. -/
theorem compiler_does_not_resample (bit : Bool) (law : FinDist Bool) :
    runtime.compileReactivePolicy leaks false (chooseBit law) ((firstResponse bit).recall false)
      ((firstResponse bit).observe app false) = FinDist.pure ⟨default, none⟩ := by
  have sent : runtime.reactiveAlreadySubmitted leaks ((firstResponse bit).recall false) 0
    = true := by
    unfold firstResponse
    rw [first_action]
    rfl
  have grant : ((firstResponse bit).observe app false).application.publicView.serviceGrant =
      some 0 := by
    unfold firstResponse
    rw [first_action]
    rfl
  simp only [compileReactivePolicy, grant, sent, ↓reduceIte]

/-- Reserved service gives the owner one activation. Additional activations
are choices of the network policy at its ordinary opportunities. -/
example : interactionVisit (graph := graph) 2 0 =
    [.grant 0, .player false, .wire, .wire, .includeLatest 0 false, .sample 0] := rfl

example (who : Bool) : (NetworkChoice.activate who).command runtime leaks = .activate who := rfl

end VegasTests.ReactiveRuntime
