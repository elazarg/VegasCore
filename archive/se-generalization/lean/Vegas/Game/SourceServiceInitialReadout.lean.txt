/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceInitialObservation
import Vegas.Game.SourceServiceReadout
import Vegas.Compile.EventGraphParameterReadout
import Vegas.EventGraph.PrivateInputs
import Vegas.Pending.ReactiveStateInvariant

/-! # Recovering the same source initialization from native inputs

Initial source references address only the persistent graph inputs. Their typed
decoder recovers the entire initial environment, including correlated private
cells, at every actual initialized descendant. The decoder is an analysis readout
of existing state; it adds neither a runtime field nor a player observation.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Decode the initial context from its compiler input references, independently
of event completion or the availability of terminal outputs. -/
def sourceInitialReadout (setup : Setup (Player := Player) (L := L))
    (config : (graph setup).Config) : Option (State L setup.context) :=
  decodeState? (ContextRefs.initial setup.context (outputLayout setup.program)) config.store

/-- Persistent encoded inputs identify the same complete initial source state,
without sampling a replacement or choosing a compatible support witness. -/
theorem sourceInitialReadout_eq_some_of_inputs
    (setup : Setup (Player := Player) (L := L)) (config : (graph setup).Config)
    (initial : State L setup.context) (inputs : config.inputs = setup.eventInputs initial) :
    sourceInitialReadout setup config = some initial := by
  apply decodeState?_eq_some
  apply ContextRefs.initial_agrees
  intro input
  change some (config.inputs input) = some (encodeInputs initial input)
  rw [inputs]
  rfl

/-- Initialization already recovers the actual sampled state before any event
has completed. No source-profile or independence condition is needed. -/
theorem sourceInitialReadout_initial (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) :
    sourceInitialReadout setup
      (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs initial)).config =
        some initial :=
  sourceInitialReadout_eq_some_of_inputs setup _ initial rfl

/-- Every graph descendant of this initialization recovers this same initial
state, including unfinished prefixes and public expiry completions. -/
theorem sourceInitialReadout_reachable (setup : Setup (Player := Player) (L := L))
    (initial : State L setup.context) (config : (graph setup).Config)
    (reachable : EventGraph.Config.Reachable (graph := graph setup)
      (setup.eventInputs initial) config) :
    sourceInitialReadout setup config = some initial :=
  sourceInitialReadout_eq_some_of_inputs setup config initial reachable.inputs_eq

/-- The source encoding cannot merge distinct initial environments. This
allows the initial-state identity to be retained jointly with any parameter. -/
theorem eventInputs_injective (setup : Setup (Player := Player) (L := L)) :
    Function.Injective setup.eventInputs := by
  intro first second encoded
  have decoded := sourceInitialReadout_eq_some_of_inputs setup
    (EventGraphRuntime.State.initial (graph := graph setup) (setup.eventInputs first)).config
    second encoded
  exact Option.some.inj ((sourceInitialReadout_initial setup first).symm.trans decoded)

/-- Arbitrary actual native response and scheduler rounds preserve the selected
initial state. The operational invariant is obtained from initialized support,
not from the source policy or completion of the run. -/
theorem sourceInitialReadout_runRounds
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : State L setup.context)
    (players : Player → (application setup leaks).Policy)
    (scheduler : (application setup leaks).Scheduler) (count : Nat)
    (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).runRounds scheduler players count
      (ReactiveApplication.Execution.initial (application setup leaks)
        (EventGraphRuntime.State.initial (graph := graph setup)
          (setup.eventInputs initial)))).support) :
    sourceInitialReadout setup execution.application.config = some initial := by
  have invariant := (ReactiveApplication.Invariant.policyInvariant (application setup leaks)
    ((runtime setup).reactiveStateInvariant leaks (setup.eventInputs initial)) players).runRounds
      scheduler count _ execution
        (EventGraphRuntime.State.initial_invariant (graph := graph setup)
          (setup.eventInputs initial)) reached
  exact sourceInitialReadout_reachable setup initial _ invariant.reachable

/-- Every legal initialized native history decodes its actual supported initial
draw. Injectivity above makes this identity unique, even for correlated laws. -/
theorem sourceInitialReadout_history
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (horizon : Nat) (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some control)) :
    ∃ initial ∈ setup.initialLaw.support,
      sourceInitialReadout setup control.execution.application.config = some initial := by
  have initialized : initialLaw setup =
      (setup.initialLaw.map setup.eventInputs).map
        (EventGraphRuntime.State.initial (graph := graph setup)) := by
    rw [PMF.map_comp]
    rfl
  rw [initialized] at trace
  have reached := (runtime setup).reactive_history_graph_reachable leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler trace
  obtain ⟨inputs, supported, reachable⟩ := reached
  obtain ⟨initial, selected, rfl⟩ := PMF.support_map .. ▸ supported
  exact ⟨initial, selected, sourceInitialReadout_reachable setup initial _ reachable⟩

/-- Successful terminal readout contains the same initial environment recovered
directly from the persistent graph inputs. This relates the ancestor parameter
to the actual terminal source state, without a separate parameter draw. -/
theorem sourceInitialReadout_of_sourceReadout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (control : (application setup leaks).Control)
    (source : State L setup.program.terminalCtx)
    (decoded : sourceReadout setup leaks (some control) = some source) :
    sourceInitialReadout setup control.execution.application.config =
      some (initialState setup.program source) := by
  rw [sourceReadout_eq_decode] at decoded
  apply decodeState?_eq_some
  exact terminalRefsWith_initial_agrees setup.program _ _ _ source
    (decodeState?_agrees (terminalRefs setup.program) _ source decoded)

end Vegas
