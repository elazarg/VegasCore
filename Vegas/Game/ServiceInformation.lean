/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealService
import Vegas.Compile.EventGraphHistory
import Vegas.EventGraph.SequentialLaw

/-! # Source information recovered from native owner observations

The decoder reads the existing masked graph store and the owner's retained
completion actions. It uses neither a hidden setup draw nor network inputs.
Typed store and completion-history agreement therefore recover the exact
source decision view, including correlated private inputs. Reconstruction of
the additional runtime fields and complete information fibers is separate.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- Changing only the dependency order leaves the owner's completion list
unchanged after the existing mode conversion. -/
theorem ownCompletions_fromModeCompletion (who : Player)
    (history : List (serviceGraph setup mode).Completion) :
    ((serviceGraph setup mode).ownCompletions who history).map
        (setup.eventGraph.fromModeCompletion mode) =
      setup.eventGraph.ownCompletions who
        (history.map (setup.eventGraph.fromModeCompletion mode)) := by
  simp only [EventGraph.ownCompletions, List.filter_map]
  rfl

/-- The identity carried in an arbitrary native view is checked before reading
its dependent observation. At an actual observation that check is reflexive. -/
def decisionView? {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (view : (serviceApplication setup mode deadline leaks).PlayerView) : Option
    (DecisionView who Γ) :=
  if same : view.application.who = who then
    let observed : (serviceGraph setup mode).PlayerObservation who := same ▸
        view.application.observation
    (decodeObservation? who refs observed.store).map fun source =>
      (source, decodeCompletions setup.program
        (observed.ownActions.map (setup.eventGraph.fromModeCompletion mode)))
  else none

theorem decisionView?_observe {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (source : Config Player L Γ)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (store : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
        (execution.application.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) = source.history) :
    decisionView? setup leaks refs who
        (execution.observe (serviceApplication setup mode deadline leaks) who) =
      some (source.view who) := by
  unfold decisionView?
  rw [dite_eq_left
          (show (execution.observe (serviceApplication setup mode deadline leaks)
          who).application.who = who from rfl)]
  change (decodeObservation? who refs
      ((serviceGraph setup mode).playerStore who execution.application.config.store)).map
        (fun observed => (observed, decodeCompletions setup.program
          (((serviceGraph setup mode).ownCompletions who execution.application.config.history).map
            (setup.eventGraph.fromModeCompletion mode)))) = _
  rw [decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode) refs who
          source.state execution.application.config.store store, Option.map_some,
          ownCompletions_fromModeCompletion]
  change some (sourceObserve who source.state,
    decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion mode)) who) = _
  rw [history]
  rfl

/-- A native information fiber cannot identify two different source decision
views when the operational compiler invariants hold at both histories. -/
theorem source_view_eq_of_observe_eq {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (serviceApplication setup mode deadline leaks).Execution)
    (leftStore : refs.Agrees left.state nativeLeft.application.config.store)
    (rightStore : refs.Agrees right.state nativeRight.application.config.store)
    (leftHistory : decodeHistory setup.program
        (nativeLeft.application.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) = left.history)
    (rightHistory : decodeHistory setup.program
        (nativeRight.application.config.history.map
          (setup.eventGraph.fromModeCompletion mode)) = right.history)
    (same : nativeLeft.observe (serviceApplication setup mode deadline leaks) who =
      nativeRight.observe (serviceApplication setup mode deadline leaks) who) : left.view who =
          right.view who := by
  have first := decisionView?_observe setup leaks refs who left nativeLeft leftStore leftHistory
  have second := decisionView?_observe setup leaks refs who right nativeRight
    rightStore rightHistory
  rw [same] at first
  exact Option.some.inj (first.symm.trans second)

end Vegas
