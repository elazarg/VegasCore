/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRuntime
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
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Changing only the dependency order leaves the owner's completion list
unchanged after the existing mode conversion. -/
theorem ownCompletions_from_sequential (who : Player)
    (history : List (graph setup).Completion) :
    ((graph setup).ownCompletions who history).map
        (setup.eventGraph.fromModeCompletion .sequential) =
      setup.eventGraph.ownCompletions who
        (history.map (setup.eventGraph.fromModeCompletion .sequential)) := by
  simp only [EventGraph.ownCompletions, List.filter_map]
  rfl

/-- The identity carried in an arbitrary native view is checked before reading
its dependent observation. At an actual observation that check is reflexive. -/
def decisionView? {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (view : (application setup leaks).PlayerView) : Option (DecisionView who Γ) :=
  if same : view.application.who = who then
    let observed : (graph setup).PlayerObservation who := same ▸ view.application.observation
    (decodeObservation? who refs observed.store).map fun source =>
      (source, decodeCompletions setup.program
        (observed.ownActions.map (setup.eventGraph.fromModeCompletion .sequential)))
  else none

theorem decisionView?_observe {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (source : Config Player L Γ) (execution : (application setup leaks).Execution)
    (store : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
        (execution.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = source.history) :
    decisionView? setup leaks refs who (execution.observe (application setup leaks) who) =
      some (source.view who) := by
  unfold decisionView?
  rw [dite_eq_left (show (execution.observe (application setup leaks) who).application.who = who
    from rfl)]
  change (decodeObservation? who refs
      ((graph setup).playerStore who execution.application.config.store)).map
        (fun observed => (observed, decodeCompletions setup.program
          (((graph setup).ownCompletions who execution.application.config.history).map
            (setup.eventGraph.fromModeCompletion .sequential)))) = _
  rw [decodeObservation?_playerStore_eq_some (graph := graph setup) refs who source.state
    execution.application.config.store store, Option.map_some,
    ownCompletions_from_sequential]
  change some (sourceObserve who source.state,
    decodeHistory setup.program
      (execution.application.config.history.map
        (setup.eventGraph.fromModeCompletion .sequential)) who) = _
  rw [history]
  rfl

/-- A native information fiber cannot identify two different source decision
views when the operational compiler invariants hold at both histories. -/
theorem source_view_eq_of_observe_eq {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (application setup leaks).Execution)
    (leftStore : refs.Agrees left.state nativeLeft.application.config.store)
    (rightStore : refs.Agrees right.state nativeRight.application.config.store)
    (leftHistory : decodeHistory setup.program
        (nativeLeft.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = left.history)
    (rightHistory : decodeHistory setup.program
        (nativeRight.application.config.history.map
          (setup.eventGraph.fromModeCompletion .sequential)) = right.history)
    (same : nativeLeft.observe (application setup leaks) who =
      nativeRight.observe (application setup leaks) who) : left.view who = right.view who := by
  have first := decisionView?_observe setup leaks refs who left nativeLeft leftStore leftHistory
  have second := decisionView?_observe setup leaks refs who right nativeRight
    rightStore rightHistory
  rw [same] at first
  exact Option.some.inj (first.symm.trans second)

end Vegas
