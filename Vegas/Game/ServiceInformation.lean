module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealService
public import Vegas.Compile.EventGraphHistory
public import Vegas.EventGraph.SequentialLaw

@[expose] public section

/-! # Source information recovered from native owner observations

The decoder reads the masked graph store, public default record and owner's
retained completion actions. It uses neither a hidden setup draw nor network
inputs. Typed store, default-record and completion-history agreement recover
the exact source decision view, including correlated private inputs. Reconstruction of
the additional runtime fields and complete information fibers is separate.
-/

noncomputable section

namespace Vegas

open SourceProgram

open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {duration : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The identity carried in an arbitrary native view is checked before reading
its dependent observation. At an actual observation that check is reflexive. -/
def decisionView? {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (view : (serviceApplication setup mode duration leaks).PlayerView) : Option
    (DecisionView who Γ) :=
  if same : view.application.who = who then
    let observed : (serviceGraph setup mode).PlayerObservation who := same ▸
        view.application.observation
    (decodeObservation? who refs observed.store).map fun source =>
      ⟨source, observed.defaults, decodeCompletions setup.program
        (observed.ownActions)⟩
  else none

/-- Compiler agreement recovers all three components of the source view exactly. -/
theorem decisionView?_observe {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (source : Config Player L Γ)
    (execution : (serviceApplication setup mode duration leaks).Execution)
    (store : refs.Agrees source.state execution.application.config.store)
    (history : decodeHistory setup.program
        (execution.application.config.history) = source.history)
    (defaults : execution.application.config.defaults = source.defaults) :
    decisionView? setup leaks refs who
        (execution.observe (serviceApplication setup mode duration leaks) who) =
      some (source.view who) := by
  unfold decisionView?
  rw [dite_eq_left
          (show (execution.observe (serviceApplication setup mode duration leaks)
          who).application.who = who from rfl)]
  change (decodeObservation? who refs
      ((serviceGraph setup mode).playerStore who execution.application.config.store)).map
        (fun observed => DecisionView.mk observed execution.application.config.defaults
          (decodeCompletions setup.program
            ((serviceGraph setup mode).ownCompletions who
              execution.application.config.history))) = _
  rw [decodeObservation?_playerStore_eq_some (graph := serviceGraph setup mode) refs who
          source.state execution.application.config.store store, Option.map_some]
  change some (DecisionView.mk (sourceObserve who source.state)
    execution.application.config.defaults (decodeHistory setup.program
      (execution.application.config.history) who)) = _
  rw [history, defaults]
  rfl

/-- A native information fiber cannot identify two different source decision
views when the operational compiler invariants hold at both histories. -/
theorem source_view_eq_of_observe_eq {Γ : SourceCtx Player L}
    (refs : ContextRefs (graphLayout setup.program) Γ) (who : Player)
    (left right : Config Player L Γ)
    (nativeLeft nativeRight : (serviceApplication setup mode duration leaks).Execution)
    (leftStore : refs.Agrees left.state nativeLeft.application.config.store)
    (rightStore : refs.Agrees right.state nativeRight.application.config.store)
    (leftHistory : decodeHistory setup.program
        (nativeLeft.application.config.history) = left.history)
    (rightHistory : decodeHistory setup.program
        (nativeRight.application.config.history) = right.history)
    (leftDefaults : nativeLeft.application.config.defaults = left.defaults)
    (rightDefaults : nativeRight.application.config.defaults = right.defaults)
    (same : nativeLeft.observe (serviceApplication setup mode duration leaks) who =
      nativeRight.observe (serviceApplication setup mode duration leaks) who) : left.view who =
          right.view who := by
  have first := decisionView?_observe setup leaks refs who left nativeLeft leftStore
    leftHistory leftDefaults
  have second := decisionView?_observe setup leaks refs who right nativeRight
    rightStore rightHistory rightDefaults
  rw [same] at first
  exact Option.some.inj (first.symm.trans second)

end Vegas
