/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingRepairInclusion
import Vegas.Pending.PhaseFailureCoverage
import Vegas.EventGraph.ResolutionProvenance
import Vegas.Pending.ReactiveBindingFrameOpening

/-! # Native projections used by the existing binding-repair frame

The projection forgets physical namespaces and phase observations in a proof
invariant. It does not replace the actual scheduler or its passive observation law.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- A native carrier for applying the existing frame lemmas. Actual leaked
packets are projected from the physical history, never sampled from this rule. -/
def nativeLeaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph) :=
  fun _ _ => PMF.pure ∅

local notation "app" => phaseApplication runtime leaks
local notation "nativeApp" => runtime.reactiveApplication (nativeLeaks (graph := graph))

def network (physical : MessageNetwork Player (CommitAttemptPacket graph)) :
    MessageNetwork Player (WitnessedPacket graph) :=
  ⟨physical.pending.map PhaseCount.nativeMessage, physical.ledger.map PhaseCount.nativeMessage,
    fun who => (physical.leaked who).map PhaseCount.nativeMessage,
    physical.inputs.map PhaseCount.nativeMessage, physical.nextSerial⟩

def view (physical : (app).PlayerView) : (nativeApp).PlayerView :=
  ⟨⟨physical.messages.leaked.map PhaseCount.nativeMessage,
    physical.messages.ledger.map PhaseCount.nativeMessage⟩, physical.application.1,
      physical.receipts⟩

def action (physical : (app).Action) : (nativeApp).Action := ⟨physical.transmission⟩

def entry (physical : (app).PlayerEntry) : (nativeApp).PlayerEntry :=
  ⟨view runtime leaks physical.beforeView, action runtime leaks physical.action,
    physical.emitted.map PhaseCount.nativeMessage⟩

def command : (app).Command → (nativeApp).Command
  | .wait => .wait
  | .activate who => .activate who
  | .include id => .include id
  | .application operation => .application operation

def environmentView (physical : (app).EnvironmentView) : (nativeApp).EnvironmentView :=
  ⟨⟨physical.network.pending.map PhaseCount.nativeMessage,
    physical.network.ledger.map PhaseCount.nativeMessage,
    physical.network.inputs.map PhaseCount.nativeMessage, physical.network.nextSerial⟩,
    physical.application.native, physical.receipts⟩

def environmentEntry (physical : (app).EnvironmentEntry) : (nativeApp).EnvironmentEntry :=
  ⟨environmentView runtime leaks physical.beforeView, command runtime leaks physical.command⟩

def execution (physical : (app).Execution) : (nativeApp).Execution :=
  ⟨physical.application.current.native, network physical.network, physical.receipts,
    fun who => (physical.recall who).map (entry runtime leaks),
    physical.environmentRecall.map (environmentEntry runtime leaks)⟩

theorem observe (physical : (app).Execution) (who : Player) :
    (execution runtime leaks physical).observe (nativeApp) who =
      view runtime leaks (physical.observe (app) who) := rfl

theorem observeEnvironment (physical : (app).Execution) :
    (execution runtime leaks physical).observeEnvironment (nativeApp) =
      environmentView runtime leaks (physical.observeEnvironment (app)) := rfl

theorem outputs (past : List (app).PlayerEntry) :
    (nativeApp).outputs (past.map (entry runtime leaks)) =
      ((app).outputs past).map PhaseCount.nativeMessage := by
  induction past with
  | nil => rfl
  | cons first rest ih =>
      simp only [ReactiveApplication.outputs] at ih
      cases sent : first.emitted <;> simp only [ReactiveApplication.outputs, List.filterMap_cons,
        List.map_cons, entry, sent, Option.map_none, Option.map_some, ih]

end Vegas.EventGraphRuntime.PhaseBindingRepair
