/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.PendingMenusSource
import Vegas.Pending.ReactiveServiceProgress
import Vegas.Pending.ReactivePolicyFacts
import Interaction.ReactiveSubgamePrefix
import Interaction.PendingSelection

/-! # An early opening competes with later withholding

The schedule is fixed, and each inclusion samples uniformly among distinct
unpublished envelopes for the event. One earlier valid binding and one earlier
withholding packet are pending at a proper native subgame. Transmitting an
opening for the later event can be better than repairing the current binding.
-/

noncomputable section

namespace Vegas.Examples.ReactiveEarlyOpening

open GameTheory.Protocol GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

abbrev graph := PendingMenus.graph
abbrev runtime := PendingMenus.runtime
abbrev input := PendingMenus.input

def leaks : MessageNetwork.ObservationRule Unit (WitnessedPacket graph) := fun _ _ => PMF.pure ∅
abbrev app := runtime.reactiveApplication leaks

def initialState : EventGraphRuntime.State graph :=
  State.initial input
def initial : app.Execution := .initial app initialState

def first : app.Action := runtime.reactiveBinding leaks () 0 .int (.success 1) 0
def second : app.Action := ⟨some ⟨⟨.withhold 1, none⟩, .none⟩⟩

/-- Uniform choice among distinct, unpublished identifiers for this event. -/
def select (event : graph.EventId) (view : app.EnvironmentView) : PMF app.Command :=
  ((MessageNetwork.uniformPending (fun packet =>
    decide (packet.payload.call.event? graph = some event) &&
      !(view.network.ledger.any fun prior => prior.id = packet.id))
    view.network.pending).map (fun selected => selected.elim .wait .include)).map
      (app.atMostOnceCommand view)

/-- All activation and inclusion times are fixed before any player response. -/
def scheduler : app.Scheduler := fun history view =>
  match history.length with
  | 0 | 1 | 2 => PMF.pure (.activate ())
  | 3 => select 0 view
  | 4 => PMF.pure (.activate ())
  | 5 => select 1 view
  | _ => PMF.pure .wait

abbrev arena := app.protocol (PMF.pure initialState) 6 scheduler
abbrev model := app.information (PMF.pure initialState) 6 scheduler

/-- Only the initial two scheduling decisions constrain the subgame-root proof. -/
def responsePrefix : app.TwoResponsePrefix where
  initialState := initialState
  remaining := 4
  scheduler := scheduler
  schedules history view early := by
    have casesLength : history.length = 0 ∨ history.length = 1 := by omega
    rcases casesLength with zero | one
    · simp only [scheduler, zero]
    · simp only [scheduler, one]
  activation execution := by
    simp only [ReactiveApplication.Execution.environmentStep, app, reactiveApplication, leaks,
      PMF.pure_map, MessageNetwork.learn_empty]

abbrev activated := responsePrefix.activated
abbrev afterFirst := responsePrefix.afterFirst
abbrev afterSecond := responsePrefix.afterSecond
abbrev secondHistory := responsePrefix.secondHistory

def contested : app.Execution := afterSecond first second

theorem activation (execution : app.Execution) :
    execution.environmentStep app (.activate ()) = PMF.pure (activated execution) :=
  responsePrefix.activation execution

/-- Recall identifies this prefix inside every future decision information set. -/
theorem contested_isSubgameRoot : model.IsSubgameRoot (secondHistory first second) :=
  responsePrefix.secondHistory_isSubgameRoot first second

end Vegas.Examples.ReactiveEarlyOpening
