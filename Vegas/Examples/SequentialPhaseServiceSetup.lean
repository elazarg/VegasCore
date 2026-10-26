/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Expr.Simple
import Vegas.Game.RevealService
import Vegas.Game.SequentialRuntimePhases
import Vegas.Pending.PhaseFiniteNature
import Mathlib.Probability.Distributions.Uniform

/-! # Shared private Boolean publication and finite physical service data -/

noncomputable section

namespace Vegas.Examples.SequentialPhaseService

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory
  GameTheory.Protocol GameTheory.Math.Probability

abbrev Player := Unit
abbrev owner : Player := ()

def context : SourceCtx Player simpleExpr := [(0, .commitment owner .bool)]

def program : SourceProgram Player simpleExpr context {0} :=
  .reveal 1 owner 0 (by decide) .here (by decide) <|
  .ret [(owner, .ite (.getResultD (.var 1 .here) (.constBool false))
    (.constInt 2) (.constInt 0))]

def sourceInitial (bit : Bool) : State simpleExpr context :=
  Env.cons (.success bit) (Env.empty _)

def setup : Setup (Player := Player) (L := simpleExpr) where
  context := context
  namesNodup := by decide
  initialLaw := (PMF.uniformOfFintype Bool).map sourceInitial
  obligations := {0}
  program := program
  accounts := rfl
  exitTransfers := fun _ => 0

abbrev compiled := graph setup
abbrev event : compiled.EventId := ⟨0, by decide⟩
abbrev runtime := Vegas.runtime setup
abbrev plan := sequentialRuntimePhasePlan program

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket compiled) :=
  fun _ _ => PMF.pure ∅

abbrev app := phaseApplication runtime leaks

def initial : PMF app.State :=
  (setup.initialLaw.map setup.eventInputs).map (PhaseRuntimeState.initial plan)

def command : Nat → app.Command
  | 0 => .activate owner
  | 1 => .include (owner, 0)
  | 2 => .application .advanceClock
  | 3 => .application (.expire event)
  | _ => .wait

def scheduler : app.Scheduler := fun past _ => PMF.pure (command past.length)

abbrev horizon := 4

instance : leaks.FiniteSupport where
  support_finite _ _ := by simp only [leaks, PMF.support_pure]; exact Set.finite_singleton _

instance : setup.FiniteInitialLaw where
  support_finite := by
    rw [show setup.initialLaw = (PMF.uniformOfFintype Bool).map sourceInitial from rfl,
      PMF.support_map]
    exact (Set.toFinite _).image _

instance : app.FiniteNature initial scheduler where
  toFiniteEnvironment := inferInstance
  initial_finite := by
    rw [initial, PMF.support_map, PMF.support_map]
    exact ((Setup.FiniteInitialLaw.support_finite (setup := setup)).image _).image _
  scheduler_finite _ _ := by rw [scheduler, PMF.support_pure]; exact Set.finite_singleton _

end Vegas.Examples.SequentialPhaseService
