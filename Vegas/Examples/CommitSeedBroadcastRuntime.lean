/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastSource
import Vegas.Examples.CommitSeedBroadcastOrder
import Vegas.Game.CompiledRuntimePhases
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseFiniteNature
import Interaction.CompletePendingObservation
import Interaction.ReactiveSchedulerSeedSupport

/-! # A shared receipt between independent first-late callback groups

The original commitment attempt polls the favorable seeds, includes the
initially submitted packets, then polls the unfavorable seeds. All these
commands have clock two. Late submissions are considered only after both
groups finish. Later attempts and publications receive protected service.
-/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def runtime : EventGraphRuntime graph where
  deadline := fun _ => 6

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph) :=
  MessageNetwork.completePendingObservation

abbrev app := phaseApplication runtime leaks

def plan : RuntimePhasePlan graph := compiledRuntimePhasePlan program .concurrentReveals

def initialState : app.State :=
  PhaseRuntimeState.initial plan (encodeInputs (Env.empty (CellVal simpleExpr)))

def initial : PMF app.State := PMF.pure initialState

abbrev horizon : Nat := 128

def bounds : MessageBounds graph where
  candidateCount := 128
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

abbrev rawMenu := PhaseCount.rawMenu runtime leaks bounds
abbrev countedMenu := PhaseCount.onePacketMenu runtime leaks bounds

def originalAttempt : CommitAttemptId := ⟨0, 0⟩

def originalCoordinate (owner : Player) : CommitAttemptEvent graph :=
  ⟨originalAttempt, bindingEvent owner⟩

abbrev Seeds := Equiv.Perm Player × (Player → Bool)

def pendingCommand (identifier : MessageId Player) (view : app.EnvironmentView) : app.Command :=
  if view.network.pending.any (fun message => message.id = identifier) then
    .include identifier
  else .wait

open Classical in
def ready (owner : Player) (event : graph.EventId) (view : app.EnvironmentView) : Bool :=
  decide (PhaseRuntimeState.requests view.application owner
    ⟨view.application.attempt, event⟩)

def activateReady (owner : Player) (event : graph.EventId)
    (view : app.EnvironmentView) : app.Command :=
  if ready owner event view then .activate owner else .wait

/-- The first post-response snapshot records every clock-zero envelope. -/
def earlyCommand (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match past[3]? with
  | none => .wait
  | some entry =>
      match entry.beforeView.network.inputs.find? (fun message =>
          message.sender = owner ∧ message.payload.attempt = originalAttempt) with
      | none => .wait
      | some message => pendingCommand message.id view

open Classical in
def responseCommand (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match past.getLast? with
  | none => .wait
  | some entry =>
      if entry.command = .activate owner ∧
          entry.beforeView.network.nextSerial owner < view.network.nextSerial owner then
        pendingCommand (owner, entry.beforeView.network.nextSerial owner) view
      else .wait

def lateCommand (owner : Player) (good : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  if ready owner (bindingEvent owner) view ∧ (if good then 2 else 3) = clock then
    match (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        past view).emissions.find? (fun emitted => emitted.1 = clock) with
    | none => .wait
    | some emitted => pendingCommand emitted.2.id view
  else .wait

def pollCommand (owner : Player) (good wanted : Bool)
    (view : app.EnvironmentView) : app.Command :=
  if good = wanted then activateReady owner (bindingEvent owner) view else .wait

/-- Uniformly ordered callbacks straddle one shared middle receipt block. -/
def originalCommand (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  match position with
  | 0 => activateReady alice (bindingEvent alice) view
  | 1 => activateReady bob (bindingEvent bob) view
  | 2 => activateReady carol (bindingEvent carol) view
  | 3 | 4 | 17 | 24 | 25 | 26 => .application .advanceClock
  | 5 => pollCommand (seeds.1 0) (seeds.2 (seeds.1 0)) true view
  | 6 => pollCommand (seeds.1 1) (seeds.2 (seeds.1 1)) true view
  | 7 => pollCommand (seeds.1 2) (seeds.2 (seeds.1 2)) true view
  | 8 => earlyCommand (seeds.1 0) past view
  | 9 => earlyCommand (seeds.1 1) past view
  | 10 => earlyCommand (seeds.1 2) past view
  | 11 => pollCommand (seeds.1 0) (seeds.2 (seeds.1 0)) false view
  | 12 => pollCommand (seeds.1 1) (seeds.2 (seeds.1 1)) false view
  | 13 => pollCommand (seeds.1 2) (seeds.2 (seeds.1 2)) false view
  | 14 => lateCommand (seeds.1 0) (seeds.2 (seeds.1 0)) 2 past view
  | 15 => lateCommand (seeds.1 1) (seeds.2 (seeds.1 1)) 2 past view
  | 16 => lateCommand (seeds.1 2) (seeds.2 (seeds.1 2)) 2 past view
  | 18 => activateReady (seeds.1 0) (bindingEvent (seeds.1 0)) view
  | 19 => activateReady (seeds.1 1) (bindingEvent (seeds.1 1)) view
  | 20 => activateReady (seeds.1 2) (bindingEvent (seeds.1 2)) view
  | 21 => lateCommand (seeds.1 0) (seeds.2 (seeds.1 0)) 3 past view
  | 22 => lateCommand (seeds.1 1) (seeds.2 (seeds.1 1)) 3 past view
  | 23 => lateCommand (seeds.1 2) (seeds.2 (seeds.1 2)) 3 past view
  | 27 => .application (.expire (bindingEvent alice))
  | 28 => .application (.expire (bindingEvent bob))
  | 29 => .application (.expire (bindingEvent carol))
  | _ => .wait

def tailIndex (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : Nat :=
  past.length - past.findIdx (fun entry =>
    entry.beforeView.application.attempt = view.application.attempt)

def tailCommand (event : Player → graph.EventId) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  match position with
  | 0 => activateReady alice (event alice) view
  | 1 => responseCommand alice past view
  | 2 => activateReady bob (event bob) view
  | 3 => responseCommand bob past view
  | 4 => activateReady carol (event carol) view
  | 5 => responseCommand carol past view
  | 6 | 7 | 8 | 9 | 10 | 11 => .application .advanceClock
  | 12 => .application (.expire (event alice))
  | 13 => .application (.expire (event bob))
  | 14 => .application (.expire (event carol))
  | _ => .wait

def choose (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  if view.application.attempt = originalAttempt then
    originalCommand seeds past.length past view
  else
    match view.application.phase with
    | some (.commitment, _, _) => tailCommand bindingEvent (tailIndex past view) past view
    | some (.reveal, _, _) => tailCommand revealEvent (tailIndex past view) past view
    | some (.sample, _, _) | none => .wait

def family (seeds : Seeds) : app.Scheduler :=
  fun past view => PMF.pure (choose seeds past view)

def implementation : app.SchedulerImplementation Seeds :=
  app.schedulerMixture nativeSeedLaw family

def scheduler : app.Scheduler := implementation.scheduler

theorem scheduler_eq_posterior (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    scheduler past view = (implementation.posterior past).map
      (fun seeds => choose seeds past view) := by
  rw [scheduler, ReactiveApplication.SchedulerImplementation.scheduler_eq]
  change ((implementation.posterior past).bind fun seeds =>
    (PMF.pure (choose seeds past view)).map (fun command => (command, seeds))).map Prod.fst = _
  simp only [PMF.pure_map, PMF.map_bind]
  rfl

instance finiteLeaks : leaks.FiniteSupport := by
  unfold leaks
  infer_instance

instance finiteNature : app.FiniteNature initial scheduler :=
  phaseApplication_finiteNature runtime leaks initial scheduler (by
    rw [initial, PMF.support_pure]
    exact Set.finite_singleton _) (by
    intro past view
    rw [scheduler_eq_posterior, PMF.support_map]
    exact (Set.toFinite _).image _)

instance familyFiniteNature (seeds : Seeds) : app.FiniteNature initial (family seeds) :=
  phaseApplication_finiteNature runtime leaks initial (family seeds) (by
    rw [initial, PMF.support_pure]
    exact Set.finite_singleton _) (by
    intro past view
    rw [family, PMF.support_pure]
    exact Set.finite_singleton _)

theorem choose_original (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (original : view.application.attempt = originalAttempt) :
    choose seeds past view = originalCommand seeds past.length past view := by
  simp only [choose, ite_eq_left original]

end Vegas.Examples.CommitSeedBroadcast
