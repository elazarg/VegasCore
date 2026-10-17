/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingSource
import Vegas.Game.CompiledRuntimePhases
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseFiniteNature
import Interaction.CompletePendingObservation
import Interaction.ReactiveAddressedScheduler
import Interaction.ReactiveSchedulerSeedSupport
import Interaction.ReactiveRoundReachability

/-! # An initialized two-owner private-seed service -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

abbrev graph := serviceGraph setup .concurrentReveals

def runtime : EventGraphRuntime graph where
  deadline := fun _ => 6

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph) :=
  MessageNetwork.completePendingObservation

abbrev app := phaseApplication runtime leaks

def plan : RuntimePhasePlan graph := compiledRuntimePhasePlan program .concurrentReveals

def initial : PMF app.State :=
  (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)

def initialState : app.State :=
  PhaseRuntimeState.initial plan (encodeInputs (Env.empty (CellVal simpleExpr)))

def initialExecution : app.Execution := ReactiveApplication.Execution.initial app initialState

theorem initial_eq_pure : initial = PMF.pure initialState := by
  change ((PMF.pure (Env.empty (CellVal simpleExpr))).map encodeInputs).map
    (PhaseRuntimeState.initial plan) = PMF.pure initialState
  simp only [PMF.pure_map, initialState]

theorem initialState_clock : initialState.current.native.clock = 0 := by
  unfold initialState PhaseRuntimeState.initial
  rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.2]
  rfl

theorem initialState_candidate (owner : Player) (serial : Nat) :
    initialState.current.native.candidates.lookup (owner, .prepared serial) = .fresh := by
  unfold initialState PhaseRuntimeState.initial
  rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
  exact State.initial_candidate _ owner (.prepared serial)

abbrev horizon : Nat := 64

def bounds : MessageBounds graph where
  candidateCount := 64
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

abbrev rawMenu := PhaseCount.rawMenu runtime leaks bounds
abbrev countedMenu := PhaseCount.onePacketMenu runtime leaks bounds

def originalAttempt : CommitAttemptId := ⟨0, 0⟩

def aliceBinding : graph.EventId := ⟨0, by decide⟩
def bobBinding : graph.EventId := ⟨1, by decide⟩
def aliceReveal : graph.EventId := ⟨2, by decide⟩
def bobReveal : graph.EventId := ⟨3, by decide⟩

def bindingEvent (owner : Player) : graph.EventId :=
  if owner = alice then aliceBinding else bobBinding

def originalCoordinate (owner : Player) : CommitAttemptEvent graph :=
  ⟨originalAttempt, bindingEvent owner⟩

def originalAddress (owner : Player) : PhaseSeedAddress graph :=
  ⟨originalCoordinate owner, by
    constructor
    · change 0 < 4
      decide
    · change 0 ≤ 2
      decide⟩

abbrev Seeds := Unit × (PhaseSeedAddress graph → Bool)

def seedLaws (address : PhaseSeedAddress graph) : PMF Bool :=
  if address = originalAddress alice ∨ address = originalAddress bob then
    PMF.uniformOfFintype Bool
  else PMF.pure false

def seedPrior : PMF Seeds :=
  (independentProduct seedLaws).map fun seeds => ((), seeds)

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

/-- The snapshot after the two original responses identifies actual clock-zero
envelopes without inspecting their calls, private preparations or evidence. -/
def earlyCommand (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match past[2]? with
  | none => .wait
  | some entry =>
      match entry.beforeView.network.inputs.find? (fun message =>
          message.sender = owner ∧ message.payload.attempt = originalAttempt) with
      | none => .wait
      | some message => pendingCommand message.id view

open Classical in
/-- Include exactly the envelope of the immediately preceding activation.
A silent response cannot select a stale packet retained from an earlier phase. -/
def responseCommand (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match past.getLast? with
  | none => .wait
  | some entry =>
      if entry.command = .activate owner ∧
          entry.beforeView.network.nextSerial owner < view.network.nextSerial owner then
        pendingCommand (owner, entry.beforeView.network.nextSerial owner) view
      else .wait

def lateClock (owner : Player) (seed : Bool) : Nat :=
  (if owner = alice then 2 else 4) + if seed then 1 else 0

def lateCommand (owner : Player) (seed : Bool) (clock : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  if ready owner (bindingEvent owner) view ∧ lateClock owner seed = clock then
    match (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate owner) owner
        past view).emissions.find? (fun emitted => emitted.1 = clock) with
    | none => .wait
    | some emitted => pendingCommand emitted.2.id view
  else .wait

def pollCommand (owner : Player) (seed wanted : Bool)
    (view : app.EnvironmentView) : app.Command :=
  if seed = wanted then activateReady owner (bindingEvent owner) view else .wait

/-- The complete original routine uses twenty-two scheduler decisions.
The post-block inclusion preserves the fixed middle marker placement. -/
def originalCommand (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  match position with
  | 0 => activateReady alice aliceBinding view
  | 1 => activateReady bob bobBinding view
  | 2 | 3 | 8 | 11 | 16 | 19 => .application .advanceClock
  | 4 => pollCommand alice (seeds.2 (originalAddress alice)) false view
  | 5 => earlyCommand bob past view
  | 6 => pollCommand alice (seeds.2 (originalAddress alice)) true view
  | 7 => lateCommand alice (seeds.2 (originalAddress alice)) 2 past view
  | 9 => activateReady alice aliceBinding view
  | 10 => lateCommand alice (seeds.2 (originalAddress alice)) 3 past view
  | 12 => pollCommand bob (seeds.2 (originalAddress bob)) false view
  | 13 => earlyCommand alice past view
  | 14 => pollCommand bob (seeds.2 (originalAddress bob)) true view
  | 15 => lateCommand bob (seeds.2 (originalAddress bob)) 4 past view
  | 17 => activateReady bob bobBinding view
  | 18 => lateCommand bob (seeds.2 (originalAddress bob)) 5 past view
  | 20 => .application (.expire aliceBinding)
  | 21 => .application (.expire bobBinding)
  | _ => .wait

/-- A newly installed full namespace starts its own command block immediately. -/
def tailIndex (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : Nat :=
  past.length - past.findIdx (fun entry =>
    entry.beforeView.application.attempt = view.application.attempt)

def survivor (view : app.EnvironmentView) : Player :=
  if alice ∈ view.application.excluded then bob else alice

def retryCommand (position : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  let owner := survivor view
  match position with
  | 0 => activateReady owner (bindingEvent owner) view
  | 1 => responseCommand owner past view
  | 2 | 3 | 4 | 5 | 6 | 7 => .application .advanceClock
  | 8 => .application (.expire (bindingEvent owner))
  | _ => .wait

/-- All surviving ready reveal owners receive their callback and inclusion
before the first advance of the shared clock. -/
def revealCommand (position : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match position with
  | 0 => activateReady alice aliceReveal view
  | 1 => responseCommand alice past view
  | 2 => activateReady bob bobReveal view
  | 3 => responseCommand bob past view
  | 4 | 5 | 6 | 7 | 8 | 9 => .application .advanceClock
  | 10 => .application (.expire aliceReveal)
  | 11 => .application (.expire bobReveal)
  | _ => .wait

def choose (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  if view.application.attempt = originalAttempt then
    originalCommand seeds past.length past view
  else
    match view.application.phase with
    | some (.commitment, _, _) => retryCommand (tailIndex past view) past view
    | some (.reveal, _, _) => revealCommand (tailIndex past view) past view
    | some (.sample, _, _) | none => .wait

def family (seeds : Seeds) : app.Scheduler :=
  fun past view => PMF.pure (choose seeds past view)

def implementation : app.SchedulerImplementation Seeds :=
  app.schedulerMixture seedPrior family

def scheduler : app.Scheduler := implementation.scheduler

instance finiteLeaks : leaks.FiniteSupport := by
  unfold leaks
  infer_instance

theorem scheduler_eq_posterior (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    scheduler past view = (implementation.posterior past).map
      (fun seeds => choose seeds past view) := by
  rw [scheduler, ReactiveApplication.SchedulerImplementation.scheduler_eq]
  change ((implementation.posterior past).bind fun seeds =>
    (PMF.pure (choose seeds past view)).map (fun command => (command, seeds))).map Prod.fst = _
  simp only [PMF.pure_map, PMF.map_bind]
  rfl

instance finiteNature : app.FiniteNature initial scheduler :=
  phaseApplication_finiteNature runtime leaks initial scheduler (by
    rw [initial_eq_pure, PMF.support_pure]
    exact Set.finite_singleton _) (by
    intro past view
    rw [scheduler_eq_posterior, PMF.support_map]
    exact (Set.toFinite _).image _)

instance familyFiniteNature (seeds : Seeds) : app.FiniteNature initial (family seeds) :=
  phaseApplication_finiteNature runtime leaks initial (family seeds) (by
    rw [initial_eq_pure, PMF.support_pure]
    exact Set.finite_singleton _) (by
    intro past view
    rw [family, PMF.support_pure]
    exact Set.finite_singleton _)

theorem choose_original (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (original : view.application.attempt = originalAttempt) :
    choose seeds past view = originalCommand seeds past.length past view := by
  simp only [choose, ite_eq_left original]

theorem choose_reveal (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (retired : view.application.attempt ≠ originalAttempt)
    (phase : ∃ low high, view.application.phase = some (.reveal, low, high)) :
    choose seeds past view = revealCommand (tailIndex past view) past view := by
  obtain ⟨low, high, phase⟩ := phase
  simp only [choose, ite_eq_right retired, phase]

theorem family_apply (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) :
    family seeds past view = PMF.pure (choose seeds past view) := rfl

theorem originalCommand_bound (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (ended : 22 ≤ position) :
    originalCommand seeds position past view = .wait := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
      18 | 19 | 20 | 21 => omega
  | n + 22 => rfl

theorem revealCommand_bound (position : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (ended : 12 ≤ position) :
    revealCommand position past view = .wait := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => omega
  | n + 12 => rfl

theorem retryCommand_bound (position : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (ended : 9 ≤ position) :
    retryCommand position past view = .wait := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => omega
  | n + 9 => rfl

theorem original_realize (players : Player → app.Policy) (count : Nat) (state : app.State) :
    (seedPrior.bind fun seeds => app.runRounds (family seeds) players count
      (ReactiveApplication.Execution.initial app state)) =
        app.runRounds scheduler players count (ReactiveApplication.Execution.initial app state) :=
  app.schedulerMixture_realize seedPrior family players count state

end Vegas.Examples.CommitSeedSignalling
