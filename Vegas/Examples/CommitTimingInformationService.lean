/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitTimingInformationSource
import Vegas.Game.CompiledRuntimePhases
import Vegas.Pending.PhasePrivateService
import Vegas.Pending.PhaseFiniteNature
import Interaction.CompletePendingObservation

/-! # Native service with a private timing signal and a late fallback

Alice's first packet is included at clock one. Her clock-two activation
straddles Bob's first response and receipt, according to her original seed.
Clock-three and clock-four submissions have separate admission windows.
Every subsequent namespace receives immediate protected response service.
-/

noncomputable section

namespace Vegas.Examples.CommitTimingInformation

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

def runtime : EventGraphRuntime graph where
  deadline := fun _ => 7

def leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph) :=
  MessageNetwork.completePendingObservation

abbrev app := phaseApplication runtime leaks

def plan : RuntimePhasePlan graph := compiledRuntimePhasePlan program .concurrentReveals

def initialState (bit : Bool) : app.State :=
  PhaseRuntimeState.initial plan (encodeInputs (sourceInitial bit))

def initial : PMF app.State :=
  (setup.initialLaw.map encodeInputs).map (PhaseRuntimeState.initial plan)

def initialExecution (bit : Bool) : app.Execution :=
  ReactiveApplication.Execution.initial app (initialState bit)

theorem initialState_clock (bit : Bool) : (initialState bit).current.native.clock = 0 := by
  unfold initialState PhaseRuntimeState.initial
  rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.2]
  rfl

theorem initialState_candidate (bit : Bool) (owner : Player) (serial : Nat) :
    (initialState bit).current.native.candidates.lookup (owner, .prepared serial) = .fresh := by
  unfold initialState PhaseRuntimeState.initial
  rw [(PhaseRuntimeState.settle_physical _ _ _ _ _).2.1]
  exact State.initial_candidate _ owner (.prepared serial)

abbrev horizon : Nat := 128

def bounds : MessageBounds graph where
  candidateCount := 128
  values := Finset.univ.image fun bit : Bool => (⟨.bool, bit⟩ : Raw simpleExpr)

abbrev rawMenu := PhaseCount.rawMenu runtime leaks bounds
abbrev countedMenu := PhaseCount.onePacketMenu runtime leaks bounds

def originalAttempt : CommitAttemptId := ⟨0, 0⟩

def originalCoordinate (owner : Player) : CommitAttemptEvent graph :=
  ⟨originalAttempt, bindingEvent owner⟩

def originalAddress (owner : Player) : PhaseSeedAddress graph :=
  ⟨originalCoordinate owner, by
    constructor
    · change 0 < 4
      decide
    · change 0 ≤ 2
      decide⟩

/-- Alice's original clock-two eligibility and independent clock-four fallback. -/
abbrev Seeds := Bool × Bool

def reactionDelay (event : graph.EventId) : Nat :=
  if graph.actor? event = some alice then 0 else 2

def inclusionBound (event : graph.EventId) : Nat :=
  if graph.actor? event = some alice then 6 else 4

theorem service_margin (event : graph.EventId) :
    reactionDelay event + inclusionBound event < runtime.deadline event := by
  by_cases owned : graph.actor? event = some alice <;>
    simp [reactionDelay, inclusionBound, runtime, owned]

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

/-- The first advance retains the complete output of Alice's clock-zero response. -/
def earlyCommand (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match past[1]? with
  | none => .wait
  | some entry =>
      match entry.beforeView.network.inputs.find? (fun message =>
          message.sender = alice ∧ message.payload.attempt = originalAttempt) with
      | none => .wait
      | some message => pendingCommand message.id view

open Classical in
/-- A silent or skipped activation never selects an older envelope. -/
def responseCommand (owner : Player) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  match past.getLast? with
  | none => .wait
  | some entry =>
      if entry.command = .activate owner ∧
          entry.beforeView.network.nextSerial owner < view.network.nextSerial owner then
        pendingCommand (owner, entry.beforeView.network.nextSerial owner) view
      else .wait

def aliceEmissionCommand (clock : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  if ready alice (bindingEvent alice) view then
    match (PhaseSeedScheduler.localInput runtime leaks (originalCoordinate alice) alice
        past view).emissions.find? (fun emitted => emitted.1 = clock) with
    | none => .wait
    | some emitted => pendingCommand emitted.2.id view
  else .wait

def aliceLateCommand (eligible : Bool) (clock : Nat) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) : app.Command :=
  if eligible then aliceEmissionCommand clock past view else .wait

def alicePollCommand (good wanted : Bool) (view : app.EnvironmentView) : app.Command :=
  if good = wanted then activateReady alice (bindingEvent alice) view else .wait

/-- Original requests expire at clock seven; a retired request needs no later receipt. -/
def originalCommand (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  match position with
  | 0 => activateReady alice (bindingEvent alice) view
  | 1 | 3 | 9 | 14 | 17 | 18 | 19 => .application .advanceClock
  | 2 => earlyCommand past view
  | 4 => alicePollCommand seeds.1 true view
  | 5 => activateReady bob (bindingEvent bob) view
  | 6 => responseCommand bob past view
  | 7 => alicePollCommand seeds.1 false view
  | 8 => aliceLateCommand seeds.1 2 past view
  | 10 => activateReady alice (bindingEvent alice) view
  | 11 => activateReady bob (bindingEvent bob) view
  | 12 => responseCommand bob past view
  | 13 => aliceLateCommand (!seeds.1) 3 past view
  | 15 => activateReady alice (bindingEvent alice) view
  | 16 => aliceLateCommand seeds.2 4 past view
  | 20 => .application (.expire (bindingEvent alice))
  | 21 => .application (.expire (bindingEvent bob))
  | _ => .wait

def tailIndex (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : Nat :=
  past.length - past.findIdx (fun entry =>
    entry.beforeView.application.attempt = view.application.attempt)

/-- Both active owners are serviced before the first clock advance of a fresh namespace. -/
def tailCommand (event : Player → graph.EventId) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) : app.Command :=
  match position with
  | 0 => activateReady alice (event alice) view
  | 1 => responseCommand alice past view
  | 2 => activateReady bob (event bob) view
  | 3 => responseCommand bob past view
  | 4 | 5 | 6 | 7 | 8 | 9 | 10 => .application .advanceClock
  | 11 => .application (.expire (event alice))
  | 12 => .application (.expire (event bob))
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

theorem family_support (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (command : app.Command) :
    command ∈ (family seeds past view).support ↔ command = choose seeds past view :=
  PMF.mem_support_pure_iff _ _

instance finiteLeaks : leaks.FiniteSupport := by
  unfold leaks
  infer_instance

theorem initial_eq_bitLaw : initial = bitLaw.map initialState := by
  change ((bitLaw.map sourceInitial).map encodeInputs).map
    (PhaseRuntimeState.initial plan) = _
  simp only [PMF.map_comp]
  rfl

instance familyFiniteNature (seeds : Seeds) : app.FiniteNature initial (family seeds) :=
  phaseApplication_finiteNature runtime leaks initial (family seeds) (by
    rw [initial_eq_bitLaw, PMF.support_map]
    exact (Set.toFinite _).image _) (by
    intro past view
    rw [family, PMF.support_pure]
    exact Set.finite_singleton _)

theorem choose_original (seeds : Seeds) (past : List app.EnvironmentEntry)
    (view : app.EnvironmentView) (original : view.application.attempt = originalAttempt) :
    choose seeds past view = originalCommand seeds past.length past view := by
  simp only [choose, ite_eq_left original]

theorem originalCommand_bound (seeds : Seeds) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (later : 22 ≤ position) :
    originalCommand seeds position past view = .wait := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 |
      18 | 19 | 20 | 21 => omega
  | _ + 22 => rfl

theorem tailCommand_bound (event : Player → graph.EventId) (position : Nat)
    (past : List app.EnvironmentEntry) (view : app.EnvironmentView) (later : 13 ≤ position) :
    tailCommand event position past view = .wait := by
  match position with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 | 12 => omega
  | _ + 13 => rfl

end Vegas.Examples.CommitTimingInformation
