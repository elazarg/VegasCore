/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphInputs
import Vegas.EventGraph.Sequential
import Vegas.Pending.ReactiveRevealBlock
import Vegas.Pending.ReactiveMonitoring
import Vegas.Pending.ReactiveFiniteResponses
import Vegas.Pending.EventPublicState
import Vegas.Source.ProtocolTermination

/-! # Restricted native service for source revelation sequences

These are constructor functions for the existing event graph, reactive service,
and response menu. The first backend has one ordinary owner activation and one
watcher activation per source event. It therefore has a fixed finite calendar;
it does not model arbitrarily many intervening broadcasts.

Canonical openings are included before the watcher observes pending packets.
Withholding is silence followed by expiry.
Deadlines increase with source rank
so that a successor can remain timely after an early successful predecessor.
The definitions assert no equilibrium property; operational timeliness and the
source-history correspondence are proved in the modules that use them.
-/

noncomputable section

namespace Vegas

open SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem eventCount_eq_instructionCount {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) : eventCount program = instructionCount program := by
  induction program with
  | ret payoffs => rfl
  | sample name fresh law next ih => exact congrArg Nat.succ ih
  | commit name owner fresh guard next ih => exact congrArg Nat.succ ih
  | reveal published owner name fresh source unresolved next ih => exact congrArg Nat.succ ih

end Vegas

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiled event graph under a dependency mode. -/
abbrev serviceGraph (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) : EventGraph Player L :=
  setup.eventGraph.withMode mode

/-- The default service graph: the sequential specialization of the compiled
graph, which is its sequential mode. -/
abbrev graph (setup : Setup (Player := Player) (L := L)) := setup.eventGraph.sequentialize

/-- The service graph of every mode keeps the public-barrier dependencies except
possibly those between independent reveals. -/
theorem serviceGraph_revealRelaxedOrdered (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) : (serviceGraph setup mode).RevealRelaxedOrdered :=
  setup.eventGraph.withMode_revealRelaxedOrdered (toEventGraph_barrierOrdered setup.program) mode

/-- Deadline durations that grow with source rank: an event may stay ready for
its index plus one clock ticks. The fixed calendar needs them increasing. -/
abbrev rankDeadline (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (event : (serviceGraph setup mode).EventId) : Nat :=
  event.val + 1

/-- The service runtime of a dependency mode with a configured deadline duration
per event. The runtime counts each duration from the clock at which the event
became ready (`EventGraphRuntime.State.WithinDeadline`). -/
def serviceRuntime (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode)
    (deadline : (serviceGraph setup mode).EventId → Nat) :
    EventGraphRuntime (serviceGraph setup mode) where
  deadline := deadline

@[simp] theorem serviceRuntime_deadline (setup : Setup (Player := Player) (L := L))
    (mode : EventGraph.ExecutionMode) (deadline : (serviceGraph setup mode).EventId → Nat) :
    (serviceRuntime setup mode deadline).deadline = deadline := rfl

/-- The default service runtime: the sequential graph with `rankDeadline`. -/
abbrev runtime (setup : Setup (Player := Player) (L := L)) : EventGraphRuntime (graph setup) :=
  serviceRuntime setup .sequential (rankDeadline setup .sequential)

/-- In the sequentialized graph a ready event is the only ready event, so each
player either has it as its turn or is idle. -/
theorem soleReady_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) : state.publicView.SoleReady event :=
  ⟨(state.publicView_eventReady event).mpr ready, fun other otherReady =>
    setup.eventGraph.sequentialize_ready_unique state.config.cut
      ((state.publicView_eventReady other).mp otherReady) ready⟩

/-- In every dependency mode a ready event is its actor's turn: a player acts
at most at one ready event. -/
theorem serviceOwnTurn?_of_ready (setup : Setup (Player := Player) (L := L))
    {mode : EventGraph.ExecutionMode}
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    {event : (serviceGraph setup mode).EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (owned : (serviceGraph setup mode).actor? event = some who) :
    state.publicView.ownTurn? who = some event :=
  state.publicView.ownTurn?_of_ownTurn who event
    ⟨(state.publicView_eventReady event).mpr ready, owned, fun other otherReady otherActor =>
      (serviceGraph_revealRelaxedOrdered setup mode).ready_actor_unique state.config.cut
          ready ((state.publicView_eventReady other).mp otherReady) owned otherActor⟩

/-- A ready event is its actor's turn. -/
theorem ownTurn?_of_ready (setup : Setup (Player := Player) (L := L))
    (state : EventGraphRuntime.State (graph setup)) {event : (graph setup).EventId}
    (ready : state.config.cut.Ready event) {who : Player}
    (owned : (graph setup).actor? event = some who) :
    state.publicView.ownTurn? who = some event :=
  serviceOwnTurn?_of_ready (mode := .sequential) setup state ready owned

def block (setup : Setup (Player := Player) (L := L)) (watcher : Player)
    (event : (graph setup).EventId) : List (ServiceInstruction (graph setup)) :=
  (match (graph setup).actor? event with
    | none => []
    | some owner => [.player owner, .includeLatest event owner]) ++
    [.player watcher, .wire] ++ List.replicate ((runtime setup).deadline event) .tick ++
    [.expire event]

def plan (setup : Setup (Player := Player) (L := L)) (watcher : Player) :
    List (ServiceInstruction (graph setup)) :=
  (List.finRange (graph setup).order.eventCount).flatMap (block setup watcher)

section Configured

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

/-- The reactive application of the service runtime of a dependency mode and a
deadline configuration, under an observation rule for pending packets. -/
abbrev serviceApplication := (serviceRuntime setup mode deadline).reactiveApplication leaks

/-- The prior over initial values, compiled to initial states of the service
graph of a dependency mode. -/
def serviceInitialLaw : PMF (EventGraphRuntime.State (serviceGraph setup mode)) :=
  setup.initialLaw.map (fun initial => EventGraphRuntime.State.initial (setup.eventInputs initial))

/-- A finitely supported prior compiles to finitely many initial states. -/
theorem serviceInitialLaw_support_finite [setup.FiniteInitialLaw] :
    (serviceInitialLaw setup mode).support.Finite := by
  rw [serviceInitialLaw, PMF.support_map]
  exact setup.initialLaw_support_finite.image _

end Configured

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- The application of the default runtime. -/
abbrev application := serviceApplication setup .sequential (rankDeadline setup .sequential) leaks

/-- The initial law of the default sequential graph. -/
abbrev initialLaw : PMF (EventGraphRuntime.State (graph setup)) :=
  serviceInitialLaw setup .sequential

/-- The fixed service consults only its own public command recall. Its network
slot is idle: it includes nothing beyond the reserved inclusion of each owner's
latest packet. Private sampling remains the given rule. -/
def scheduler (watcher : Player) : (application setup leaks).Scheduler := fun history view =>
  match (plan setup watcher)[history.length]? with
  | none => PMF.pure .wait
  | some instruction => (runtime setup).interactionInstruction leaks
      ((runtime setup).idleNetwork leaks) history view instruction

/-- With a finitely supported prior and a finitely branching leak rule, all of
the fixed service's nature branches finitely: its own instructions are
deterministic. -/
instance scheduler_finiteNature [setup.FiniteInitialLaw] [leaks.FiniteSupport]
    (watcher : Player) :
    (application setup leaks).FiniteNature (initialLaw setup) (scheduler setup leaks watcher) where
  initial_finite := serviceInitialLaw_support_finite setup .sequential
  scheduler_finite history view := by
    unfold scheduler
    split
    · simp
    · rename_i instruction _
      cases instruction with
      | wire => simp [(runtime setup).idleNetwork_instruction leaks history view]
      | _ => simp [EventGraphRuntime.interactionInstruction]

abbrev horizon (watcher : Player) : Nat := (plan setup watcher).length

/-- A local view determines the sole canonical opening, when the player's turn
is an owned, successfully openable resolution. No private global state is read. -/
def opening? (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Option (application setup leaks).Action := do
  let event ← view.application.publicView.ownTurn? who
  if (graph setup).actor? event ≠ some who then none else
    match nodeView (graph setup) event with
    | .sample .. | .bind .. => none
    | .resolve _ payload binding checks _ _ =>
        match EventGraph.EventCode.resolveOutput? binding checks true
            view.application.observation.store with
        | none | some .failure => none
        | some (.success value) => do
            let candidate ← view.application.publicView.accepted binding.field
            if candidate.1 ≠ who then none else
              some (((runtime setup).reactiveNormalization leaks).action who past view
                ((runtime setup).canonicalRevealResponse leaks event candidate
                  ⟨payload, value⟩ true))

variable [Fintype Player] (bounds : MessageBounds (graph setup))

theorem silence_effective (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (⟨none⟩ : (application setup leaks).Action) ∈
      (bounds.menu (runtime setup) leaks).actions who past view := by
  rw [bounds.menu_mem]
  exact ⟨trivial, rfl⟩

open Classical in
def ordinaryActions (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) : Finset (application setup leaks).Action :=
  (insert ⟨none⟩ (opening? setup leaks who past view).toList.toFinset) ∩
    (bounds.menu (runtime setup) leaks).actions who past view

theorem silence_ordinary (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (⟨none⟩ : (application setup leaks).Action) ∈
      ordinaryActions setup leaks bounds who past view := by
  classical
  exact Finset.mem_inter.mpr ⟨Finset.mem_insert_self _ _,
    silence_effective setup leaks bounds who past view⟩

open Classical in
/-- This restricts the existing native menu to silence and a supported opening.
Source value coverage remains a proof obligation.
The watcher only observes: it transmits nothing at every local input. -/
def menu (watcher : Player) : (application setup leaks).ResponseMenu where
  actions who past view := if who = watcher then {⟨none⟩}
    else ordinaryActions setup leaks bounds who past view
  nonempty who past view := by
    split
    · exact ⟨⟨none⟩, Finset.mem_singleton_self _⟩
    · exact ⟨⟨none⟩, silence_ordinary setup leaks bounds who past view⟩

abbrev protocol (watcher : Player) :=
  (menu setup leaks bounds watcher).protocol (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

abbrev information (watcher : Player) :=
  (menu setup leaks bounds watcher).information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)

end Vegas
