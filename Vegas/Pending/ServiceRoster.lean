module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.Sequential
public import Vegas.Pending.ReactiveService

@[expose] public section

/-! # Finite activation rosters in the native service

Each event has a public finite activation roster, then protected inclusion or
public sampling, followed by clock ticks and expiry. The plan tags every
instruction with its event. A block whose event was complete at entry retains
its activations and inclusion check but contributes no clock ticks. The entry
test uses the recorded public environment view, without private scheduler state.
-/

noncomputable section

namespace Vegas

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type}
  {L : IExpr} [IExpr.ResultTypes L]

/-- Rank deadlines for the sequential graph roster. -/
abbrev rosterTimeouts (graph : EventGraph Player L) : EventTimeouts graph.sequentialize :=
  ⟨fun event => event.val + 1⟩

/-- Roster commands run on the graph in event-rank order. -/
abbrev rosterApplication [DecidableEq Player] (graph : EventGraph Player L)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize)) :=
  (reactiveApplication (rosterTimeouts graph)) leaks

/-- Initialize the sequential graph roster from a law on its typed inputs. -/
abbrev rosterInitialLaw [DecidableEq Player] (graph : EventGraph Player L)
    (inputs : PMF graph.Inputs) :
    PMF (EventGraphRuntime.State graph.sequentialize) :=
  inputs.map EventGraphRuntime.State.initial

def rosterBlock (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (event :
      graph.EventId) :
    List (ServiceInstruction graph.sequentialize) :=
  let opening : List (ServiceInstruction graph.sequentialize) :=
    match graph.sequentialize.actor? event with
    | none => [.sample event]
    | some owner => [.includeLatest event owner]
  (rosters event).map ServiceInstruction.player ++ opening ++
    List.replicate (event.val + 1) .tick ++ [.expire event]

theorem rosterBlock_no_wire (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (event :
      graph.EventId) :
    ServiceInstruction.wire ∉ rosterBlock graph rosters event := by
  unfold rosterBlock
  cases graph.sequentialize.actor? event <;> simp

def rosterPlanPrefix (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (rank : Nat) :
    List (graph.EventId × ServiceInstruction graph.sequentialize) :=
  ((List.finRange graph.order.eventCount).take rank).flatMap fun event =>
    (rosterBlock graph rosters event).map (Prod.mk event)

def rosterPlan (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) :
    List (graph.EventId × ServiceInstruction graph.sequentialize) :=
  (List.finRange graph.order.eventCount).flatMap fun event =>
    (rosterBlock graph rosters event).map (Prod.mk event)

theorem rosterPlan_no_wire (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (target :
      graph.EventId) :
    (target, ServiceInstruction.wire) ∉ rosterPlan graph rosters := by
  intro member
  obtain ⟨event, _, inside⟩ := List.mem_flatMap.mp member
  obtain ⟨instruction, inside, same⟩ := List.mem_map.mp inside
  cases same
  exact rosterBlock_no_wire graph rosters _ inside

section Scheduler

variable [DecidableEq Player]

/-- The public view at the first instruction of an event's block determines
whether that block was already completed. At its first instruction the current
view supplies the entry observation. -/
def rosterBlockCompleted (graph : EventGraph Player L)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (past : List (rosterApplication graph leaks).EnvironmentEntry)
    (view : (rosterApplication graph leaks).EnvironmentView)
    (event : graph.EventId) : Prop :=
  event ∈ ((past[(rosterPlanPrefix graph rosters event.val).length]?).elim view
    (fun entry => entry.beforeView)).application.observation.completionOrder

instance (graph : EventGraph Player L)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (past : List (rosterApplication graph leaks).EnvironmentEntry)
    (view : (rosterApplication graph leaks).EnvironmentView)
    (event : graph.EventId) :
    Decidable (rosterBlockCompleted graph leaks rosters past view event) := by
  unfold rosterBlockCompleted
  infer_instance

/-- Execute the tagged calendar. Only ticks of blocks already completed at
entry become waits; all actual roster responses remain available. -/
def rosterScheduler (graph : EventGraph Player L)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks) :
    (rosterApplication graph leaks).Scheduler :=
  fun past view => match (rosterPlan graph rosters)[past.length]? with
    | none => PMF.pure .wait
    | some (event, .tick) => PMF.pure
        (if rosterBlockCompleted graph leaks rosters past view event then .wait
          else .application .advanceClock)
    | some (_, instruction) =>
        (interactionInstruction (rosterTimeouts graph)) leaks network past view instruction

/-- A finitely supported prior and leak rule make all of the roster service's
nature branch finitely. The roster never calls its network policy. -/
instance rosterScheduler_finiteNature (graph : EventGraph Player L)
    (inputs : PMF graph.Inputs) [Fact inputs.support.Finite]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph.sequentialize))
    [leaks.FiniteSupport] (rosters : graph.EventId → List Player)
    (network : (NetworkPolicy (rosterTimeouts graph)) leaks) :
    (rosterApplication graph leaks).FiniteNature (rosterInitialLaw graph inputs)
      (rosterScheduler graph leaks rosters network) where
  initial_finite := by
    rw [rosterInitialLaw, PMF.support_map]
    exact (Fact.out : inputs.support.Finite).image _
  scheduler_finite past view := by
    cases selected : (rosterPlan graph rosters)[past.length]? with
    | none => simp [rosterScheduler, selected]
    | some pair =>
        rcases pair with ⟨target, instruction⟩
        have reserved : instruction ≠ .wire := by
          intro same
          have member := List.mem_of_getElem? selected
          rw [same] at member
          exact rosterPlan_no_wire graph rosters target member
        cases instruction <;> simp_all [rosterScheduler, interactionInstruction]

end Scheduler

/-- Every event actor has an activation at its own event. The compiler theorems
assume this coverage: without it an owner could never bind or open, so a source
choice would be unavailable in the native game. -/
def ActorOpportunities (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) : Prop :=
  ∀ event owner, graph.sequentialize.actor? event = some owner → owner ∈ rosters event

/-- Give each owned event one activation and leave chance events' rosters empty. -/
def ownerRoster (graph : EventGraph Player L) (event : graph.EventId) : List Player :=
  (graph.sequentialize.actor? event).toList

theorem ownerRoster_opportunities (graph : EventGraph Player L) :
    ActorOpportunities graph (ownerRoster graph) := by
  intro event owner owned
  simp [ownerRoster, owned]

theorem ownerRoster_length_le_one (graph : EventGraph Player L) (event : graph.EventId) :
    (ownerRoster graph event).length ≤ 1 := by
  cases owned : graph.sequentialize.actor? event <;> simp [ownerRoster, owned]

/-- Every binding owner has an activation at its binding event. This is the
part of `ActorOpportunities` that service conformance and repair use. -/
def BindingOpportunities (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) : Prop :=
  ∀ event owner payload,
    graph.sequentialize.outputLayout event = .binding owner payload → owner ∈ rosters event

/-- A binding event is owned by the player it binds for. -/
theorem binding_actor (graph : EventGraph Player L)
    (event : graph.EventId) (owner : Player) (payload : L.Ty)
    (kind : graph.sequentialize.outputLayout event = .binding owner payload) :
    graph.sequentialize.actor? event = some owner := by
  have castActor : (cast (congrArg (EventGraph.EventCode graph.sequentialize.layout) kind)
      (graph.sequentialize.nodes event)).actor = some owner := by
    generalize cast (congrArg (EventGraph.EventCode graph.sequentialize.layout) kind)
      (graph.sequentialize.nodes event) = code
    cases code
    rfl
  exact (EventGraph.EventCode.actor_cast kind (graph.sequentialize.nodes event)).symm.trans
    castActor

theorem ActorOpportunities.binding {graph : EventGraph Player L}
    {rosters : graph.EventId → List Player}
    (opportunities : ActorOpportunities graph rosters) : BindingOpportunities graph rosters :=
  fun event owner payload kind =>
    opportunities event owner (binding_actor graph event owner payload kind)

theorem rosterBlock_length (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (event :
      graph.EventId) :
    (rosterBlock graph rosters event).length = (rosters event).length + event.val + 3 := by
  unfold rosterBlock
  cases graph.sequentialize.actor? event <;>
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
      List.length_replicate] <;> omega

theorem rosterPlanPrefix_succ (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (event :
      graph.EventId) :
    rosterPlanPrefix graph rosters (event.val + 1) =
      rosterPlanPrefix graph rosters event.val ++
        (rosterBlock graph rosters event).map (Prod.mk event) := by
  simp only [rosterPlanPrefix, List.take_add_one, List.flatMap_append]
  have selected : (List.finRange graph.order.eventCount)[event.val]? = some event
    := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using event.isLt),
      List.getElem_finRange]
    exact congrArg some (Fin.ext rfl)
  simp only [selected, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The instructions after an event's roster visits: protected inclusion of the
owner's latest response, or public sampling for an actorless event, then the
clock ticks and expiry. -/
def rosterPhaseEnding (graph : EventGraph Player L)
    (event : graph.EventId) : List (ServiceInstruction graph.sequentialize) :=
  (match graph.sequentialize.actor? event with
    | none => [.sample event]
    | some owner => [.includeLatest event owner]) ++
    List.replicate (event.val + 1) .tick ++ [.expire event]

theorem rosterBlock_eq_ending (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (event :
      graph.EventId) :
    rosterBlock graph rosters event =
      (rosters event).map ServiceInstruction.player ++ rosterPhaseEnding graph event := by
  simp only [rosterBlock, rosterPhaseEnding, List.append_assoc]

/-- The service plan after its first `rank` event blocks. -/
def rosterPlanSuffix (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (rank : Nat) :
    List (graph.EventId × ServiceInstruction graph.sequentialize) :=
  ((List.finRange graph.order.eventCount).drop rank).flatMap fun event =>
    (rosterBlock graph rosters event).map (Prod.mk event)

theorem rosterPlan_split (graph : EventGraph Player L)
    (rosters : graph.EventId → List Player) (event :
      graph.EventId) :
    ∃ suffix, rosterPlan graph rosters =
      rosterPlanPrefix graph rosters event.val ++
        (rosterBlock graph rosters event).map (Prod.mk event) ++ suffix := by
  let events := List.finRange graph.order.eventCount
  let block := fun event => (rosterBlock graph rosters event).map (Prod.mk event)
  refine ⟨(events.drop (event.val + 1)).flatMap block, ?_⟩
  have split := congrArg (List.flatMap block)
    (events.take_append_drop (event.val + 1))
  rw [List.flatMap_append] at split
  change rosterPlanPrefix graph rosters (event.val + 1) ++ _ = rosterPlan graph rosters at split
  rw [rosterPlanPrefix_succ] at split
  exact split.symm

end Vegas
