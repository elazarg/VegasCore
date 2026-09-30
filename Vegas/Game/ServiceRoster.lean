/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPolicy
import Vegas.Game.RevealServiceClock
import Vegas.Pending.ReactiveServiceGrant

/-! # Finite activation rosters in the existing native service

Each event has a public finite activation roster, then protected inclusion or
public sampling, followed by clock ticks and expiry. Every listed player has
the full native response interface and its given passive observation rule.
The scheduler reads its own command count; that count is not added to player
observations. This is a service instance, not another interpreter or language.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

def rosterBlock (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    List (ServiceInstruction (graph setup)) :=
  (rosters event).map ServiceInstruction.player ++
    (match (graph setup).actor? event with
    | none => [.sample event]
    | some owner => [.includeLatest event owner]) ++
      List.replicate (event.val + 1) .tick ++ [.expire event]

def rosterPlanPrefix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    List (ServiceInstruction (graph setup)) :=
  ((List.finRange (graph setup).order.eventCount).take rank).flatMap (rosterBlock setup rosters)

def rosterPlan (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : List (ServiceInstruction (graph setup)) :=
  (List.finRange (graph setup).order.eventCount).flatMap (rosterBlock setup rosters)

def rosterScheduler (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) : (application setup leaks).Scheduler :=
  fun past view => match (rosterPlan setup rosters)[past.length]? with
    | none => PMF.pure .wait
    | some instruction => (runtime setup).interactionInstruction leaks network past view instruction

/-- A finitely supported prior, leak rule, and network policy make all of the
roster service's nature branch finitely. -/
instance rosterScheduler_finiteNature (setup : Setup (Player := Player) (L := L))
    [setup.FiniteInitialLaw]
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    [leaks.FiniteSupport] (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks) [network.FiniteSupport] :
    (application setup leaks).FiniteNature (initialLaw setup)
      (rosterScheduler setup leaks rosters network) where
  initial_finite := by
    rw [initialLaw, PMF.support_map]
    exact setup.initialLaw_support_finite.image _
  scheduler_finite past view := by
    unfold rosterScheduler
    split
    · simp
    · exact (runtime setup).interactionInstruction_support_finite leaks network past view _

/-- Every event actor has an activation at its own event. The compiler theorems
assume this coverage: without it an owner could never bind or open, so a source
choice would be unavailable in the native game. -/
def ActorOpportunities (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : Prop :=
  ∀ event owner, (graph setup).actor? event = some owner → owner ∈ rosters event

/-- Every binding owner has an activation at its binding event. This is the
part of `ActorOpportunities` that service conformance and repair use. -/
def BindingOpportunities (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) : Prop :=
  ∀ event owner payload,
    (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event

/-- A binding event is owned by the player it binds for. -/
theorem binding_actor (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (kind : (graph setup).outputLayout event = .binding owner payload) :
    (graph setup).actor? event = some owner := by
  have castActor : (cast (congrArg (EventGraph.EventCode (graph setup).layout) kind)
      ((graph setup).nodes event)).actor = some owner := by
    generalize cast (congrArg (EventGraph.EventCode (graph setup).layout) kind)
      ((graph setup).nodes event) = code
    cases code
    rfl
  exact (EventGraph.EventCode.actor_cast kind ((graph setup).nodes event)).symm.trans castActor

theorem ActorOpportunities.binding {setup : Setup (Player := Player) (L := L)}
    {rosters : (graph setup).EventId → List Player}
    (opportunities : ActorOpportunities setup rosters) : BindingOpportunities setup rosters :=
  fun event owner payload kind =>
    opportunities event owner (binding_actor setup event owner payload kind)

theorem rosterBlock_of_owner (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (owner : Player) (owned : (graph setup).actor? event = some owner) :
    rosterBlock setup rosters event =
      ((rosters event).map ServiceInstruction.player ++ [.includeLatest event owner]) ++
        List.replicate (event.val + 1) .tick ++ [.expire event] := by
  simp only [rosterBlock, owned, List.append_assoc]

theorem rosterBlock_length (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    (rosterBlock setup rosters event).length = (rosters event).length + event.val + 3 := by
  unfold rosterBlock
  cases (graph setup).actor? event <;>
    simp only [List.length_append, List.length_map, List.length_cons, List.length_nil,
      List.length_replicate] <;> omega

theorem rosterBlock_actors (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    (rosterBlock setup rosters event).filterMap instructionActor = rosters event := by
  unfold rosterBlock
  cases (graph setup).actor? event <;> simp [instructionActor]

theorem rosterBlock_no_wire (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    ServiceInstruction.wire ∉ rosterBlock setup rosters event := by
  unfold rosterBlock
  cases (graph setup).actor? event <;> simp

theorem rosterBlock_no_grant (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (block event : (graph setup).EventId) :
    ServiceInstruction.grant event ∉ rosterBlock setup rosters block := by
  unfold rosterBlock
  cases (graph setup).actor? block <;> simp

theorem rosterPlanPrefix_succ (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    rosterPlanPrefix setup rosters (event.val + 1) =
      rosterPlanPrefix setup rosters event.val ++ rosterBlock setup rosters event := by
  simp only [rosterPlanPrefix, List.take_add_one, List.flatMap_append]
  have selected : (List.finRange (graph setup).order.eventCount)[event.val]? = some event := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_finRange] using event.isLt),
      List.getElem_finRange]
    exact congrArg some (Fin.ext rfl)
  simp only [selected, Option.toList_some, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The instructions after an event's roster visits: protected inclusion of the
owner's latest response, or public sampling for an actorless event, then the
clock ticks and expiry. -/
def rosterPhaseEnding (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) : List (ServiceInstruction (graph setup)) :=
  (match (graph setup).actor? event with
    | none => [.sample event]
    | some owner => [.includeLatest event owner]) ++
    List.replicate (event.val + 1) .tick ++ [.expire event]

theorem rosterBlock_eq_ending (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    rosterBlock setup rosters event =
      (rosters event).map ServiceInstruction.player ++ rosterPhaseEnding setup event := by
  simp only [rosterBlock, rosterPhaseEnding, List.append_assoc]

/-- The service plan after its first `rank` event blocks. -/
def rosterPlanSuffix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    List (ServiceInstruction (graph setup)) :=
  ((List.finRange (graph setup).order.eventCount).drop rank).flatMap (rosterBlock setup rosters)

theorem rosterPlanPrefix_append_suffix (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    rosterPlanPrefix setup rosters rank ++ rosterPlanSuffix setup rosters rank =
      rosterPlan setup rosters := by
  simp only [rosterPlanPrefix, rosterPlanSuffix, rosterPlan, ← List.flatMap_append,
    List.take_append_drop]

theorem rosterPlanPrefix_actors (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    (rosterPlanPrefix setup rosters rank).filterMap instructionActor =
      ((List.finRange (graph setup).order.eventCount).take rank).flatMap rosters := by
  simp only [rosterPlanPrefix, List.filterMap_flatMap, rosterBlock_actors]

theorem rosterPlanPrefix_no_wire (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) :
    ServiceInstruction.wire ∉ rosterPlanPrefix setup rosters rank := by
  intro member
  obtain ⟨event, _, inside⟩ := List.mem_flatMap.mp member
  exact rosterBlock_no_wire setup rosters event inside

omit [DecidableEq Player] in
/-- A nonempty suffix of the event order starts at its rank. -/
theorem finRange_drop_cons {count rank : Nat} {event : Fin count} {rest : List (Fin count)}
    (same : event :: rest = (List.finRange count).drop rank) :
    event.val = rank ∧ rest = (List.finRange count).drop (rank + 1) := by
  have inside : rank < count := by
    by_contra outside
    rw [List.drop_eq_nil_of_le (by simpa only [List.length_finRange] using not_lt.mp outside)]
      at same
    cases same
  rw [List.drop_eq_getElem_cons (by simpa only [List.length_finRange] using inside),
    List.getElem_finRange] at same
  obtain ⟨head, tail⟩ := List.cons.inj same
  exact ⟨by rw [head]; rfl, tail⟩

theorem rosterPlanPrefix_no_grant (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (rank : Nat) (event : (graph setup).EventId) :
    ServiceInstruction.grant event ∉ rosterPlanPrefix setup rosters rank := by
  intro member
  obtain ⟨block, _, inside⟩ := List.mem_flatMap.mp member
  exact rosterBlock_no_grant setup rosters block event inside

/-- No roster instruction sets the service grant. -/
theorem roster_prefix_serviceGrant (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) (rank : Nat)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks players network
      (rosterPlanPrefix setup rosters rank) initial).support) :
    final.application.serviceGrant = initial.application.serviceGrant :=
  (runtime setup).runInteractionPlan_serviceGrant leaks players network _
    (rosterPlanPrefix_no_wire setup rosters rank) (rosterPlanPrefix_no_grant setup rosters rank)
    initial final reached

theorem rosterPlan_split (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId) :
    ∃ suffix, rosterPlan setup rosters =
      rosterPlanPrefix setup rosters event.val ++ rosterBlock setup rosters event ++ suffix := by
  let events := List.finRange (graph setup).order.eventCount
  refine ⟨(events.drop (event.val + 1)).flatMap (rosterBlock setup rosters), ?_⟩
  have split := congrArg (List.flatMap (rosterBlock setup rosters))
    (events.take_append_drop (event.val + 1))
  rw [List.flatMap_append] at split
  change rosterPlanPrefix setup rosters (event.val + 1) ++ _ = rosterPlan setup rosters at split
  rw [rosterPlanPrefix_succ] at split
  exact split.symm

/-- Every plan segment is exactly the existing native game scheduler, from
its service position and for arbitrary response policies. -/
theorem roster_segment_rounds (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (players : Player → (application setup leaks).Policy)
    (before rest after : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ rest ++ after)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = before.length) :
    (application setup leaks).runRounds (rosterScheduler setup leaks rosters network)
      players rest.length execution =
        (runtime setup).runInteractionPlan leaks players network rest execution := by
  induction rest generalizing before execution with
  | nil => rfl
  | cons instruction rest ih =>
      have selected : (rosterPlan setup rosters)[before.length]? = some instruction := by
        rw [split, List.append_assoc, List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
        rfl
      have step : (application setup leaks).round (rosterScheduler setup leaks rosters network)
          players execution = (runtime setup).interactionStep leaks players network
            instruction execution := by
        simp only [ReactiveApplication.round, rosterScheduler, position, selected, interactionStep]
      rw [List.length_cons, ReactiveApplication.runRounds, step, runInteractionPlan]
      apply bind_congr_on_support _
      intro next supported
      apply ih (before ++ [instruction])
      · simpa only [List.append_assoc, List.singleton_append] using split
      · have advanced := (runtime setup).interactionStep_recall leaks players network instruction
          execution next supported
        simp only [List.length_append, List.length_singleton]
        omega

end Vegas
