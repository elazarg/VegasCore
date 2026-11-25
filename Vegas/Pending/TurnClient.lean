module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.ReactiveSubmissionRecall
public import Vegas.EventGraph.Semantics
public import Interaction.ReactivePolicyMixture
public import Interaction.ReactiveRecovery
public import Interaction.ScheduledOpening

@[expose] public section

/-! # Ledger clients for graph behavioral profiles -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Distribution of the deciding turn for each owned graph event. -/
protected abbrev TurnTiming (graph : EventGraph Player L) (turns : Nat) :=
  ∀ event who, graph.actor? event = some who → PMF (Fin (turns + 1))

/-- Each owner decides at the first turn for its ready event. -/
protected def firstTurnTiming (graph : EventGraph Player L) (turns : Nat) :
    EventGraphRuntime.TurnTiming graph turns :=
  fun _ _ _ => PMF.pure 0

variable {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- A reference graph profile's decision at the player's turn, realized by the
canonical decision. -/
def referencePolicy (reference : graph.BehavioralProfile)
    (who : Player) : (app).Policy := fun past view =>
  if identity : view.application.who = who then
    match view.application.publicView.ownTurn? who with
    | none => PMF.pure ⟨none⟩
    | some event =>
        if owned : graph.actor? event = some who then
          let observed := identity ▸ view.application.observation
          if inactive : who ∈ observed.defaulted then PMF.pure ⟨none⟩ else
            (reference who event owned observed inactive).map
              (canonicalServiceDecision timeouts leaks who past view event)
        else PMF.pure ⟨none⟩
  else PMF.pure ⟨none⟩

/-- One opportunity of a reference's turn-counted policy: silence once the event
is recorded in the owner's recall or once a fresh call could no longer be
included before the deadline within `bound event` slots; otherwise make the
reference decision, retaining silence if it emits nothing. -/
def referenceOpportunity (bound : graph.EventId → Nat)
    (reference : graph.BehavioralProfile) (who : Player)
    (event : graph.EventId) :
    (app).Policy := fun past view =>
  if (eventRecorded timeouts) leaks past event then
    (app).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline timeouts bound event then
    (referencePolicy timeouts leaks reference who past view).bind fun response =>
      if response.transmission = none then
        (app).silentPolicy past view
      else PMF.pure response
  else (app).silentPolicy past view

/-- The opportunity index of `who`'s current input at `event`: the number of its
recorded turns at `event`, when `event` is its turn now. -/
def turnIndex (who : Player) (event : graph.EventId)
    (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : Option Nat :=
  if view.application.publicView.ownTurn? who = some event then
    some (past.countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event))
  else none

/-- Make a reference's decision at the selected turn and remain silent otherwise. -/
def turnFamily (bound : graph.EventId → Nat)
    (reference : graph.BehavioralProfile) (who : Player)
    (event : graph.EventId) (turns : Nat) (slot : Fin (turns + 1)) :
    (app).Policy :=
  (app).turnScheduledPolicy
    (turnIndex timeouts leaks who event)
    (some slot) (referenceOpportunity timeouts leaks bound reference who event)
    (app).silentPolicy

/-- A reference's turn-counted policy: at its own turn an owner follows the
behavioral realization of the event's timing lottery; otherwise it is silent. -/
def turnPolicy (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (who : Player) : (app).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (app).silentPolicy past view
  | some event =>
      if owned : graph.actor? event = some who then
        ((app).policyMixture (timing event who owned)
          (turnFamily timeouts leaks bound reference who event turns)).policy past view
      else (app).silentPolicy past view

/-- **A reference's client policy.** The turn-counted policy, completed by
silence at every history where the player's own recorded responses do not all
follow it. -/
def clientPolicy (bound : graph.EventId → Nat)
    (turns : Nat) (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (who : Player) : (app).Policy :=
  (turnPolicy timeouts leaks bound turns timing reference who).recover
    (app).silentPolicy

variable {timeouts leaks}

/-- At the first turn the owner has no earlier callback selecting the same event. -/
theorem turnIndex_first {who : Player} {event : graph.EventId} {past : List (app).PlayerEntry}
    {view : (app).PlayerView} (first : turnIndex timeouts leaks who event past view = some 0) :
    view.application.publicView.ownTurn? who = some event ∧
      ∀ entry ∈ past, entry.beforeView.application.publicView.ownTurn? who ≠ some event := by
  unfold turnIndex at first
  split at first
  · rename_i turn
    have counted := Option.some.inj first
    rw [List.countP_eq_zero] at counted
    exact ⟨turn, fun entry member equal => counted entry member (decide_eq_true equal)⟩
  · cases first

/-- On a first-turn timing, the deciding event's policy mixture reduces at every
transcript to the policy for slot zero. -/
theorem firstTurnPolicy_at_turn {bound : graph.EventId → Nat} {turns : Nat}
    {reference : graph.BehavioralProfile} {who : Player}
    {past : List (app).PlayerEntry} {view : (app).PlayerView} {event : graph.EventId}
    (owned : graph.actor? event = some who) (serving : view.application.publicView.ownTurn? who =
      some event) :
    turnPolicy timeouts leaks bound turns (EventGraphRuntime.firstTurnTiming graph turns)
      reference who
      past view =
      turnFamily timeouts leaks bound reference who event turns 0 past view := by
  let family := turnFamily timeouts leaks bound reference who event turns
  have pin : ((app).policyMixture (PMF.pure (0 : Fin (turns + 1))) family).posterior past =
      PMF.pure 0 := by
    simpa only [List.nil_append] using (app).policyMixture_posterior_pure_append
      (PMF.pure (0 : Fin (turns + 1))) family [] past 0 rfl
  simp only [turnPolicy, serving, owned, ↓reduceDIte]
  change ((app).policyMixture (PMF.pure (0 : Fin (turns + 1))) family).policy past view = _
  rw [(app).policyMixture_policy, pin, PMF.pure_bind]

/-- At the first turn for its event, the owner follows the graph profile when a
timely submission is still available. -/
theorem turnPolicy_first {bound : graph.EventId → Nat} {turns : Nat}
    {reference : graph.BehavioralProfile} {who : Player}
    {past : List (app).PlayerEntry} {view : (app).PlayerView} {event : graph.EventId}
    (owned : graph.actor? event = some who)
    (first : turnIndex timeouts leaks who event past view = some 0) :
    turnPolicy timeouts leaks bound turns (EventGraphRuntime.firstTurnTiming graph turns)
      reference who
      past view =
      referenceOpportunity timeouts leaks bound reference who event past view := by
  rw [firstTurnPolicy_at_turn owned (turnIndex_first first).1]
  exact (app).turnScheduledPolicy_selected _ (0 : Fin (turns + 1)) _ _ past view first

/-- Clients using first-turn timing remain silent at later turns for the same event. -/
theorem turnPolicy_later {bound : graph.EventId → Nat} {turns : Nat}
    {reference : graph.BehavioralProfile} {who : Player}
    {past : List (app).PlayerEntry} {view : (app).PlayerView} {event : graph.EventId}
    (owned : graph.actor? event = some who) (serving : view.application.publicView.ownTurn? who =
      some event) (later : turnIndex timeouts leaks who event past view ≠ some 0) :
    turnPolicy timeouts leaks bound turns (EventGraphRuntime.firstTurnTiming graph turns)
      reference who
      past view =
      PMF.pure ⟨none⟩ := by
  rw [firstTurnPolicy_at_turn owned serving]
  exact (app).turnScheduledPolicy_unselected _ (some (0 : Fin (turns + 1))) _ _ past view
    (fun slot selected => by cases selected; exact later)

end Vegas.EventGraphRuntime
