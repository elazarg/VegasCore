module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.TurnSubmissionDiscipline
public import Vegas.Pending.FixedOpportunity

@[expose] public section

/-! # Event identities and fresh submissions of timed ledger clients -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- A submission from a timed client names its current turn and has no earlier record
in the player's own recall. This holds for every timing distribution. -/
theorem turnPolicy_submission (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns) (client : graph.BehavioralProfile)
    (owner : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action)
    (member : response ∈ (turnPolicy timeouts leaks bound turns timing client owner past
      view).support) (event : graph.EventId)
    (named : submittedEvent? timeouts leaks response = some event) :
    view.application.publicView.ownTurn? owner = some event ∧
      eventRecorded timeouts leaks past event = false := by
  have silent (chosen : response ∈ ((app).silentPolicy past view).support) : False := by
    obtain rfl := (app).silentPolicy_cases past view response chosen
    cases named
  have serving := turnPolicy_submitsAtTurn timeouts leaks bound turns timing client owner past
    view response member event named
  refine ⟨serving, ?_⟩
  have owned := (view.application.publicView.ownTurn?_spec owner event serving).2
  simp only [turnPolicy, serving, dite_eq_left owned, ReactiveApplication.policyMixture_policy,
    PMF.support_bind] at member
  obtain ⟨slot, _, branch⟩ := Set.mem_iUnion₂.mp member
  by_contra recorded
  have already := Bool.eq_true_of_not_eq_false recorded
  simp only [turnFamily, ReactiveApplication.turnScheduledPolicy, referenceOpportunity, already,
    ↓reduceIte, ite_self] at branch
  exact silent branch

/-- Fixing the action at its first turn also prevents a repeat submission of the event. -/
theorem fixedAction_noRepeatedEvent (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns) (client : graph.BehavioralProfile)
    (owner : Player) (event : graph.EventId) (action : graph.Action event)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (member : response ∈ (if turnIndex timeouts leaks owner event past view = some 0
      then fixedOpportunity timeouts leaks bound owner event action past view
      else turnPolicy timeouts leaks bound turns timing client owner past view).support)
    (recorded : eventRecorded timeouts leaks past event = true) :
    submittedEvent? timeouts leaks response ≠ some event := by
  intro named
  split at member
  · simp only [fixedOpportunity, recorded, ↓reduceIte, ReactiveApplication.silentPolicy_apply,
      PMF.mem_support_pure_iff] at member
    subst response
    cases named
  · have fresh := (turnPolicy_submission timeouts leaks bound turns timing client owner past view
      response member event named).2
    simp [recorded] at fresh

end Vegas.EventGraphRuntime
