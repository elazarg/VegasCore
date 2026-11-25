module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ReactiveCanonicalDecision
public import Vegas.Pending.ReactiveSubmissionRecall

@[expose] public section

/-! # The timed ledger response to a fixed graph action -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : EventGraph Player L} (timeouts : EventTimeouts graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => (reactiveApplication timeouts) leaks

/-- The owner's response with its graph action fixed. It uses the canonical
decision when it transmits and a fresh call still fits the deadline within the
inclusion bound, and silence when the decision is silent, too late, or the event is
already recorded in the owner's own recall. -/
def fixedOpportunity (bound : graph.EventId → Nat) (owner : Player)
    (event : graph.EventId) (action : graph.Action event) :
    (app).Policy := fun past view =>
  if eventRecorded timeouts leaks past event then (app).silentPolicy past view
  else if view.application.publicView.InclusionFitsDeadline timeouts bound event then
    if (canonicalServiceDecision timeouts leaks owner past view event action).transmission = none
    then (app).silentPolicy past view
    else PMF.pure (canonicalServiceDecision timeouts leaks owner past view event action)
  else (app).silentPolicy past view

variable {timeouts leaks}

/-- A silent canonical decision stays silent at the bounded opportunity. -/
theorem fixedOpportunity_silent {bound : graph.EventId → Nat} {owner : Player}
    {event : graph.EventId} (action : graph.Action event)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (quiet : (canonicalServiceDecision timeouts leaks owner past view event action).transmission =
      none) :
    fixedOpportunity timeouts leaks bound owner event action past view = PMF.pure ⟨none⟩ := by
  unfold fixedOpportunity
  simp only [quiet, ↓reduceIte, ReactiveApplication.silentPolicy_apply]
  split_ifs <;> rfl

end Vegas.EventGraphRuntime
