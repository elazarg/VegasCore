module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.SilentAction
public import Vegas.Pending.FixedOpportunity
public import Vegas.Pending.CanonicalTransmission
public import Vegas.Game.SourceServiceReachedDecoding
public import Vegas.Game.SourceServiceTurnPolicy
public import Vegas.Source.DisclosureBehavioral
public import Vegas.Pending.ReactiveCanonicalResolution
public import Vegas.Pending.ReactiveCandidateBudget

@[expose] public section

/-! # First-turn decisions of a fixed source action

The owner's policy deciding one fixed source action at its first turn at an
event, and silent at every other input (`Vegas.decidedTurnPolicy`), makes the
canonical compiled decision of that action while a fresh call still fits the
deadline (`Vegas.EventGraphRuntime.fixedOpportunity`). An action is effective when the compiled
decision realizes it (`Vegas.EventGraphRuntime.EffectiveAction`), including authentic openings
whose deferred guards reject publication. Silence represents binding omission
or a disclosure of `false` (`Vegas.SilentAction`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

/-- Decide `action` at the first turn at `event`, and stay silent at every other
input. -/
def decidedTurnPolicy (bound : (serviceGraph setup deps).EventId → Nat) (owner : Player)
    (event : (serviceGraph setup deps).EventId) (action : (serviceGraph setup deps).Action event) :
    (serviceApplication setup deps duration leaks).Policy :=
  (serviceApplication setup deps duration leaks).turnScheduledPolicy
  (turnIndex (serviceTimeouts setup deps duration) leaks owner event) (some (0 : Fin 1))
  (fixedOpportunity (serviceTimeouts setup deps duration) leaks bound owner event action)
  (serviceApplication setup deps duration leaks).silentPolicy

variable {setup}

variable {leaks}

/-- A fixed silent source action stays silent at every input of its turn policy. -/
theorem decidedTurnPolicy_silent {bound : (serviceGraph setup deps).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup deps).EventId}
    (action : (serviceGraph setup deps).Action event) (silent : SilentAction event action)
    (past : List (serviceApplication setup deps duration leaks).PlayerEntry)
    (view : (serviceApplication setup deps duration leaks).PlayerView) :
    decidedTurnPolicy setup leaks bound owner event action past view = PMF.pure ⟨none⟩ := by
  unfold decidedTurnPolicy ReactiveApplication.turnScheduledPolicy
  dsimp only
  split
  · exact fixedOpportunity_silent action past view
      (canonicalServiceDecision_silent owner past view event action silent)
  · rfl

section Transmission

variable {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  (timeouts : EventTimeouts (serviceGraph setup deps))
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- An effective non-silent source action produces a concrete transmission at
an actual initialized turn, including an authentic opening whose guards reject. -/
theorem canonicalServiceDecision_transmits_of_effective {horizon : Nat}
    {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    (control : ((reactiveApplication timeouts) leaks).Control)
    (trace : (((reactiveApplication timeouts) leaks).protocol
      (serviceInitialDistribution setup deps) horizon scheduler).Trace
      (some control))
    (owner : Player) (event : (serviceGraph setup deps).EventId)
    (turn : control.execution.application.publicView.ownTurn? owner = some event)
    (action : (serviceGraph setup deps).Action event)
    (effective : EffectiveAction control.execution.application.config event action)
    (loud : ¬ SilentAction event action) :
    ∃ material, ((canonicalServiceDecision timeouts) leaks owner (control.execution.logs owner)
      (control.execution.observe ((reactiveApplication timeouts) leaks) owner) event
        action).transmission =
        some material := by
  apply EventGraphRuntime.canonicalServiceDecision_transmits_of_effective timeouts control
    (horizon := horizon) (scheduler := scheduler)
    (inputs := setup.initialDistribution.map setup.eventInputs) _ owner event turn action effective
      loud
  rwa [← serviceInitialDistribution_eq_inputs setup]

end Transmission

end Vegas
