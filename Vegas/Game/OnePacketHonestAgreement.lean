/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketHonestDecision
import Vegas.Game.OnePacketLawApproximation

/-! # As-if-honest play agrees with the first-turn clients where they play

The as-if-honest profile of the one-packet game, read as native policies,
sends the as-if-honest response when the one-packet menu offers it and is
silent otherwise (`Vegas.decodeProfile_honestProfile`).

Suppose the canonical menu retains every first canonical packet sent within its
deadline (`Vegas.RetainsFirstCanonical`). Then, for a well-formed setup under
the asynchronous contract with timely delays, at every input the scheduler
queries along a run of the first-turn clients of the intended effective
opening, as-if-honest play responds exactly as those clients do
(`Vegas.honestPolicy_eq_openingClients`): without an own turn both are silent;
after an earlier turn at the event both are silent, the clients by their turn
count and as-if-honest play because its packet repeats an own submission; and
at the first turn both make the compiled decision of the effective opening,
which the one-packet menu offers whenever it transmits.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

section Decoded

variable [Fintype Player] (bounds : MessageBounds (graph setup))
  (initial : PMF (application setup leaks).State) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)

open Classical in
/-- A response the one-packet menu offers, and silence otherwise. -/
def onePacketFilter (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action) :
    (application setup leaks).Action :=
  if response ∈ bounds.onePacketActions (runtime setup) leaks who past view then response
  else ⟨none⟩

/-- **As-if-honest play as native policies.** -/
theorem decodeProfile_honestProfile (assessment : setup.intendedModel.BehavioralAssessment)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (bounds.onePacketMenu (runtime setup) leaks).decodeProfile initial horizon scheduler
        (honestProfile setup leaks bounds initial horizon scheduler assessment) who past view =
      (honestResponse setup leaks assessment who past view).map
        (onePacketFilter bounds who past view) := by
  classical
  simp only [ReactiveApplication.ResponseMenu.decodeProfile, ReactiveApplication.decodePolicy,
    ReactiveApplication.ResponseMenu.embedPolicy, honestProfile, honestChoice, PMF.map_comp]
  congr 1
  funext response
  simp only [Function.comp_apply, responseChoice, onePacketFilter]
  split <;> rfl

end Decoded

section Static

/-- Every execution reached by rounds from initialization decodes to a point
carrying the program's registry and publication status. -/
theorem roundsFrom_static (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (profile : BehavioralProfile setup.program)
    (count : Nat) (execution : (application setup leaks).Execution)
    (supported : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support) :
    DecodedExecution setup leaks profile
      (ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context)) execution := by
  obtain ⟨state, stateMem, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ supported)
  obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ stateMem
  refine DecodedExecution.runRounds (fun state joint target holds reached =>
    ProtocolState.staticAt_step setup.program [] (Revelations.initial setup.context) state joint
      target holds reached) scheduler players count _ ?_ execution reached
  let residual := SourceResidual.initial setup profile initial
  refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
  change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial (graph := graph setup)
    (setup.eventInputs initial)).config = some point at decoded
  rw [residual.decode, Option.some.injEq] at decoded
  subst decoded
  exact ProtocolState.staticAt_entry setup.program _ rfl rfl

end Static

section Agreement

variable (setup leaks) in
/-- **Retention of first canonical packets.** At an owner's turn at an event
its recall has not submitted for, while a fresh call still fits the deadline,
every transmitting canonical decision is retained by the canonical menu. -/
def RetainsFirstCanonical [Fintype Player] (bounds : MessageBounds (graph setup))
    (bound : (graph setup).EventId → Nat) : Prop :=
  ∀ who (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (event : (graph setup).EventId)
    (action : (graph setup).Action event),
    view.application.publicView.ownTurn? who = some event →
    (runtime setup).eventRecorded leaks past event = false →
    view.application.publicView.InclusionFitsDeadline (runtime setup) bound event →
    ((runtime setup).canonicalServiceDecision leaks who past view event action).transmission ≠
      none →
    (runtime setup).canonicalServiceDecision leaks who past view event action ∈
      bounds.canonicalActions (runtime setup) leaks who past view

end Agreement

end Vegas
