/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Interaction.ReactivePolicyInvariant

/-! # Actual prior commitment traffic after one decision completes

Issued readiness tokens at a ready sequential rank cannot name a later rank.
If the owner sends no further commitments, arbitrary foreign responses and
scheduler commands preserve that bound. Once the current event completes,
every old token-valid owner commitment addresses a completed event.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A bound on the events addressed by actual token-valid owner commitments.
It inspects persisted authenticated input envelopes, not intended raw material. -/
def ownerCommitmentRanksBelow (who : Player) (rank : Nat)
    (execution : (application setup leaks).Execution) : Prop :=
  ∀ message ∈ execution.network.inputs, message.sender = who →
    ∀ event candidate, message.payload.call = .commitment event candidate →
      message.payload.tokenValid = true → event.val ≤ rank

/-- Actual issued tokens at a ready sequential rank cannot authorize a future
event: such authorization would require the ready event to have completed. -/
theorem ownerCommitmentRanksBelow_of_ready
    (execution : (application setup leaks).Execution)
    (facts : SettledFacts setup leaks execution)
    (who : Player) (current : (graph setup).EventId)
    (ready : execution.application.config.cut.Ready current) :
    ownerCommitmentRanksBelow setup leaks who current.val execution := by
  intro message emitted _ event candidate addressed valid
  obtain ⟨named, tokenNamed, tokenEq⟩ := (WitnessedPacket.tokenValid_iff message.payload).mp valid
  rw [addressed] at tokenNamed
  cases Option.some.inj tokenNamed
  by_contra later
  have predecessor : current ∈ (graph setup).order.predecessors event :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.lt_of_not_ge later⟩
  exact ready.1 (facts.issued message emitted ⟨event⟩ tokenEq current predecessor)

/-- Sending no new owner commitments preserves the actual rank bound under
all foreign raw responses, passive sampling, inclusion and application commands. -/
theorem ownerCommitmentRanksBelow_policyInvariant
    (players : Player → (application setup leaks).Policy) (who : Player) (rank : Nat)
    (noncommitment : ∀ past view response, response ∈ (players who past view).support →
      ∀ material, response.transmission = some material →
        ∀ event candidate, material.call.packet ≠ .commitment event candidate) :
    (application setup leaks).PolicyInvariant players
      (ownerCommitmentRanksBelow setup leaks who rank) := by
  let app := application setup leaks
  refine { respond := ?_, environment := ?_ }
  · intro execution actor action prior chosen message member authored event candidate addressed
      valid
    rcases action with ⟨transmission⟩
    cases transmission with
    | none => exact prior message member authored event candidate addressed valid
    | some material =>
        change message ∈ execution.network.inputs ++ [_] at member
        rcases List.mem_append.mp member with old | fresh
        · exact prior message old authored event candidate addressed valid
        · cases List.mem_singleton.mp fresh
          have own : actor = who := authored
          subst actor
          have packet : material.call.packet = .commitment event candidate := addressed
          exact (noncommitment _ _ _ chosen material rfl event candidate packet).elim
  · intro execution next command prior moved message member authored event candidate addressed
      valid
    rw [app.environmentStep_inputs execution next command moved] at member
    exact prior message member authored event candidate addressed valid

/-- At the completed rank, every bounded old owner commitment addresses an
already completed event. Later inclusions cannot create a second binding result. -/
theorem ownerCommitmentRanksBelow_completed
    (execution : (application setup leaks).Execution) (who : Player)
    (current : (graph setup).EventId)
    (bounded : ownerCommitmentRanksBelow setup leaks who current.val execution)
    (completed : current ∈ execution.application.config.cut.completed) :
    ∀ message ∈ execution.network.inputs, message.sender = who →
      ∀ event candidate, message.payload.call = .commitment event candidate →
        message.payload.tokenValid = true → event ∈ execution.application.config.cut.completed := by
  intro message emitted authored event candidate addressed valid
  have within := bounded message emitted authored event candidate addressed valid
  rcases lt_or_eq_of_le within with earlier | same
  · exact execution.application.config.cut.predecessor_closed completed
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, earlier⟩)
  · exact Fin.ext same ▸ completed

/-- The commitment bound and completed-event endpoint are derived from a real
initialized raw prefix and the actual chosen response. No old-packet provenance
is supplied by the caller, and every later foreign policy and command is allowed. -/
theorem sourceService_no_new_commitments_old_packets_completed
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (control : (application setup leaks).Control)
    (trace : ((application setup leaks).protocol initial horizon scheduler).Trace (some control))
    (who : Player) (current : (graph setup).EventId)
    (ready : control.execution.application.config.cut.Ready current)
    (response : (application setup leaks).Action)
    (players : Player → (application setup leaks).Policy)
    (noncommitment : ∀ past view action, action ∈ (players who past view).support →
      ∀ material, action.transmission = some material →
        ∀ event candidate, material.call.packet ≠ .commitment event candidate)
    (rounds : Nat) (next : (application setup leaks).Execution)
    (reached : next ∈ ((application setup leaks).runRounds scheduler players rounds
      (control.execution.respond (application setup leaks) who response)).support)
    (completed : current ∈ next.application.config.cut.completed) :
    ∀ message ∈ next.network.inputs, message.sender = who →
      ∀ event candidate, message.payload.call = .commitment event candidate →
        message.payload.tokenValid = true → event ∈ next.application.config.cut.completed := by
  classical
  let app := application setup leaks
  let before := control.execution.respond app who response
  have facts := settledFacts_respond control.execution
    (settledFacts_history initial horizon scheduler trace) who response
  have configEq := ((runtime setup).reactive_respond_application leaks control.execution who
    response).1
  have readyBefore : before.application.config.cut.Ready current := by
    change (control.execution.respond app who response).application.config.cut.Ready current
    rwa [configEq]
  have bounded := ownerCommitmentRanksBelow_of_ready setup leaks before facts who current
    readyBefore
  have after := (ownerCommitmentRanksBelow_policyInvariant setup leaks players who current.val
    noncommitment).runRounds scheduler rounds before next bounded reached
  exact ownerCommitmentRanksBelow_completed setup leaks next who current after completed

end Vegas
