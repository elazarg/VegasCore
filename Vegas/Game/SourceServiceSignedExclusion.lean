/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRiskSlots
import Vegas.Game.SourceServiceCanonicalConformance
import Vegas.Pending.ReactiveSignedEvidence

/-! # Concrete signed packet exclusions at clear service sites

The actual signed packet of a canonical response conforms when this owner's
risk is clear, even after foreign raw responses. A signed constructor breach
therefore proves exclusion from the clear risk menu. The premise concerns
actual emitted content, not a failed certificate request or private material.
Collection for that content is supplied by the signed-evidence lower leaf.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- An actual signed constructor breach cannot be retained at a clear legal
own activation. Other owners' earlier raw responses remain unrestricted. -/
theorem signedContentBreach_risk_excluded
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    (execution : (application setup leaks).Execution) (who : Player)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (response : (application setup leaks).Action)
    (material : (application setup leaks).Submission)
    (transmission : response.transmission = some material)
    (breach : SignedContentBreach
      ⟨(who, execution.network.nextSerial who), (application setup leaks).packet
        ((application setup leaks).submit execution.application who material) who
          (execution.network.known who) material⟩) :
    response ∉ bounds.riskActions (runtime setup) leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) := by
  intro member
  rw [bounds.riskActions_of_clear (runtime setup) leaks bound who _ _ clear] at member
  have persistentClear := ((runtime setup).serviceRisk_clear_iff leaks bound who _ _).mp clear |>.1
  obtain ⟨atTurn, slots⟩ := riskCanonicalSlots_history bounds bound _ trace who persistentClear
  have rawTrace := (bounds.riskMenu (runtime setup) leaks bound).toRawTrace (initialLaw setup)
    horizon scheduler trace
  rcases bounds.clearActions_cases (runtime setup) leaks who _ _ response member with
    member | ⟨_, conformant⟩
  swap
  · obtain ⟨other, sent, _, conform⟩ := conformantResponse_actual rawTrace who response conformant
    rw [transmission] at sent
    cases Option.some.inj sent
    exact breach.not_freshServiceEnvelope (runtime setup) execution.application.publicView conform
  obtain ⟨event, action, turn, _, _, timely, unrecorded, _, decided⟩ :=
    bounds.canonicalActions_submission (runtime setup) leaks who _ _ response member material
      transmission
  have fresh := canonicalSlot_fresh_of_used rawTrace who atTurn slots event turn unrecorded
  have conform := canonicalServiceDecision_freshServiceEnvelope rawTrace event turn timely fresh
    action material (by rw [← decided]; exact transmission)
  exact breach.not_freshServiceEnvelope (runtime setup) execution.application.publicView conform

end Vegas
