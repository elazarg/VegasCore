/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstTurnNoMiss
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceAudit

/-! # Actual audit soundness under exact first-turn play

An owner following the exact first-turn source policy has no public decision
miss and every authored packet is permitted by the actual settled record.
Authentic sampling therefore collects no charge from that owner, even with
arbitrary foreign raw policies. Positive observation or report coverage is
not needed for this soundness direction.

If all owners follow the policy, the joint realized settlement vector is
exactly the base payoff at every supported control. These are laws of
prescribed play from initialization, not incentive comparisons or claims
about histories after the focal owner's raw deviations.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- No actual charge is collected from the prescribed owner at any supported
control. Other owners may follow arbitrary raw policies and incur charges. -/
theorem sourceServiceFirstTurn_audit_clear {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (state : (application setup leaks).ProtocolState)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players state) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) state who = 0 := by
  cases state with
  | none => exact (runtime setup).serviceAudit_charge_none leaks _ who
  | some control =>
      have noMiss := sourceServiceFirstTurn_no_public_miss_roundSupported contract timely players
        who turns profile follows control reached
      unfold sourceServiceAudit
      rw [(runtime setup).serviceAudit_charge, noMiss]
      simp only [Bool.false_eq_true, ↓reduceIte]
      apply (application setup leaks).sampledTrafficAudit_sound
      · exact authentic _
      · intro record member authored
        exact sourceServiceTurnPolicy_owner_settled_roundSupported contract players who
          (firstTurnTiming setup turns) profile follows control reached record member authored

/-- Prescribed play preserves the entire realized payoff vector, including
correlated audit randomness. No equilibrium or coverage premise is needed. -/
theorem sourceServiceFirstTurn_settlement {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : ∀ who, players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (base : (application setup leaks).ProtocolState → Player → ℝ) (deposit : Player → ℝ)
    (state : (application setup leaks).ProtocolState)
    (reached : (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler
      players state) :
    TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit state = PMF.pure (base state) :=
  TerminalAudit.settlement_clean base _ _ deposit state fun who =>
    sourceServiceFirstTurn_audit_clear contract timely players who turns profile (follows who)
      sample authentic state reached

end Vegas
