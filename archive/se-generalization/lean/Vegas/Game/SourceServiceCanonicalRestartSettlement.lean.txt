/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCanonicalRestart
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit

/-! # Realized settlement of the same canonical source restart

From an actual canonical completion boundary with no owner public miss, the
first-turn restart preserves the same typed source continuation and its whole
realized payoff vector. Utilities read the initial parameter and public outcome
from that same terminal source state. Authentic audit samples may be partial and
correlate every player's verdict. Accepted delayed prefixes and persistent
private opportunity risk are allowed.

This is an audited source continuation benchmark. It does not identify the free
continuation returned by equilibrium completion or prove its optimality.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The actual typed readout and realized public-payoff vector use one source
draw, including its correlated initial parameter. Clean settlement is applied
to the actual final record, without a future-profile initialization premise. -/
theorem sourceServiceCanonicalHistory_firstTurn_settlement {Parameter : Type}
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (permitted : ∀ who, (profile who).Admitted setup.program (CommitmentInterface.values _))
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (rank remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ordered : execution.application.config.cut.IsPrefix rank)
    (untouched : ∀ event : (graph setup).EventId, event.val = rank →
      Untouched setup leaks event execution)
    (noMiss : ∀ who, execution.application.publicView.missedDecisionBy who = false)
    (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) :
    (((application setup leaks).runToHorizon scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      horizon execution).bind fun final =>
        (TerminalAudit.settlement
          (baseUtility setup leaks
            (fun source => utility (setup.parameterOutcome parameter source)))
          ((runtime setup).serviceAuditObservation leaks) (sourceServiceAudit setup leaks sample)
          deposit ((application setup leaks).finished final)).map fun payoffs =>
            (sourceReadout setup leaks ((application setup leaks).finished final), payoffs)) =
      (setup.continuationLaw profile
        (sourceServicePrefix? setup rank execution.application.config)).map
          (fun source => (some source, utility (setup.parameterOutcome parameter source))) := by
  let app := application setup leaks
  let future := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let law := app.runToHorizon scheduler future horizon execution
  let base := baseUtility setup leaks
    (fun source => utility (setup.parameterOutcome parameter source))
  have readoutLaw := (sourceServiceCanonicalHistory_firstTurn_continuation (turns := turns)
    bounds covered initialCovered capacity contract timely profile permitted effective rank
      remaining execution trace ordered untouched).1
  have clean (final : app.Execution) (reached : final ∈ law.support) :
      TerminalAudit.settlement base ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks sample) deposit (app.finished final) =
          PMF.pure (base (app.finished final)) :=
    TerminalAudit.settlement_clean base _ _ deposit (app.finished final) fun who =>
      sourceServiceCanonicalHistory_firstTurn_audit_clear bounds covered initialCovered capacity
        contract timely profile permitted effective rank remaining execution trace ordered untouched
        who (noMiss who) sample authentic final reached
  calc
    _ = law.map (fun final => (sourceReadout setup leaks (app.finished final),
        base (app.finished final))) := by
      rw [← PMF.bind_pure_comp]
      apply bind_congr_on_support _
      intro final reached
      rw [clean final reached, PMF.pure_map]
      rfl
    _ = (sourceContinuation setup profile rank execution.application.config).map
        (fun outcome => (outcome, fun who => outcome.elim 0
          (fun source => utility (setup.parameterOutcome parameter source) who))) := by
      rw [← readoutLaw, PMF.map_comp]
      rfl
    _ = _ := by rw [sourceContinuation, PMF.map_comp]; rfl

end Vegas
