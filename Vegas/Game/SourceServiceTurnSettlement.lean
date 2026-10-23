/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediateRisk
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceAudit
import Vegas.Game.ServiceHonestLaw

/-! # The realized settlement law of the turn-counted policy

The turn-counted prescribed policy and its first-turn limit differ only in the
owners' timing lotteries, so the two runs are within the total deferral weight
of each other in total variation, for every scheduler
(`Vegas.serviceTurnPolicy_roundsFrom_bind_within`).

On a barrier-ordered graph, under the asynchronous contract the first-turn
limit has the exact source joint
law of the typed outcome and the realized settlement
(`Vegas.sourceServiceFirstTurn_settlement_law`): its readout law is the source
law, no owner has a public binding omission, and every transmitted packet is
permitted by the settled record, so an authentic partial audit collects
nothing. Hence the turn-counted policy's executions have the source joint law
of typed outcome and realized payoffs within the total deferral weight
(`Vegas.sourceServiceTurnPolicy_execution_settlement_lawError`). Deferral can
still produce charged binding omissions and, at a resolution, uncharged
withholding by expiry; their mass is part of this error.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability GameTheory.Enforcement
open Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-! ## Coupling with the first-turn limit -/
/-! ## The exact settlement law of the first-turn limit -/

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

variable {setup} {leaks}
/-- **No charge under the first-turn limit.** Under the asynchronous contract,
at every execution the first-turn profile reaches within the horizon, an
authentic partial audit collects from no player: no owner has a public
binding omission and the settled record permits every transmitted packet. -/
theorem sourceServiceFirstTurn_charge_zero
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (profile : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile) count).support) (who : Player) : TerminalAudit.charge
    ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
    (serviceSourceAudit setup mode deadline leaks sample)
        ((serviceApplication setup mode deadline leaks).finished execution) who = 0 := by
  have noMiss := sourceServiceFirstTurn_no_miss contract timely
    (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile) who
    turns profile rfl count within execution reached
  change TerminalAudit.charge _ _
    (some (⟨0, none, execution⟩ : (serviceApplication setup mode deadline leaks).Control)) who = 0
  unfold serviceSourceAudit
  rw [(serviceRuntime setup mode deadline).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply (serviceApplication setup mode deadline leaks).sampledTrafficAudit_sound
  · exact authentic _
  · intro record member owner
    exact sourceServiceTurnPolicy_owner_settled contract
      (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
          profile) who
      (firstTurnTiming setup turns mode) profile rfl count within execution reached record
      member owner

end Generic

section Ordered

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **The first-turn limit's exact settlement law.** Under the asynchronous
contract with `delay + bound < deadline`, for every source profile whose
first-turn clients have its source outcome law, the first-turn profile's
executions after `horizon` rounds have the source joint law of typed outcome
and realized payoffs, for every authentic partial audit and every deposit. -/
theorem sourceServiceFirstTurn_settlement_law
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {horizon turns : Nat} {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) profile) horizon).bind (fun execution =>
        (TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
          ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks sample) deposit
            ((serviceApplication setup mode deadline leaks).finished execution)).map
          fun payoffs => (serviceSourceReadout setup mode deadline leaks
            ((serviceApplication setup mode deadline leaks).finished execution), payoffs)) =
      (setup.run profile).map (fun state => (some state, utility state)) := by
  let app := serviceApplication setup mode deadline leaks
  have clean : ∀ execution ∈ (app.roundsFrom (serviceInitialLaw setup mode) scheduler
      (serviceTurnPolicy setup mode deadline leaks bound turns (firstTurnTiming setup turns mode)
        profile) horizon).support,
      (TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
          ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks sample) deposit
            (app.finished execution)).map (fun payoffs =>
          (serviceSourceReadout setup mode deadline leaks (app.finished execution), payoffs)) =
        PMF.pure (serviceSourceReadout setup mode deadline leaks (app.finished execution),
          serviceBaseUtility setup mode deadline leaks utility (app.finished execution)) := by
    intro execution reached
    rw [TerminalAudit.settlement_clean (serviceBaseUtility setup mode deadline leaks utility) _ _
      deposit (app.finished execution)
      (sourceServiceFirstTurn_charge_zero contract timely profile sample authentic horizon le_rfl
        execution reached), PMF.pure_map]
  unfold FirstTurnSourceLaw at terminal
  have joint := congrArg (PMF.map (fun state : Option (State L setup.program.terminalCtx) =>
    (state, fun who => state.elim 0 (fun final => utility final who)))) terminal
  simp only [PMF.map_comp, Function.comp_def, Option.elim_some] at joint
  exact (bind_congr_on_support _ clean).trans ((PMF.bind_pure_comp _ _).trans joint)

/-! ## The settlement law of the turn-counted policy -/

/-- **The turn-counted policy's settlement law on executions.** Under the
asynchronous contract with `delay + bound < deadline`, for every turn timing and
every source profile whose first-turn clients have its source outcome law, the
turn-counted profile's executions after `horizon`
rounds have the source joint law of typed outcome and realized payoffs within
the total deferral weight in total variation, for every authentic partial audit
and every deposit. -/
theorem sourceServiceTurnPolicy_execution_settlement_lawError
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceTurnPolicy setup mode deadline leaks bound turns timing profile)
          horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
              ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
              (serviceSourceAudit setup mode deadline leaks sample) deposit
                ((serviceApplication setup mode deadline leaks).finished execution)).map
              fun payoffs => (serviceSourceReadout setup mode deadline leaks
                ((serviceApplication setup mode deadline leaks).finished execution), payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) := by
  rw [← sourceServiceFirstTurn_settlement_law contract timely profile terminal sample
    authentic utility deposit]
  exact serviceTurnPolicy_roundsFrom_bind_within (serviceInitialLaw setup mode) scheduler horizon
    bound timing profile _

variable [Fintype Player]

end Ordered

end Vegas
