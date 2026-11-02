/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.ServiceTimingCoupling
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceAudit
import Interaction.ReactiveRestrictedContinuation
import Interaction.ReactiveRecovery

/-! # Settlement laws of turn-counted source clients

Authentic traffic from prescribed clients passes the protocol audit, including
source omissions and authentic openings whose public guards reject. Such source
defaults retain their declared game payoff. The first-turn source law therefore
preserves the joint source configuration and settlement law. Other turn timings
are within their product deferral error in total variation.
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

section Generic

variable (setup : Setup (Player := Player) (L := L)) {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))

variable {setup} {leaks}
/-- Prescribed clients incur no protocol-audit charge under any turn timing.
Source defaults are game actions and retain their declared payoff. -/
theorem sourceServiceTurnPolicy_charge_zero
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
        (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) count).support)
    (who : Player) : TerminalAudit.charge
    ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
    (serviceSourceAudit setup mode deadline leaks sample)
        ((serviceApplication setup mode deadline leaks).finished execution) who = 0 := by
  change TerminalAudit.charge _ _
    (some (⟨0, none, execution⟩ : (serviceApplication setup mode deadline leaks).Control)) who = 0
  unfold serviceSourceAudit
  rw [(serviceRuntime setup mode deadline).serviceAudit_charge]
  apply (serviceApplication setup mode deadline leaks).sampledTrafficAudit_sound
  · exact authentic _
  · intro record member owner
    exact sourceServiceTurnPolicy_owner_settled contract
      (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) who
      timing profile rfl count within execution reached record member owner

end Generic

section Settlement

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- **The first-turn limit's exact settlement law.** Under the asynchronous
contract, for every source profile whose
first-turn clients have its source outcome law, the first-turn profile's
executions after `horizon` rounds have the source joint law of typed outcome
and realized payoffs, for every authentic partial audit and every deposit. -/
theorem sourceServiceFirstTurn_settlement_law
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {horizon turns : Nat} {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Config Player L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
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
      (sourceServiceTurnPolicy_charge_zero contract (firstTurnTiming setup turns mode) profile
        sample authentic horizon le_rfl execution reached), PMF.pure_map]
  unfold FirstTurnSourceLaw at terminal
  have joint := congrArg (PMF.map (fun state : Option (Config Player L setup.program.terminalCtx) =>
    (state, fun who => state.elim 0 (fun final => utility final who)))) terminal
  simp only [PMF.map_comp, Function.comp_def, Option.elim_some] at joint
  exact (bind_congr_on_support _ clean).trans ((PMF.bind_pure_comp _ _).trans joint)

/-! ## The settlement law of the turn-counted policy -/

/-- **The turn-counted policy's settlement law on executions.** Under the
asynchronous contract with `delay + bound < deadline`, for every turn timing and
every source profile whose first-turn clients have its source outcome law, the
turn-counted profile's executions after `horizon`
rounds have the source joint law of typed outcome and realized payoffs within
the product deferral error in total variation, for every authentic partial audit
and every deposit. -/
theorem sourceServiceTurnPolicy_execution_settlement_lawError
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Config Player L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV timing.deferralError
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
  rw [← sourceServiceFirstTurn_settlement_law contract profile terminal sample
    authentic utility deposit]
  exact serviceTurnPolicy_roundsFrom_bind_within (serviceInitialLaw setup mode) scheduler horizon
    bound timing profile _

variable [Finite Player]

/-- **Honest execution of the client policies, for every source profile.**
Under the asynchronous contract, for every turn
timing and every source profile whose clients' first-turn limit has its source
outcome law, the client policies of the profile's turn-counted clients, restricted to a response
menu that admits them, have the profile's source joint law of typed outcome and
realized payoffs within the product deferral error in total variation, for every
authentic partial audit and every deposit. -/
theorem sourceServiceClients_clientPolicy_settlement_lawError
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timing : TurnTiming setup turns mode) (original : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup mode deadline leaks horizon scheduler bound turns
      (normalizeDisclosureProfile setup.program original))
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (serviceInitialLaw setup mode) horizon scheduler who
      (serviceClientPolicy setup mode deadline leaks bound turns timing
        (normalizeDisclosureProfile setup.program original) who))
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx × DefaultHistory Player → Player → ℝ)
    (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement
      (serviceBaseUtility setup mode deadline leaks
        (fun final => utility (final.state, final.defaults)))
      ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
      (serviceSourceAudit setup mode deadline leaks sample) deposit
    PMF.WithinTV timing.deferralError
      (((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
          (serviceClientPolicy setup mode deadline leaks bound turns timing
            (normalizeDisclosureProfile setup.program original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs =>
            ((serviceSourceReadout setup mode deadline leaks final.state).map
              (fun terminal => (terminal.state, terminal.defaults)), payoffs)))
      ((setup.run original).map
        (fun final =>
          (some (final.state, final.defaults), utility (final.state, final.defaults)))) := by
  intro settle
  let app := serviceApplication setup mode deadline leaks
  let clients := normalizeDisclosureProfile setup.program original
  have physical := menu.run_restrict_eq_finish (serviceInitialLaw setup mode) horizon scheduler
    (serviceClientPolicy setup mode deadline leaks bound turns timing clients) covered
    (2 * horizon + 1) (menu.protocol (serviceInitialLaw setup mode) horizon scheduler).initHistory
    le_rfl
  have states : ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
        (serviceClientPolicy setup mode deadline leaks bound turns timing clients who))
      (2 * horizon + 1)).map (fun final => final.state) =
        (serviceInitialLaw setup mode).bind (fun state =>
          (app.runRounds scheduler
            (serviceClientPolicy setup mode deadline leaks bound turns timing clients) horizon
            (ReactiveApplication.Execution.initial app state)).map app.finished) := by
    rw [InformationModel.runBehavioral]
    exact physical
  have native : ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
        (serviceClientPolicy setup mode deadline leaks bound turns timing clients who))
      (2 * horizon + 1)).bind (fun final =>
        (settle final.state).map fun payoffs =>
          (serviceSourceReadout setup mode deadline leaks final.state, payoffs)) =
      (app.roundsFrom (serviceInitialLaw setup mode) scheduler
        (serviceClientPolicy setup mode deadline leaks bound turns timing clients) horizon).bind
          (fun execution => (settle (app.finished execution)).map
            fun payoffs => (serviceSourceReadout setup mode deadline leaks
              (app.finished execution), payoffs)) := by
    have joint := congrArg (fun law : PMF app.ProtocolState =>
      law.bind fun final =>
        (settle final).map fun payoffs =>
          (serviceSourceReadout setup mode deadline leaks final, payoffs)) states
    simp only [PMF.bind_map, PMF.bind_bind] at joint
    refine joint.trans ?_
    unfold ReactiveApplication.roundsFrom
    simp only [PMF.bind_bind, Function.comp_def]
    rfl
  have compared :=
    (sourceServiceTurnPolicy_execution_settlement_lawError contract timing
      clients terminal sample authentic
      (fun final => utility (final.state, final.defaults)) deposit).map
        (fun outcome => (outcome.1.map (fun final => (final.state, final.defaults)), outcome.2))
  rw [← sourceServiceClientPolicy_roundsFrom] at compared
  have observedNative := congrArg
    (PMF.map (fun outcome =>
      (outcome.1.map (fun final => (final.state, final.defaults)), outcome.2))) native
  have normalizedLaw := congrArg
    (PMF.map (fun outcome => (some outcome, utility outcome)))
    (setup.run_normalizeDisclosures_eq original)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Option.map_some]
    at compared observedNative normalizedLaw
  rw [← observedNative, normalizedLaw] at compared
  exact compared


end Settlement

end Vegas
