module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ServiceTimingCoupling
public import Vegas.Game.SourceServiceOwnerSettled
public import Vegas.Game.SourceServiceAudit
public import Interaction.ReactiveRestrictedContinuation
public import Interaction.ReactiveRecovery

@[expose] public section

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
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}

section Generic

variable (setup : Setup (Player := Player) (L := L)) {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps)))

variable {setup} {leaks}
/-- Prescribed clients incur no protocol-audit charge under any turn timing.
Source defaults are game actions and retain their declared payoff. -/
theorem sourceServiceTurnPolicy_charge_zero
    (serial : (serviceGraph setup deps).ActorSerial)
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (count : Nat) (within : count ≤ horizon)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (reached : execution ∈
        ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler
        (serviceTurnPolicy setup deps duration leaks bound turns timing profile) count).support)
    (who : Player) : TerminalAudit.charge
    ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
    (serviceSourceAudit setup deps duration leaks sample)
        ((serviceApplication setup deps duration leaks).finished execution) who = 0 := by
  change TerminalAudit.charge _ _
    (some (⟨0, none, execution⟩ : (serviceApplication setup deps duration leaks).Control)) who = 0
  unfold serviceSourceAudit
  rw [(serviceAudit_charge (serviceTimeouts setup deps duration))]
  apply (serviceApplication setup deps duration leaks).sampledTrafficAudit_sound
  · exact authentic _
  · intro record member owner
    exact sourceServiceTurnPolicy_owner_settled serial contract
      (serviceTurnPolicy setup deps duration leaks bound turns timing profile) who
      timing profile rfl count within execution reached record member owner

end Generic

section Settlement

variable {setup : Setup (Player := Player) (L := L)} {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- **The first-turn limit's exact settlement law.** Under the asynchronous
contract, for every source profile whose
first-turn clients have its source outcome law, the first-turn profile's
executions after `horizon` rounds have the source joint law of typed outcome
and realized payoffs, for every authentic partial audit and every deposit. The supplied reader
replaces the service readout. -/
theorem sourceServiceFirstTurn_settlement_law_readout
    (serial : (serviceGraph setup deps).ActorSerial)
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {horizon turns : Nat} {delay bound : (serviceGraph setup deps).EventId → Nat}
    (reader : (serviceApplication setup deps duration leaks).ProtocolState →
      Option (Config Player L setup.program.terminalCtx))
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnReadoutLaw setup deps duration leaks reader horizon scheduler bound turns
      profile)
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Config Player L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler (serviceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) profile) horizon).bind (fun execution =>
        (TerminalAudit.settlement (readoutBaseUtility reader utility)
          ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
          (serviceSourceAudit setup deps duration leaks sample) deposit
            ((serviceApplication setup deps duration leaks).finished execution)).map
          fun payoffs => (reader
            ((serviceApplication setup deps duration leaks).finished execution), payoffs)) =
      (setup.run profile).map (fun state => (some state, utility state)) := by
  let app := serviceApplication setup deps duration leaks
  have clean : ∀ execution ∈ (app.roundsFrom (serviceInitialLaw setup deps) scheduler
      (serviceTurnPolicy setup deps duration leaks bound turns (firstTurnTiming setup turns deps)
        profile) horizon).support,
      (TerminalAudit.settlement (readoutBaseUtility reader utility)
          ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
          (serviceSourceAudit setup deps duration leaks sample) deposit
            (app.finished execution)).map (fun payoffs =>
          (reader (app.finished execution), payoffs)) =
        PMF.pure (reader (app.finished execution),
          readoutBaseUtility reader utility (app.finished execution)) := by
    intro execution reached
    rw [TerminalAudit.settlement_clean (readoutBaseUtility reader utility) _ _
      deposit (app.finished execution)
      (sourceServiceTurnPolicy_charge_zero serial contract (firstTurnTiming setup turns deps)
        profile
        sample authentic horizon le_rfl execution reached), PMF.pure_map]
  unfold FirstTurnReadoutLaw at terminal
  have joint := congrArg (PMF.map (fun state : Option (Config Player L setup.program.terminalCtx) =>
    (state, fun who => state.elim 0 (fun final => utility final who)))) terminal
  simp only [PMF.map_comp, Function.comp_def, Option.elim_some] at joint
  exact (bind_congr_on_support _ clean).trans ((PMF.bind_pure_comp _ _).trans joint)

/-- The service-reader instance of `sourceServiceFirstTurn_settlement_law_readout`. -/
theorem sourceServiceFirstTurn_settlement_law
    (serial : (serviceGraph setup deps).ActorSerial)
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {horizon turns : Nat} {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup deps duration leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Config Player L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    ((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler (serviceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) profile) horizon).bind (fun execution =>
        (TerminalAudit.settlement (serviceBaseUtility setup deps duration leaks utility)
          ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
          (serviceSourceAudit setup deps duration leaks sample) deposit
            ((serviceApplication setup deps duration leaks).finished execution)).map
          fun payoffs => (serviceSourceReadout setup deps duration leaks
            ((serviceApplication setup deps duration leaks).finished execution), payoffs)) =
      (setup.run profile).map (fun state => (some state, utility state)) :=
  sourceServiceFirstTurn_settlement_law_readout serial (serviceSourceReadout setup deps duration
    leaks)
    contract profile terminal sample
    authentic utility deposit

/-! ## The settlement law of the turn-counted policy -/

/-- **The turn-counted policy's settlement law on executions.** Under the
asynchronous contract with `delay + bound < duration`, for every turn timing and
every source profile whose first-turn clients have its source outcome law, the
turn-counted profile's executions after `horizon`
rounds have the source joint law of typed outcome and realized payoffs within
the product deferral error in total variation, for every authentic partial audit
and every deposit. The supplied reader replaces the service readout. -/
theorem sourceServiceTurnPolicy_execution_settlement_lawError_readout
    (serial : (serviceGraph setup deps).ActorSerial)
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (reader : (serviceApplication setup deps duration leaks).ProtocolState →
      Option (Config Player L setup.program.terminalCtx))
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnReadoutLaw setup deps duration leaks reader horizon scheduler bound turns
      profile)
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Config Player L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV timing.deferralError
      (((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler (serviceTurnPolicy setup deps duration leaks bound turns timing profile)
          horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (readoutBaseUtility reader utility)
              ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
              (serviceSourceAudit setup deps duration leaks sample) deposit
                ((serviceApplication setup deps duration leaks).finished execution)).map
              fun payoffs => (reader
                ((serviceApplication setup deps duration leaks).finished execution), payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) := by
  rw [← sourceServiceFirstTurn_settlement_law_readout serial reader contract profile terminal sample
    authentic utility deposit]
  exact serviceTurnPolicy_roundsFrom_bind_within (serviceInitialLaw setup deps) scheduler horizon
    bound timing profile _

/-- The service-reader instance of
`sourceServiceTurnPolicy_execution_settlement_lawError_readout`. -/
theorem sourceServiceTurnPolicy_execution_settlement_lawError
    (serial : (serviceGraph setup deps).ActorSerial)
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timing : TurnTiming setup turns deps) (profile : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup deps duration leaks horizon scheduler bound turns profile)
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : Config Player L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV timing.deferralError
      (((serviceApplication setup deps duration leaks).roundsFrom (serviceInitialLaw setup deps)
        scheduler (serviceTurnPolicy setup deps duration leaks bound turns timing profile)
          horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (serviceBaseUtility setup deps duration leaks utility)
              ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
              (serviceSourceAudit setup deps duration leaks sample) deposit
                ((serviceApplication setup deps duration leaks).finished execution)).map
              fun payoffs => (serviceSourceReadout setup deps duration leaks
                ((serviceApplication setup deps duration leaks).finished execution), payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) :=
  sourceServiceTurnPolicy_execution_settlement_lawError_readout serial (serviceSourceReadout setup
    deps
    duration leaks) contract timing
    profile terminal sample authentic utility deposit

variable [Finite Player]

/-- **Honest execution of the client policies, for every source profile.**
Under the asynchronous contract, for every turn
timing and every source profile whose clients' first-turn limit has its source
outcome law, the client policies of the profile's turn-counted clients, restricted to a response
menu that admits them, have the profile's source joint law of typed outcome and
realized payoffs within the product deferral error in total variation, for every
authentic partial audit and every deposit. The supplied reader replaces the service readout. -/
theorem sourceServiceClients_clientPolicy_settlement_lawError_readout
    {deps : setup.dataflowGraph.Dependencies} {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (serial : (serviceGraph setup deps).ActorSerial)
    (reader : (serviceApplication setup deps duration leaks).ProtocolState →
      Option (Config Player L setup.program.terminalCtx))
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timing : TurnTiming setup turns deps) (original : BehavioralProfile setup.program)
    (terminal : FirstTurnReadoutLaw setup deps duration leaks reader horizon scheduler bound turns
      (normalizeDisclosureProfile setup.program original))
    (menu : (serviceApplication setup deps duration leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (serviceInitialLaw setup deps) horizon scheduler who
      (serviceClientPolicy setup deps duration leaks bound turns timing
        (normalizeDisclosureProfile setup.program original) who))
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx × DefaultHistory Player → Player → ℝ)
    (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement
      (readoutBaseUtility reader
        (fun final => utility (final.state, final.defaults)))
      ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
      (serviceSourceAudit setup deps duration leaks sample) deposit
    PMF.WithinTV timing.deferralError
      (((menu.information (serviceInitialLaw setup deps) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (serviceInitialLaw setup deps) horizon scheduler who
          (serviceClientPolicy setup deps duration leaks bound turns timing
            (normalizeDisclosureProfile setup.program original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs =>
            ((reader final.state).map
              (fun terminal => (terminal.state, terminal.defaults)), payoffs)))
      ((setup.run original).map
        (fun final =>
          (some (final.state, final.defaults), utility (final.state, final.defaults)))) := by
  intro settle
  let app := serviceApplication setup deps duration leaks
  let clients := normalizeDisclosureProfile setup.program original
  have states := menu.run_restrict_eq_roundsFrom (serviceInitialLaw setup deps) horizon
    scheduler (serviceClientPolicy setup deps duration leaks bound turns timing clients) covered
  have native : ((menu.information (serviceInitialLaw setup deps) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup deps) horizon scheduler who
        (serviceClientPolicy setup deps duration leaks bound turns timing clients who))
      (2 * horizon + 1)).bind (fun final =>
        (settle final.state).map fun payoffs =>
          (reader final.state, payoffs)) =
      (app.roundsFrom (serviceInitialLaw setup deps) scheduler
        (serviceClientPolicy setup deps duration leaks bound turns timing clients) horizon).bind
          (fun execution => (settle (app.finished execution)).map
            fun payoffs => (reader
              (app.finished execution), payoffs)) := by
    have joint := congrArg (fun law : PMF app.ProtocolState =>
      law.bind fun final =>
        (settle final).map fun payoffs =>
          (reader final, payoffs)) states
    simpa only [PMF.bind_map, Function.comp_def] using joint
  have compared :=
    (sourceServiceTurnPolicy_execution_settlement_lawError_readout serial reader contract timing
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


/-- The service-reader instance of
`sourceServiceClients_clientPolicy_settlement_lawError_readout`. -/
theorem sourceServiceClients_clientPolicy_settlement_lawError
    {deps : setup.dataflowGraph.Dependencies} {duration : (serviceGraph setup deps).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup deps).EventId → Nat}
    (serial : (serviceGraph setup deps).ActorSerial)
    (contract : AsyncContract (serviceTimeouts setup deps duration) leaks
      (serviceInitialLaw setup deps) horizon scheduler delay bound)
    (timing : TurnTiming setup turns deps) (original : BehavioralProfile setup.program)
    (terminal : FirstTurnSourceLaw setup deps duration leaks horizon scheduler bound turns
      (normalizeDisclosureProfile setup.program original))
    (menu : (serviceApplication setup deps duration leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (serviceInitialLaw setup deps) horizon scheduler who
      (serviceClientPolicy setup deps duration leaks bound turns timing
        (normalizeDisclosureProfile setup.program original) who))
    (sample : List (SettledEvidence setup deps) → PMF (List (SettledEvidence setup deps)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx × DefaultHistory Player → Player → ℝ)
    (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement
      (serviceBaseUtility setup deps duration leaks
        (fun final => utility (final.state, final.defaults)))
      ((serviceAuditObservation (serviceTimeouts setup deps duration)) leaks)
      (serviceSourceAudit setup deps duration leaks sample) deposit
    PMF.WithinTV timing.deferralError
      (((menu.information (serviceInitialLaw setup deps) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (serviceInitialLaw setup deps) horizon scheduler who
          (serviceClientPolicy setup deps duration leaks bound turns timing
            (normalizeDisclosureProfile setup.program original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs =>
            ((serviceSourceReadout setup deps duration leaks final.state).map
              (fun terminal => (terminal.state, terminal.defaults)), payoffs)))
      ((setup.run original).map
        (fun final =>
          (some (final.state, final.defaults), utility (final.state, final.defaults)))) :=
  sourceServiceClients_clientPolicy_settlement_lawError_readout serial (serviceSourceReadout setup
    deps
    duration leaks) contract timing
    original terminal menu covered sample authentic utility deposit

end Settlement

end Vegas
