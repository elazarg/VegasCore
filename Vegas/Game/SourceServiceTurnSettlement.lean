/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSiteBridge
import Vegas.Game.SourceServiceGeometricTiming
import Vegas.Game.SourceServiceImmediateRisk
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceAudit
import Vegas.Game.RevealServiceCalendarState
import Vegas.Game.ServiceTimingCoupling
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
nothing. Hence the turn-counted policy has the source joint law of typed
outcome and realized payoffs within the total deferral weight, on executions
(`Vegas.sourceServiceTurnPolicy_execution_settlement_lawError`) and restricted
to an admissible response menu
(`Vegas.sourceServiceTurnPolicy_settlement_lawError`). The turn-counted clients
of an arbitrary source profile follow its disclosure normalization, which has
the same source law; together with packet permission against arbitrary
foreign play this is `Vegas.sourceServiceClients_honestExecution`, and in the
menu's information model `Vegas.sourceServiceClients_settlement_lawError`. The
error vanishes with the geometric timing's weight
(`Vegas.geometricTiming_settlement_lawError`). Deferral can still produce
charged binding omissions and, at a resolution, uncharged withholding by
expiry; their mass is part of this error.
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

/-! ## Phase decomposition -/
/-- At a terminal configuration no player has a turn, so the turn-counted
policy is silent. -/
theorem sourceServiceTurnPolicy_terminal {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (terminal : state.config.cut.IsPrefix (serviceGraph setup mode).order.eventCount)
    (who : Player) (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (current : view.application.publicView = state.publicView) :
    serviceTurnPolicy setup mode deadline leaks bound turns timing profile who past view =
      (serviceApplication setup mode deadline leaks).silentPolicy past view := by
  have idle : view.application.publicView.ownTurn? who = none := by
    cases turn : view.application.publicView.ownTurn? who with
    | none => rfl
    | some event =>
        have ready := (PublicView.ownTurn?_spec _ who event turn).1
        rw [current] at ready
        exact absurd ((terminal.2 event).mpr event.isLt)
          ((State.publicView_eventReady _ event).mp ready).1
  simp only [serviceTurnPolicy, idle]
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

/-- **Honest execution of the turn-counted clients.** On a barrier-ordered
graph, under the asynchronous contract with `delay + bound < deadline`, for
every turn timing and every source profile:

* the clients' executions after `horizon` rounds have the profile's source joint
  law of typed outcome and realized payoffs within the total deferral weight in
  total variation, for every authentic partial audit and every deposit;
* every packet transmitted by a player following its client is permitted by
  the settled record at every execution reached within the horizon, whatever
  the other players do. -/
theorem sourceServiceClients_honestExecution [Finite Player]
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (timing : TurnTiming setup turns mode) (original : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((serviceApplication setup mode deadline leaks).roundsFrom (serviceInitialLaw setup mode)
        scheduler (serviceTurnPolicy setup mode deadline leaks bound turns timing
          (sourceServiceClientProfile setup original)) horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
              ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
              (serviceSourceAudit setup mode deadline leaks sample) deposit
                ((serviceApplication setup mode deadline leaks).finished execution)).map
              fun payoffs => (serviceSourceReadout setup mode deadline leaks
                ((serviceApplication setup mode deadline leaks).finished execution), payoffs)))
      ((setup.run original).map (fun state => (some state, utility state))) ∧
    ∀ (players : Player → (serviceApplication setup mode deadline leaks).Policy) (who : Player),
      players who = serviceTurnPolicy setup mode deadline leaks bound turns timing
        (sourceServiceClientProfile setup original) who →
      ∀ count ≤ horizon, ∀ execution ∈ ((serviceApplication setup mode deadline leaks).roundsFrom
        (serviceInitialLaw setup mode) scheduler players count).support,
      ∀ record ∈ (serviceApplication setup mode deadline leaks).executionTraffic execution,
        record.envelope.sender = who →
          ((serviceRuntime setup mode deadline).settledRecord leaks execution).permits
            record.envelope = true := by
  refine ⟨?_, fun players who follows count within execution reached =>
    sourceServiceTurnPolicy_owner_settled contract players who timing
      (sourceServiceClientProfile setup original) follows count within execution reached⟩
  rw [← sourceServiceClientProfile_run original]
  exact sourceServiceTurnPolicy_execution_settlement_lawError contract timely timing
    (sourceServiceClientProfile setup original) (firstTurn_readout_law setup leaks ordered contract
      timely turns _ (sourceServiceClientProfile_effective original))
    sample authentic utility deposit

variable [Fintype Player]

/-- **Honest execution with realized settlement.** On a barrier-ordered graph,
under the asynchronous contract with `delay + bound < deadline`, for every turn
timing and every source profile with effective disclosures, players admissible
for a response menu that follow the turn-counted policy have, in the menu's
information model, the source joint law of typed outcome and realized payoffs
within the total deferral weight in total variation, for every authentic
partial audit and every deposit. Binding omissions and expired resolutions
caused by deferral are part of this error. -/
theorem sourceServiceTurnPolicy_settlement_lawError
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (timing : TurnTiming setup turns mode) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (serviceInitialLaw setup mode) horizon scheduler who
      (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who))
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
      ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
      (serviceSourceAudit setup mode deadline leaks sample) deposit
    PMF.WithinTV (∑ event, timing.deferral event)
      (((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
          (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs =>
            (serviceSourceReadout setup mode deadline leaks final.state, payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) := by
  intro settle
  let app := serviceApplication setup mode deadline leaks
  have physical := menu.run_restrict_eq_finish (serviceInitialLaw setup mode) horizon scheduler
    (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) covered
    (2 * horizon + 1) (menu.protocol (serviceInitialLaw setup mode) horizon scheduler).initHistory
    le_rfl
  have states : ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who))
      (2 * horizon + 1)).map (fun final => final.state) =
        (serviceInitialLaw setup mode).bind (fun state =>
          (app.runRounds scheduler
            (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) horizon
            (ReactiveApplication.Execution.initial app state)).map app.finished) := by
    rw [InformationModel.runBehavioral]
    exact physical
  have native : ((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile who))
      (2 * horizon + 1)).bind (fun final =>
        (settle final.state).map fun payoffs =>
          (serviceSourceReadout setup mode deadline leaks final.state, payoffs)) =
      (app.roundsFrom (serviceInitialLaw setup mode) scheduler
        (serviceTurnPolicy setup mode deadline leaks bound turns timing profile) horizon).bind
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
  rw [native]
  exact sourceServiceTurnPolicy_execution_settlement_lawError contract timely timing
    profile (firstTurn_readout_law setup leaks ordered contract timely turns profile effective)
    sample authentic utility deposit

/-- **Honest execution with realized settlement, for every source profile.**
On a barrier-ordered graph, under the asynchronous contract with
`delay + bound < deadline`, for every turn timing and every source profile,
players admissible for a response menu that follow the turn-counted clients of
the profile have, in the menu's information model, the profile's source joint
law of typed outcome and realized payoffs within the total deferral weight in
total variation, for every authentic partial audit and every deposit. -/
theorem sourceServiceClients_settlement_lawError
    (ordered : (serviceGraph setup mode).BarrierOrdered)
    {scheduler : (serviceApplication setup mode deadline leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) horizon scheduler delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (timing : TurnTiming setup turns mode) (original : BehavioralProfile setup.program)
    (menu : (serviceApplication setup mode deadline leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (serviceInitialLaw setup mode) horizon scheduler who
      (serviceTurnPolicy setup mode deadline leaks bound turns timing
        (sourceServiceClientProfile setup original) who))
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement (serviceBaseUtility setup mode deadline leaks utility)
      ((serviceRuntime setup mode deadline).serviceAuditObservation leaks)
      (serviceSourceAudit setup mode deadline leaks sample) deposit
    PMF.WithinTV (∑ event, timing.deferral event)
      (((menu.information (serviceInitialLaw setup mode) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (serviceInitialLaw setup mode) horizon scheduler who
          (serviceTurnPolicy setup mode deadline leaks bound turns timing
            (sourceServiceClientProfile setup original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs => (serviceSourceReadout setup mode deadline leaks
            final.state, payoffs)))
      ((setup.run original).map (fun state => (some state, utility state))) := by
  intro settle
  rw [← sourceServiceClientProfile_run original]
  exact sourceServiceTurnPolicy_settlement_lawError ordered contract timely timing
    (sourceServiceClientProfile setup original) (sourceServiceClientProfile_effective original)
    menu covered sample authentic utility deposit

end Ordered

section Menu

variable [Fintype Player]

/-- **The settlement error vanishes with the deferral weight.** For every
source profile and the geometric timing with weight `weight`, the turn-counted
clients' joint law of typed outcome and realized payoffs is within
`eventCount * weight` of the source joint law; along weights tending to zero
the error tends to zero (`Vegas.geometricTiming_deferral_tendsto`). -/
theorem geometricTiming_settlement_lawError
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (bounded : weight ≤ 1)
    (original : BehavioralProfile setup.program)
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who
      (sourceServiceTurnPolicy setup leaks bound turns
        (geometricTiming setup turns weight nonnegative bounded)
        (sourceServiceClientProfile setup original) who))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement (baseUtility setup leaks utility)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    PMF.WithinTV ((graph setup).order.eventCount * weight)
      (((menu.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who
          (sourceServiceTurnPolicy setup leaks bound turns
            (geometricTiming setup turns weight nonnegative bounded)
            (sourceServiceClientProfile setup original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs => (sourceReadout setup leaks final.state, payoffs)))
      ((setup.run original).map (fun state => (some state, utility state))) := by
  have all : Finset.univ.filter (fun event : (graph setup).EventId => 0 ≤ event.val) =
      Finset.univ :=
    Finset.filter_true_of_mem fun event _ => Nat.zero_le event.val
  have remaining := geometricTiming_remainingDeferral_le setup turns weight nonnegative bounded 0
  rw [all] at remaining
  exact (sourceServiceClients_settlement_lawError (serviceGraph_barrierOrdered setup (by decide))
    contract timely
    (geometricTiming setup turns weight nonnegative bounded) original menu covered sample
    authentic utility deposit).mono remaining

end Menu

end Vegas
