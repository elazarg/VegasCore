/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSiteBridge
import Vegas.Game.SourceServiceGeometricTiming
import Vegas.Game.SourceServiceImmediateRisk
import Vegas.Game.SourceServiceOwnerSettled
import Vegas.Game.SourceServiceAudit
import Vegas.Game.RevealServiceCalendarState

/-! # The realized settlement law of the turn-counted policy

The turn-counted prescribed policy and its first-turn limit differ only in the
owners' timing lotteries. From every completion boundary, the two runs to the
horizon are within the remaining deferral weight of each other in total
variation, as laws of whole executions, for every scheduler
(`Vegas.sourceServiceTurnPolicy_runToHorizon_bind_within`). Each event's phase
splits by the owner's turn index, whose first branch is exactly the first-turn
phase, and the remaining continuation is compared recursively from the next
boundary. A run that spends the horizon, and the terminal boundary, where every
player is idle, leave nothing to compare.

Under the asynchronous contract the first-turn limit has the exact source joint
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

/-- Scheduler rounds are a run that never stops early. -/
private theorem runRounds_eq_runUntil_never {Principal : Type} [DecidableEq Principal]
    (app : ReactiveApplication Principal) (scheduler : app.Scheduler)
    (players : Principal → app.Policy) (count : Nat) (execution : app.Execution) :
    app.runRounds scheduler players count execution =
      app.runUntil scheduler players (fun _ => False) count execution := by
  induction count generalizing execution with
  | zero => rfl
  | succ count ih =>
      simp only [ReactiveApplication.runRounds, ReactiveApplication.runUntil, ↓reduceIte]
      congr 1
      funext next
      exact ih next

/-- At a terminal configuration no player has a turn, so the turn-counted
policy is silent. -/
theorem sourceServiceTurnPolicy_terminal (bound : (graph setup).EventId → Nat) (turns : Nat)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (state : EventGraphRuntime.State (graph setup))
    (terminal : state.config.cut.IsPrefix (graph setup).order.eventCount)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (current : view.application.publicView = state.publicView) :
    sourceServiceTurnPolicy setup leaks bound turns timing profile who past view =
      (application setup leaks).silentPolicy past view := by
  have idle : view.application.publicView.ownTurn? who = none := by
    cases turn : view.application.publicView.ownTurn? who with
    | none => rfl
    | some event =>
        have ready := (PublicView.ownTurn?_spec _ who event turn).1
        rw [current] at ready
        have rankEq := (ready_iff_rank setup _ _ terminal event).mp
          ((State.publicView_eventReady _ event).mp ready)
        exact absurd rankEq (Nat.ne_of_lt event.isLt)
  simp only [sourceServiceTurnPolicy, idle]

/-- From a terminal configuration the turn-counted policy runs as silence, for
every timing. -/
theorem runRounds_turnPolicy_terminal (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (count : Nat)
    (execution : (application setup leaks).Execution)
    (terminal : execution.application.config.cut.IsPrefix (graph setup).order.eventCount) :
    (application setup leaks).runRounds scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) count execution =
      (application setup leaks).runRounds scheduler
        (fun _ => (application setup leaks).silentPolicy) count execution := by
  let app := application setup leaks
  rw [runRounds_eq_runUntil_never, runRounds_eq_runUntil_never]
  apply app.runUntil_congr_of_agree scheduler _ _ _
    (fun current => current.application.config.cut.IsPrefix (graph setup).order.eventCount)
  · intro current holds _ command _ middle moved who active
    cases command with
    | activate actor =>
        have sameApp := activation_application setup leaks current middle actor moved
        exact sourceServiceTurnPolicy_terminal bound turns timing profile middle.application
          (by rw [sameApp]; exact holds) who _ _ rfl
    | «include» _ => cases active
    | application _ => cases active
    | wait => cases active
  · intro current holds _ next reached
    have one : next ∈ (app.runRounds scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) 1 current).support := by
      simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using reached
    rw [runRounds_config_terminal scheduler _ 1 current next holds one]
    exact holds
  · exact terminal

/-- Before an actorless event completes, the turn-counted policy runs as
silence. -/
theorem runUntil_turnPolicy_actorless (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId)
    (actorless : (graph setup).actor? event = none) (count : Nat)
    (execution : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution) :
    (application setup leaks).runUntil scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  rw [runUntil_turnPolicy_eq_phase scheduler bound turns timing profile event count execution
    ordered seen, phaseProfile_actorless setup leaks bound turns timing profile event actorless]

/-- **Phase decomposition by turn index.** Before an owned event completes,
from an execution whose recorded responses never saw it ready, the
turn-counted policy runs as the owner's timing lottery over the members that
decide at the selected turn, every other player silent. -/
theorem runUntil_turnPolicy_owned (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (turns : Nat) (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner) (count : Nat)
    (execution : (application setup leaks).Execution)
    (ordered : execution.application.config.cut.IsPrefix event.val)
    (seen : ReadySeen setup leaks event.val execution)
    (untouched : Untouched setup leaks event execution) :
    (application setup leaks).runUntil scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (timing event owner owned).bind (fun slot =>
        (application setup leaks).runUntil scheduler
          (Function.update (fun _ => (application setup leaks).silentPolicy) owner
            (sourceServiceTurnFamily setup leaks bound profile owner event turns slot))
          (fun final => event ∈ final.application.config.cut.completed) count execution) := by
  let app := application setup leaks
  rw [runUntil_turnPolicy_eq_phase scheduler bound turns timing profile event count execution
    ordered seen, phaseProfile_owned setup leaks bound turns timing profile event owner owned]
  let mixture := app.policyMixture (timing event owner owned)
    (sourceServiceTurnFamily setup leaks bound profile owner event turns)
  have prior : mixture.posterior (execution.recall owner) = timing event owner owned := by
    apply app.policyMixture_posterior_of_agree _ _ app.silentPolicy
    intro earlier entry member slot
    apply app.turnScheduledPolicy_of_none
    apply sourceServiceTurn_of_not_turn
    intro turn
    have entryMember : entry ∈ execution.recall owner :=
      member.subset (List.mem_append_right _ (List.mem_singleton_self _))
    exact untouched owner entry entryMember (PublicView.ownTurn?_spec _ owner event turn).1
  rw [← app.runUntil_policyMixture scheduler (timing event owner owned)
    (sourceServiceTurnFamily setup leaks bound profile owner event turns) owner _ _ _ execution,
    prior]

/-! ## Coupling with the first-turn limit -/

/-- **The turn-counted policy is close to its first-turn limit as a law of
executions.** For every scheduler, timing and source profile, from every
completion boundary of rank `rank` within the horizon, the turn-counted and
first-turn runs to the horizon, followed by any common kernel, are within the
sum of the remaining events' deferral weights in total variation. -/
theorem sourceServiceTurnPolicy_runToHorizon_bind_within {β : Type}
    (scheduler : (application setup leaks).Scheduler) {horizon turns : Nat}
    {bound : (graph setup).EventId → Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (readout : (application setup leaks).Execution → PMF β) (rank : Nat)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns timing profile) rank execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    PMF.WithinTV (∑ event ∈ Finset.univ.filter
        (fun event : (graph setup).EventId => rank ≤ event.val), timing.deferral event)
      (((application setup leaks).runToHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) horizon execution).bind
          readout)
      (((application setup leaks).runToHorizon scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          horizon execution).bind readout) := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns timing profile
  let limit := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  suffices remaining : ∀ gap rank (execution : app.Execution),
      (graph setup).order.eventCount - rank = gap →
      CompletionBoundary setup leaks scheduler players rank execution →
      execution.environmentRecall.length ≤ horizon →
      PMF.WithinTV (∑ event ∈ Finset.univ.filter
          (fun event : (graph setup).EventId => rank ≤ event.val), timing.deferral event)
        ((app.runToHorizon scheduler players horizon execution).bind readout)
        ((app.runToHorizon scheduler limit horizon execution).bind readout) from
    remaining _ rank execution rfl boundary bounded
  intro gap
  induction gap with
  | zero =>
      intro rank execution gapEq boundary bounded
      have rankEq : rank = (graph setup).order.eventCount := by
        have := boundary.ordered.1
        omega
      subst rankEq
      have same : app.runToHorizon scheduler players horizon execution =
          app.runToHorizon scheduler limit horizon execution := by
        unfold ReactiveApplication.runToHorizon
        rw [runRounds_turnPolicy_terminal scheduler bound turns timing profile _ execution
            boundary.ordered,
          runRounds_turnPolicy_terminal scheduler bound turns (firstTurnTiming setup turns)
            profile _ execution boundary.ordered]
      rw [same]
      exact (PMF.WithinTV.refl _).mono
        (Finset.sum_nonneg fun event _ => deferral_nonneg timing event)
  | succ gap ih =>
      intro rank execution gapEq boundary bounded
      have inside : rank < (graph setup).order.eventCount := by omega
      let event : (graph setup).EventId := ⟨rank, inside⟩
      let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
      rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players stop horizon execution,
        app.runToHorizon_eq_runUntilHorizon_bind scheduler limit stop horizon execution,
        PMF.bind_bind, PMF.bind_bind]
      have later := PMF.WithinTV.bind_right (app.runUntilHorizon scheduler players stop horizon
          execution)
        (first := fun stopped => (app.runToHorizon scheduler players horizon stopped).bind readout)
        (second := fun stopped => (app.runToHorizon scheduler limit horizon stopped).bind readout)
        (error := ∑ other ∈ Finset.univ.filter
          (fun other : (graph setup).EventId => rank + 1 ≤ other.val), timing.deferral other)
        (fun stopped reached => by
          rcases app.runUntilHorizon_stopped scheduler players stop horizon
              (horizon - execution.environmentRecall.length) execution stopped (by omega)
              reached with done | spent
          · obtain ⟨stoppedBounded, stoppedBoundary⟩ := CompletionBoundary.stopped event execution
              boundary bounded stopped reached done
            exact ih (rank + 1) stopped (by omega) stoppedBoundary stoppedBounded
          · have frozen (any : Player → app.Policy) :
                app.runToHorizon scheduler any horizon stopped = PMF.pure stopped := by
              unfold ReactiveApplication.runToHorizon
              rw [spent, Nat.sub_self]
              rfl
            rw [frozen players, frozen limit]
            exact (PMF.WithinTV.refl _).mono
              (Finset.sum_nonneg fun other _ => deferral_nonneg timing other))
      have step : PMF.WithinTV (timing.deferral event)
          ((app.runUntilHorizon scheduler players stop horizon execution).bind
            (fun stopped => (app.runToHorizon scheduler limit horizon stopped).bind readout))
          ((app.runUntilHorizon scheduler limit stop horizon execution).bind
            (fun stopped => (app.runToHorizon scheduler limit horizon stopped).bind readout)) := by
        obtain ⟨ranked, rankedOrdered, rankedSeen⟩ := roundsFrom_ranked setup leaks scheduler
          players _ execution boundary.supported
        have rankEq := isPrefix_unique rankedOrdered boundary.ordered
        subst rankEq
        have seen : ReadySeen setup leaks event.val execution := rankedSeen
        unfold ReactiveApplication.runUntilHorizon
        cases owned : (graph setup).actor? event with
        | none =>
            rw [runUntil_turnPolicy_actorless scheduler bound turns timing profile event owned _
                execution boundary.ordered seen,
              runUntil_turnPolicy_actorless scheduler bound turns (firstTurnTiming setup turns)
                profile event owned _ execution boundary.ordered seen]
            exact (PMF.WithinTV.refl _).mono (deferral_nonneg timing event)
        | some owner =>
            have untouched := boundary.untouched event rfl
            rw [runUntil_turnPolicy_owned scheduler bound turns timing profile event owner owned _
                execution boundary.ordered seen untouched,
              runUntil_turnPolicy_owned scheduler bound turns (firstTurnTiming setup turns)
                profile event owner owned _ execution boundary.ordered seen untouched,
              PMF.bind_bind,
              show (firstTurnTiming setup turns) event owner owned = PMF.pure 0 from rfl,
              PMF.pure_bind]
            exact PMF.WithinTV.of_bind_point _ 0 _
              (le_of_eq (deferral_eq timing event owner owned).symm)
      have total : (∑ other ∈ Finset.univ.filter
            (fun other : (graph setup).EventId => rank + 1 ≤ other.val),
            timing.deferral other) + timing.deferral event =
          ∑ other ∈ Finset.univ.filter
            (fun other : (graph setup).EventId => rank ≤ other.val), timing.deferral other := by
        have single : timing.deferral event =
            ∑ other, if other = event then timing.deferral other else 0 := by simp
        rw [Finset.sum_filter, Finset.sum_filter, single, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro other _
        by_cases same : other = event
        · subst same
          simp [event]
        · have different : other.val ≠ rank := fun equal => same (Fin.ext equal)
          by_cases above : rank + 1 ≤ other.val
          · simp [above, show rank ≤ other.val by omega, same]
          · simp [above, show ¬ rank ≤ other.val by omega, same]
      exact (later.trans step).mono total.le

/-- **Initialized coupling.** For every scheduler, the turn-counted policy's
executions after `horizon` rounds from initialization, followed by any common
kernel, are within the total deferral weight of the first-turn limit's. -/
theorem sourceServiceTurnPolicy_roundsFrom_bind_within {β : Type}
    (scheduler : (application setup leaks).Scheduler) {horizon turns : Nat}
    {bound : (graph setup).EventId → Nat} (timing : TurnTiming setup turns)
    (profile : BehavioralProfile setup.program)
    (readout : (application setup leaks).Execution → PMF β) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) horizon).bind readout)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          horizon).bind readout) := by
  let app := application setup leaks
  unfold ReactiveApplication.roundsFrom
  rw [PMF.bind_bind, PMF.bind_bind]
  apply PMF.WithinTV.bind_right
  intro state supported
  have close := sourceServiceTurnPolicy_runToHorizon_bind_within (horizon := horizon)
    (bound := bound) scheduler
    timing profile readout 0 (ReactiveApplication.Execution.initial app state)
    (initial_completionBoundary setup leaks scheduler _ state supported) (Nat.zero_le _)
  have all : Finset.univ.filter (fun event : (graph setup).EventId => 0 ≤ event.val) =
      Finset.univ :=
    Finset.filter_true_of_mem fun event _ => Nat.zero_le event.val
  rw [all] at close
  exact close

/-! ## The exact settlement law of the first-turn limit -/

/-- **No charge under the first-turn limit.** Under the asynchronous contract,
at every execution the first-turn profile reaches within the horizon, an
authentic partial audit collects from no player: no owner has a public
binding omission and the settled record permits every transmitted packet. -/
theorem sourceServiceFirstTurn_charge_zero {scheduler : (application setup leaks).Scheduler}
    {horizon turns : Nat} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (count : Nat) (within : count ≤ horizon) (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        count).support)
    (who : Player) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample)
        ((application setup leaks).finished execution) who = 0 := by
  have noMiss := sourceServiceFirstTurn_no_miss contract timely
    (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile) who
    turns profile rfl count within execution reached
  change TerminalAudit.charge _ _
    (some (⟨0, none, execution⟩ : (application setup leaks).Control)) who = 0
  unfold sourceServiceAudit
  rw [(runtime setup).serviceAudit_charge, noMiss]
  simp only [Bool.false_eq_true, ↓reduceIte]
  apply (application setup leaks).sampledTrafficAudit_sound
  · exact authentic _
  · intro record member owner
    exact sourceServiceTurnPolicy_owner_settled contract
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile) who
      (firstTurnTiming setup turns) profile rfl count within execution reached record member owner

/-- **The first-turn limit's exact settlement law.** Under the asynchronous
contract with `delay + bound < deadline`, for every source profile with
effective disclosures, the first-turn profile's executions after `horizon`
rounds have the source joint law of typed outcome and realized payoffs, for
every authentic partial audit and every deposit. -/
theorem sourceServiceFirstTurn_settlement_law [Finite Player]
    {scheduler : (application setup leaks).Scheduler}
    {horizon turns : Nat} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    ((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          horizon).bind (fun execution =>
        (TerminalAudit.settlement (baseUtility setup leaks utility)
          ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample) deposit
            ((application setup leaks).finished execution)).map fun payoffs =>
          (sourceReadout setup leaks ((application setup leaks).finished execution), payoffs)) =
      (setup.run profile).map (fun state => (some state, utility state)) := by
  have clean : ∀ execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        horizon).support,
      (TerminalAudit.settlement (baseUtility setup leaks utility)
          ((runtime setup).serviceAuditObservation leaks)
          (sourceServiceAudit setup leaks sample) deposit
            ((application setup leaks).finished execution)).map (fun payoffs =>
          (sourceReadout setup leaks ((application setup leaks).finished execution), payoffs)) =
        PMF.pure (sourceReadout setup leaks ((application setup leaks).finished execution),
          baseUtility setup leaks utility ((application setup leaks).finished execution)) := by
    intro execution reached
    rw [TerminalAudit.settlement_clean (baseUtility setup leaks utility) _ _ deposit
      ((application setup leaks).finished execution)
      (sourceServiceFirstTurn_charge_zero contract timely profile sample authentic horizon le_rfl
        execution reached), PMF.pure_map]
  have exact := BoundaryContinuationWithin.law setup leaks
    (sourceServiceTurnPolicy_boundaryContinuationWithin
      (sourceServiceTurnPolicy_firstTurnCompletes contract timely (firstTurnTiming setup turns)
        profile effective))
    (fun rank => Finset.sum_eq_zero fun event _ => firstTurnTiming_deferral setup turns event)
  have terminal : ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        horizon).map (fun execution =>
          sourceReadout setup leaks ((application setup leaks).finished execution)) =
      (setup.run profile).map some := by
    rw [← initialLaw_bind_sourceContinuation setup profile]
    unfold ReactiveApplication.roundsFrom
    rw [PMF.map_bind]
    apply bind_congr_on_support _
    intro state supported
    exact exact 0 (ReactiveApplication.Execution.initial (application setup leaks) state)
      (initial_completionBoundary setup leaks scheduler _ state supported) (Nat.zero_le _)
  have joint := congrArg (PMF.map (fun state : Option (State L setup.program.terminalCtx) =>
    (state, fun who => state.elim 0 (fun final => utility final who)))) terminal
  simp only [PMF.map_comp, Function.comp_def, Option.elim_some] at joint
  exact (bind_congr_on_support _ clean).trans ((PMF.bind_pure_comp _ _).trans joint)

/-! ## The settlement law of the turn-counted policy -/

/-- **The turn-counted policy's settlement law on executions.** Under the
asynchronous contract with `delay + bound < deadline`, for every turn timing
and every source profile with effective disclosures, the turn-counted
profile's executions after `horizon` rounds have the source joint law of typed
outcome and realized payoffs within the total deferral weight in total
variation, for every authentic partial audit and every deposit. -/
theorem sourceServiceTurnPolicy_execution_settlement_lawError [Finite Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (baseUtility setup leaks utility)
              ((runtime setup).serviceAuditObservation leaks)
              (sourceServiceAudit setup leaks sample) deposit
                ((application setup leaks).finished execution)).map fun payoffs =>
              (sourceReadout setup leaks ((application setup leaks).finished execution), payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) := by
  rw [← sourceServiceFirstTurn_settlement_law contract timely profile effective sample authentic
    utility deposit]
  exact sourceServiceTurnPolicy_roundsFrom_bind_within scheduler timing profile _

/-- The turn-counted clients of a source profile follow the profile with
ineffective disclosure intentions replaced by withholding. -/
abbrev sourceServiceClientProfile (setup : Setup (Player := Player) (L := L))
    (original : BehavioralProfile setup.program) : BehavioralProfile setup.program :=
  normalizeDisclosureProfile setup.program [] (Revelations.initial setup.context) original

/-- The clients' profile has only effective disclosures. -/
theorem sourceServiceClientProfile_effective (original : BehavioralProfile setup.program)
    (who : Player) :
    (sourceServiceClientProfile setup original who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context) :=
  (original who).normalizeDisclosureFrom_effective setup.program []
    (Revelations.initial setup.context) (fun view => PMF.pure view.2)

/-- The clients' profile has the original profile's source law. -/
theorem sourceServiceClientProfile_run [Finite Player]
    (original : BehavioralProfile setup.program) :
    setup.run (sourceServiceClientProfile setup original) = setup.run original := by
  unfold Setup.run
  apply bind_congr_on_support _
  intro initial _
  exact normalizeDisclosureProfile_runFrom setup.program original (setup.initialConfig initial)

/-- **Honest execution of the turn-counted clients.** Under the asynchronous
contract with `delay + bound < deadline`, for every turn timing and every
source profile:

* the clients' executions after `horizon` rounds have the profile's source joint
  law of typed outcome and realized payoffs within the total deferral weight in
  total variation, for every authentic partial audit and every deposit;
* every packet transmitted by a player following its client is permitted by
  the settled record at every execution reached within the horizon, whatever
  the other players do. -/
theorem sourceServiceClients_honestExecution [Finite Player]
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (original : BehavioralProfile setup.program)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    PMF.WithinTV (∑ event, timing.deferral event)
      (((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing
          (sourceServiceClientProfile setup original)) horizon).bind
          (fun execution =>
            (TerminalAudit.settlement (baseUtility setup leaks utility)
              ((runtime setup).serviceAuditObservation leaks)
              (sourceServiceAudit setup leaks sample) deposit
                ((application setup leaks).finished execution)).map fun payoffs =>
              (sourceReadout setup leaks ((application setup leaks).finished execution), payoffs)))
      ((setup.run original).map (fun state => (some state, utility state))) ∧
    ∀ (players : Player → (application setup leaks).Policy) (who : Player),
      players who = sourceServiceTurnPolicy setup leaks bound turns timing
        (sourceServiceClientProfile setup original) who →
      ∀ count ≤ horizon, ∀ execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
        scheduler players count).support,
      ∀ record ∈ (application setup leaks).executionTraffic execution,
        record.envelope.sender = who →
          ((runtime setup).settledRecord leaks execution).permits record.envelope = true := by
  refine ⟨?_, fun players who follows count within execution reached =>
    sourceServiceTurnPolicy_owner_settled contract players who timing
      (sourceServiceClientProfile setup original) follows count within execution reached⟩
  rw [← sourceServiceClientProfile_run original]
  exact sourceServiceTurnPolicy_execution_settlement_lawError contract timely timing
    (sourceServiceClientProfile setup original) (sourceServiceClientProfile_effective original)
    sample authentic utility deposit

section Menu

variable [Fintype Player]

/-- **Honest execution with realized settlement.** Under the asynchronous
contract with `delay + bound < deadline`, for every turn timing and every
source profile with effective disclosures, players admissible for a response
menu that follow the turn-counted policy have, in the menu's information model,
the source joint law of typed outcome and realized payoffs within the total
deferral weight in total variation, for every authentic partial audit and
every deposit. Binding omissions and expired resolutions caused by deferral
are part of this error. -/
theorem sourceServiceTurnPolicy_settlement_lawError
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
      (Revelations.initial setup.context))
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who
      (sourceServiceTurnPolicy setup leaks bound turns timing profile who))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement (baseUtility setup leaks utility)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    PMF.WithinTV (∑ event, timing.deferral event)
      (((menu.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who
          (sourceServiceTurnPolicy setup leaks bound turns timing profile who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs => (sourceReadout setup leaks final.state, payoffs)))
      ((setup.run profile).map (fun state => (some state, utility state))) := by
  intro settle
  have physical := menu.run_restrict_eq_finish (initialLaw setup) horizon scheduler
    (sourceServiceTurnPolicy setup leaks bound turns timing profile) covered (2 * horizon + 1)
    (menu.protocol (initialLaw setup) horizon scheduler).initHistory le_rfl
  have states : ((menu.information (initialLaw setup) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who
        (sourceServiceTurnPolicy setup leaks bound turns timing profile who))
      (2 * horizon + 1)).map (fun final => final.state) =
        (initialLaw setup).bind (fun state =>
          ((application setup leaks).runRounds scheduler
            (sourceServiceTurnPolicy setup leaks bound turns timing profile) horizon
            (ReactiveApplication.Execution.initial (application setup leaks) state)).map
              (application setup leaks).finished) := by
    rw [InformationModel.runBehavioral]
    exact physical
  have native : ((menu.information (initialLaw setup) horizon scheduler).runBehavioral
      (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who
        (sourceServiceTurnPolicy setup leaks bound turns timing profile who))
      (2 * horizon + 1)).bind (fun final =>
        (settle final.state).map fun payoffs => (sourceReadout setup leaks final.state, payoffs)) =
      ((application setup leaks).roundsFrom (initialLaw setup) scheduler
        (sourceServiceTurnPolicy setup leaks bound turns timing profile) horizon).bind
          (fun execution => (settle ((application setup leaks).finished execution)).map
            fun payoffs => (sourceReadout setup leaks
              ((application setup leaks).finished execution), payoffs)) := by
    have joint := congrArg (fun law : PMF (application setup leaks).ProtocolState =>
      law.bind fun final =>
        (settle final).map fun payoffs => (sourceReadout setup leaks final, payoffs)) states
    simp only [PMF.bind_map, PMF.bind_bind] at joint
    refine joint.trans ?_
    unfold ReactiveApplication.roundsFrom
    simp only [PMF.bind_bind, Function.comp_def]
    rfl
  rw [native]
  exact sourceServiceTurnPolicy_execution_settlement_lawError contract timely timing profile
    effective sample authentic utility deposit

/-- **Honest execution with realized settlement, for every source profile.**
Under the asynchronous contract with `delay + bound < deadline`, for every turn
timing and every source profile, players admissible for a response menu that
follow the turn-counted clients of the profile have, in the menu's information
model, the profile's source joint law of typed outcome and realized payoffs
within the total deferral weight in total variation, for every authentic
partial audit and every deposit. -/
theorem sourceServiceClients_settlement_lawError
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (timing : TurnTiming setup turns) (original : BehavioralProfile setup.program)
    (menu : (application setup leaks).ResponseMenu)
    (covered : ∀ who, menu.Admissible (initialLaw setup) horizon scheduler who
      (sourceServiceTurnPolicy setup leaks bound turns timing
        (sourceServiceClientProfile setup original) who))
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (utility : State L setup.program.terminalCtx → Player → ℝ) (deposit : Player → ℝ) :
    let settle := TerminalAudit.settlement (baseUtility setup leaks utility)
      ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) deposit
    PMF.WithinTV (∑ event, timing.deferral event)
      (((menu.information (initialLaw setup) horizon scheduler).runBehavioral
        (fun who => menu.restrictPolicy (initialLaw setup) horizon scheduler who
          (sourceServiceTurnPolicy setup leaks bound turns timing
            (sourceServiceClientProfile setup original) who))
        (2 * horizon + 1)).bind (fun final =>
          (settle final.state).map fun payoffs => (sourceReadout setup leaks final.state, payoffs)))
      ((setup.run original).map (fun state => (some state, utility state))) := by
  intro settle
  rw [← sourceServiceClientProfile_run original]
  exact sourceServiceTurnPolicy_settlement_lawError contract timely timing
    (sourceServiceClientProfile setup original) (sourceServiceClientProfile_effective original)
    menu covered sample authentic utility deposit

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
  exact (sourceServiceClients_settlement_lawError contract timely
    (geometricTiming setup turns weight nonnegative bounded) original menu covered sample
    authentic utility deposit).mono remaining

end Menu

end Vegas
