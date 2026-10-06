/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediateAudit
import Interaction.ReactiveRestrictedContinuation
import GameTheory.Protocol.BehavioralTerminal

/-! # A single clean comparator in the risk-menu game

The immediate runtime policy represents one behavioral policy of the finite
risk menu. Replacing the owner's whole policy evaluates its actual immediate
continuation from every legal clear active history, against arbitrary opponent
behavioral policies. Every supported terminal continuation has zero actual
owner collection under authentic sampling, including packets in the prefix.

The policy depends on the owner's local observation and recall. It is shared
across hidden histories and does not assume global admission at synthetic
inputs. This result concerns a comparator in the risk-menu game; it does not
embed a source equilibrium or supply a collection bound for excluded actions.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The same immediate policy is used at every information history. Its
irrelevant finite-menu fallback is only used when an input lacks admission. -/
def sourceServiceImmediateComparator {mode : EventGraph.ExecutionMode}
    {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    (bounds : MessageBounds (serviceGraph setup mode))
    (bound : (serviceGraph setup mode).EventId → Nat) (horizon : Nat)
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (profile : BehavioralProfile setup.program) (who : Player) :
    ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).information
      (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy who :=
  (bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).restrictPolicy
    (serviceInitialLaw setup mode) horizon scheduler who
    (serviceImmediatePolicy setup mode deadline leaks bound profile who)

/-- Whole-policy replacement has exactly the actual physical continuation
law. Opponent policies are arbitrary policies of the risk-menu information
model, rather than an assumed image of prescribed runtime policies. -/
theorem sourceServiceImmediateComparator_terminal_law
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    (bound : (graph setup).EventId → Nat) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (certificate : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((bounds.riskMenu (runtime setup) leaks bound).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).History) :
    (((bounds.riskMenu (runtime setup) leaks bound).information (initialLaw setup) horizon
      scheduler).runBehavioralTerminalFrom certificate
        (Profile.update (sig := ((bounds.riskMenu (runtime setup) leaks bound).information
          (initialLaw setup) horizon scheduler).behavioralSignature) baseline who
          (sourceServiceImmediateComparator bounds bound horizon scheduler profile who))
        history).map History.state =
      (application setup leaks).finish (initialLaw setup) horizon scheduler
        (Function.update ((bounds.riskMenu (runtime setup) leaks bound).decodeProfile
          (initialLaw setup) horizon scheduler baseline) who
          (sourceServiceImmediatePolicy setup leaks bound profile who)) history.state := by
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let players := Function.update (menu.decodeProfile (initialLaw setup) horizon scheduler baseline)
    who (sourceServiceImmediatePolicy setup leaks bound profile who)
  have admitted : ∀ player, menu.Admissible (initialLaw setup) horizon scheduler player
      (players player) := by
    intro player
    by_cases same : player = who
    · subst player
      simpa only [players, Function.update_self] using
        sourceServiceImmediatePolicy_risk_admissible bounds covered initialCovered capacity bound
          profile who permitted horizon scheduler
    · intro control _ _ response supported
      simp only [players, Function.update_of_ne same,
        ReactiveApplication.ResponseMenu.decodeProfile] at supported
      exact menu.decode_embedPolicy_covered (initialLaw setup) horizon scheduler player
        (baseline player) _ _ response supported
  have represented : (fun player => menu.restrictPolicy (initialLaw setup) horizon scheduler
      player (players player)) = Profile.update
        (sig := (menu.information (initialLaw setup) horizon scheduler).behavioralSignature)
        baseline who
        (sourceServiceImmediateComparator bounds bound horizon scheduler profile who) := by
    funext player
    by_cases same : player = who
    · subst player
      simp only [players, Function.update_self, Profile.update_same,
        sourceServiceImmediateComparator, menu]
    · simp only [players, Function.update_of_ne same, Profile.update_of_ne _ _ same,
        ReactiveApplication.ResponseMenu.decodeProfile]
      exact menu.restrict_decode_embedPolicy (initialLaw setup) horizon scheduler player
        (baseline player)
  rw [InformationModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded
    (menu.information (initialLaw setup) horizon scheduler) certificate
      (menu.bounded (initialLaw setup) horizon scheduler), ← represented]
  apply menu.run_restrict_eq_finish (initialLaw setup) horizon scheduler players admitted
  change app.rank horizon history.state ≤ 2 * horizon + 1
  have budget := app.trace_bound (initialLaw setup) horizon scheduler
    (menu.toRawTrace (initialLaw setup) horizon scheduler history.trace)
  omega

/-- At every actual clear active history, every supported terminal continuation
under the same whole-policy comparator has zero owner collection. The starting
history need not be reached by the baseline or by the comparator. -/
theorem sourceServiceImmediateComparator_terminal_charge_zero
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {horizon remaining : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (certificate : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((bounds.riskMenu (runtime setup) leaks bound).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (history : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).History)
    (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (clear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
      (execution.observe (application setup leaks) who) = false)
    (final : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).History)
    (reached : final ∈ (((bounds.riskMenu (runtime setup) leaks bound).information
      (initialLaw setup) horizon scheduler).runBehavioralTerminalFrom certificate
        (Profile.update (sig := ((bounds.riskMenu (runtime setup) leaks bound).information
          (initialLaw setup) horizon scheduler).behavioralSignature) baseline who
          (sourceServiceImmediateComparator bounds bound horizon scheduler profile who))
        history).support)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual) :
    TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
      (sourceServiceAudit setup leaks sample) final.state who = 0 := by
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  let model := menu.information (initialLaw setup) horizon scheduler
  let players := Function.update (menu.decodeProfile (initialLaw setup) horizon scheduler baseline)
    who (sourceServiceImmediatePolicy setup leaks bound profile who)
  have stateReached : final.state ∈ ((model.runBehavioralTerminalFrom certificate
      (Profile.update (sig := model.behavioralSignature) baseline who
        (sourceServiceImmediateComparator bounds bound horizon scheduler profile who)) history).map
      History.state).support := by
    rw [PMF.support_map]
    exact ⟨final, reached, rfl⟩
  rw [sourceServiceImmediateComparator_terminal_law bounds covered initialCovered capacity bound
    horizon scheduler profile who permitted certificate baseline history, current] at stateReached
  change final.state ∈ (app.finish (initialLaw setup) horizon scheduler players
    (some ⟨remaining, some who, execution⟩)).support at stateReached
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, ReactiveApplication.invoke,
    PMF.bind_map] at stateReached
  obtain ⟨next, continued, stateEq⟩ := PMF.support_map .. ▸ stateReached
  obtain ⟨response, chosen, nextReached⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ continued)
  have followed : players who = sourceServiceImmediatePolicy setup leaks bound profile who :=
    Function.update_self ..
  rw [followed] at chosen
  have trace := current ▸ history.trace
  have zero := sourceServiceImmediatePolicy_audit_clear_after_prefix_response bounds covered
    initialCovered capacity contract timely players who profile permitted followed execution trace
    clear response chosen remaining le_rfl next nextReached sample authentic
  rw [← stateEq]
  simpa only [Nat.sub_self, ReactiveApplication.finished] using zero

/-- A clear local information site shares one comparator across all its hidden
histories, independently of their probability under any assessment belief. -/
theorem sourceServiceImmediateComparator_charge_zero_at_information
    (bounds : MessageBounds (graph setup)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state)
    (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (certificate : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup)
      horizon scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((bounds.riskMenu (runtime setup) leaks bound).information
      (initialLaw setup) horizon scheduler).BehavioralPolicy player)
    (site : ((bounds.riskMenu (runtime setup) leaks bound).information (initialLaw setup) horizon
      scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (clear : (runtime setup).serviceRisk leaks bound who past view = false)
    (sample : List (SettledEvidence setup) → PMF (List (SettledEvidence setup)))
    (authentic : ∀ actual evidence, evidence ∈ (sample actual).support → evidence ⊆ actual) :
    ∀ history : ((bounds.riskMenu (runtime setup) leaks bound).information (initialLaw setup)
      horizon scheduler).InformationHistory who site.1,
    ∀ final ∈ (((bounds.riskMenu (runtime setup) leaks bound).information (initialLaw setup)
      horizon scheduler).runBehavioralTerminalFrom certificate
        (Profile.update (sig := ((bounds.riskMenu (runtime setup) leaks bound).information
          (initialLaw setup) horizon scheduler).behavioralSignature) baseline who
        (sourceServiceImmediateComparator bounds bound horizon scheduler profile who))
        history.1).support,
      TerminalAudit.charge ((runtime setup).serviceAuditObservation leaks)
        (sourceServiceAudit setup leaks sample) final.state who = 0 := by
  let app := application setup leaks
  let menu := bounds.riskMenu (runtime setup) leaks bound
  intro history final reached
  have active := InformationModel.InformationSite.active _ site history
  have info := (menu.info (initialLaw setup) horizon scheduler who history.1.trace).symm.trans
    (history.2.trans observed)
  cases current : history.1.state with
  | none =>
      rw [current] at active
      cases active
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      rw [current] at active info
      change actor = some who at active
      subst actor
      change (if some who = some who then
        some (execution.recall who, execution.observe app who) else none) = some (past, view)
        at info
      rw [ite_eq_left rfl] at info
      have recallEq := congrArg Prod.fst (Option.some.inj info)
      have viewEq := congrArg Prod.snd (Option.some.inj info)
      change execution.recall who = past at recallEq
      change execution.observe app who = view at viewEq
      have actualClear : (runtime setup).serviceRisk leaks bound who (execution.recall who)
          (execution.observe app who) = false := by
        rw [recallEq, viewEq]
        exact clear
      exact sourceServiceImmediateComparator_terminal_charge_zero bounds covered initialCovered
        capacity contract timely profile who permitted certificate baseline history.1 execution
        current actualClear final reached sample authentic

/-- A pointwise terminal base-payoff lower bound yields the clean comparator
certificate for every belief at the same clear information site. The chosen
policy is fixed before the belief and shared by all hidden histories. -/
theorem sourceServiceImmediateComparator_clean_lower
    {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}
    (configuration : RankSequential setup mode deadline)
    (bounds : MessageBounds (serviceGraph setup mode)) (covered : bounds.CoversBindingValues)
    (initialCovered : ∀ state ∈ (serviceInitialLaw setup mode).support, bounds.CandidateValues
      state)
    (capacity : (serviceGraph setup mode).order.eventCount ≤ bounds.candidateCount)
    {horizon : Nat} {scheduler : (serviceApplication setup mode deadline leaks).Scheduler}
    {delay bound : (serviceGraph setup mode).EventId → Nat}
    (contract : AsyncContract (serviceRuntime setup mode deadline) leaks (serviceInitialLaw setup
      mode) horizon scheduler
      delay bound)
    (timely : AsyncTimely (serviceRuntime setup mode deadline) delay bound)
    (profile : BehavioralProfile setup.program) (who : Player)
    (permitted : (profile who).Admitted setup.program (CommitmentInterface.values _))
    (certificate : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
      (serviceInitialLaw setup mode)
      horizon scheduler).WellFoundedHistories)
    (baseline : ∀ player, ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks
      bound).information
      (serviceInitialLaw setup mode) horizon scheduler).BehavioralPolicy player)
    (site : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).information
      (serviceInitialLaw setup mode) horizon
      scheduler).InformationSite who)
    (past : List (serviceApplication setup mode deadline leaks).PlayerEntry)
    (view : (serviceApplication setup mode deadline leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (clear : (serviceRuntime setup mode deadline).serviceRisk leaks bound who past view = false)
    (sample : List (SettledEvidence setup mode) → PMF (List (SettledEvidence setup mode)))
    (authentic : ∀ actual evidence, evidence ∈ (sample actual).support → evidence ⊆ actual)
    (base : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).protocol
      (serviceInitialLaw setup mode) horizon
      scheduler).History → ℝ) (lower : ℝ)
    (bounded : ∀ final, (serviceApplication setup mode deadline leaks).terminal final.state → lower
      ≤ base final)
    (belief : PMF (((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).information
      (serviceInitialLaw setup mode)
      horizon scheduler).InformationHistory who site.1)) :
    ∃ alternative : ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).information
      (serviceInitialLaw setup mode)
      horizon scheduler).BehavioralPolicy who,
    alternative = sourceServiceImmediateComparator bounds bound horizon scheduler profile who ∧
      ∀ history ∈ belief.support,
      ∀ final ∈ (((bounds.riskMenu (serviceRuntime setup mode deadline) leaks bound).information
        (serviceInitialLaw setup mode)
        horizon scheduler).runBehavioralTerminalFrom certificate
          (Profile.update (sig := ((bounds.riskMenu (serviceRuntime setup mode deadline) leaks
            bound).information
            (serviceInitialLaw setup mode) horizon scheduler).behavioralSignature) baseline who
              alternative)
          history.1).support,
        lower ≤ base final ∧ TerminalAudit.charge ((serviceRuntime setup mode
          deadline).serviceAuditObservation leaks)
          (serviceSourceAudit setup mode deadline leaks sample) final.state who = 0 := by
  obtain ⟨rfl, rfl⟩ := configuration
  refine ⟨sourceServiceImmediateComparator bounds bound horizon scheduler profile who, rfl, ?_⟩
  intro history _ final reached
  refine ⟨bounded final ?_, ?_⟩
  · exact ((bounds.riskMenu (runtime setup) leaks bound).information (initialLaw setup) horizon
      scheduler).runBehavioralTerminalFrom_support_terminal certificate _ history.1 final reached
  · exact sourceServiceImmediateComparator_charge_zero_at_information bounds covered initialCovered
      capacity contract timely profile who permitted certificate baseline site past view observed
      clear sample authentic history final reached

end Vegas
