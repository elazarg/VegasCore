/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ExpectationBind
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveAliasEquilibrium
import Interaction.ReactiveLocalContinuation
import GameTheoryExtensions.Protocol.ContinuationHorizon
import Interaction.ReactiveAuditContinuation

/-! # Sequential equilibria of the one-packet game under the count audit

The one-packet game restricts the bounded effective runtime to silence and
responses transmitting a packet the count verdict permits. Both games have the
same application, scheduler, observations, horizon and initial law, and are
evaluated with a state utility, minus the deposit for each collected count
charge.

The count audit charges nobody in the one-packet game, under any scheduler. An
excluded response transmits a packet the count verdict forbids, and that
packet stays forbidden under every later play, so coverage of forbidden count
evidence collects it with probability at least the coverage rate. Once the rate
times the deposit covers the spread of the utility, every sequential
equilibrium of the one-packet game extends to the bounded effective runtime and
then to the bounded raw runtime, with the same law of play and no charge on its
paths.

The utility bounds range over all protocol states, so the spread does not
depend on the scheduler, and deposits can be fixed before it. Missed bindings
are not charged; the utility is free to treat them as exclusions.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

open Classical in
/-- Committing, at an actual decision history, a response whose local
envelope the count verdict forbids gives the coverage product as a lower bound
on the expected collection, under arbitrary later behavioral policies of any
response menu. -/
theorem countForbidden_collection_committed
    (menu : (runtime.reactiveApplication leaks).ResponseMenu)
    (initial : PMF (runtime.reactiveApplication leaks).State) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (runtime.reactiveApplication leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information initial horizon scheduler).InfoState who)
    (choice : (menu.information initial horizon scheduler).Choice who info)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace = info)
    (material : (runtime.reactiveApplication leaks).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (forbidden : countPermits ((runtime.reactiveApplication leaks).outputs (execution.recall who))
      (runtime.localEnvelope leaks who (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who) material) = false) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge (runtime.reactiveApplication leaks).stateTraffic
          (runtime.countAudit leaks service.sample) final.state who) := by
  classical
  subst info
  let app := runtime.reactiveApplication leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  let updated := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  let observe := fun final : protocol.History => app.stateTraffic final.state
  change observationRate who * deliveryRate who ≤
    expect (model.runBehavioralTerminalFrom certificate updated history)
      (fun final => TerminalAudit.charge observe (runtime.countAudit leaks service.sample)
        final who)
  let rawTrace := menu.toRawTrace initial horizon scheduler history.trace
  have traceBound := app.trace_bound initial horizon scheduler rawTrace
  have traceLength : rawTrace.length = history.trace.length :=
    menu.toRawTrace_length initial horizon scheduler history.trace
  have positive : 0 < app.rank horizon history.state := by
    rw [current]
    change 0 < 2 * remaining + 1
    omega
  let fuel := 2 * horizon + 1 - history.trace.length - 1
  have fuelEq : 1 + fuel = 2 * horizon + 1 - history.trace.length := by
    dsimp only [fuel]
    omega
  have committed := menu.run_commit_response initial horizon scheduler profile
    history who remaining execution current choice ⟨some material⟩ selected
  change (model.runBehavioralFrom updated 1 history).map History.state = _ at committed
  have activeTrace : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ rawTrace
  have recalled := runtime.countRecall_history leaks activeTrace
  obtain ⟨inputs, fresh, _⟩ := runtime.countPermits_respond leaks execution recalled who material
  rw [model.runBehavioralTerminalFrom_eq_remaining certificate updated
    (menu.bounded initial horizon scheduler) history, ← fuelEq,
    model.runBehavioralFrom_add]
  refine expect_bind_ge_constant_on_support _ _ _ _
    (TerminalAudit.payoffIntegrable_charge _ _ _ _) ?_
  intro next supported
  have nextState : next.state =
      some ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ := by
    have member : next.state ∈
        ((model.runBehavioralFrom updated 1 history).map History.state).support := by
      rw [PMF.support_map]
      exact ⟨next, supported, rfl⟩
    rw [committed] at member
    exact (PMF.mem_support_pure_iff _ _).mp member
  exact app.audit_collection_continuation menu initial horizon scheduler countPermits
    (fun left right message same => countPermits_congr left right message same)
    (runtime.countAudit leaks service.sample) (fun who => observationRate who * deliveryRate who)
    (runtime.countAudit_collection leaks service observationRate deliveryRate
      delivery_nonnegative coverage) updated fuel next
    ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ nextState _
    (by rw [inputs]; exact List.mem_append_right _ (List.mem_singleton_self _))
    (by rw [fresh]; exact forbidden)

namespace MessageBounds

variable (bounds : MessageBounds graph) (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
  (initial : PMF (State graph)) (horizon : Nat)
  (scheduler : (runtime.reactiveApplication leaks).Scheduler)

/-- The one-packet game as an action restriction of the bounded effective
game. It changes no application state, observation, response or scheduler
step. -/
def onePacketRestriction :
    ((bounds.onePacketMenu runtime leaks).information initial horizon scheduler).ActionRestriction
      ((bounds.menu runtime leaks).information initial horizon scheduler) :=
  ReactiveApplication.ResponseMenu.IncludedIn.actionRestriction
    (bounds.onePacketMenu_in_effective runtime leaks) initial horizon scheduler

/-- An excluded choice is, at a decision input, a transmission whose local
envelope the count verdict forbids against own earlier packets. -/
theorem onePacketRestriction_extra (who : Player)
    (site : ((bounds.onePacketMenu runtime leaks).information initial horizon
      scheduler).InformationSite who)
    (action : ((bounds.menu runtime leaks).information initial horizon scheduler).Choice who
      ((bounds.onePacketRestriction runtime leaks initial horizon scheduler).site who site).1)
    (extra : action ∉ Set.range
      ((bounds.onePacketRestriction runtime leaks initial horizon scheduler).choice who site.1)) :
    ∃ past view material, site.1 = some (past, view) ∧ action.1 = some ⟨some material⟩ ∧
      countPermits ((runtime.reactiveApplication leaks).outputs past)
        (runtime.localEnvelope leaks who past view material) = false := by
  let effective := bounds.menu runtime leaks
  let included := bounds.onePacketMenu_in_effective runtime leaks
  rcases site with ⟨info, occurs⟩
  cases info with
  | none =>
      obtain ⟨_, _, response, member⟩ := occurs
      cases member
  | some data =>
      change (effective.information initial horizon scheduler).Choice who (some data) at action
      change action ∉ Set.range ((included.actionRestriction initial horizon scheduler).choice
        who (some data)) at extra
      obtain ⟨response, value, available, absent⟩ := included.extra_choice_response
        initial horizon scheduler who data.1 data.2 action extra
      obtain ⟨material, sent, rejected⟩ := bounds.onePacket_extra runtime leaks who data.1 data.2
        response available absent
      refine ⟨data.1, data.2, material, rfl, ?_, rejected⟩
      rw [value]
      rcases response with ⟨transmission⟩
      change transmission = some material at sent
      rw [sent]

local instance effectiveHistory_nonempty :
    Nonempty ((bounds.menu runtime leaks).protocol initial horizon scheduler).History :=
  ⟨((bounds.menu runtime leaks).protocol initial horizon scheduler).initHistory⟩

open Classical in
/-- **One-packet equilibria extend to the bounded effective runtime.** Under
coverage of forbidden count evidence, if the coverage rate times the deposit
covers the spread of the utility over all protocol states, every sequential
equilibrium of the one-packet game under the utility extends to a sequential
equilibrium of the bounded effective runtime under the utility minus the
deposit for each collected count charge. The extension keeps the strategies
and beliefs at every one-packet site, has the same terminal law and the same
joint law of terminal history and realized payoffs, and charges nobody on its
paths. -/
theorem onePacket_sequentialEquilibrium_extends
    [(runtime.reactiveApplication leaks).FiniteNature initial scheduler]
    (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (utility : (runtime.reactiveApplication leaks).ProtocolState → Player → ℝ)
    (lower upper deposit : Player → ℝ)
    (lower_le : ∀ state who, lower who ≤ utility state who)
    (le_upper : ∀ state who, utility state who ≤ upper who)
    (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      upper who - lower who ≤ observationRate who * deliveryRate who * deposit who) :
    let onePacket := bounds.onePacketMenu runtime leaks
    let effective := bounds.menu runtime leaks
    let restriction := bounds.onePacketRestriction runtime leaks initial horizon scheduler
    let sourceCertificate := (onePacket.bounded initial horizon scheduler).wellFoundedHistories
    let targetCertificate := (effective.bounded initial horizon scheduler).wellFoundedHistories
    let observe := (runtime.reactiveApplication leaks).stateTraffic
    let audit := runtime.countAudit leaks service.sample
    let payoff := TerminalAudit.utility utility observe audit deposit
    let settle := TerminalAudit.settlement utility observe audit deposit
    ∀ source : (onePacket.information initial horizon scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium
        (onePacket.decisionInformationAntichain initial horizon scheduler) sourceCertificate
        (fun who final => utility final.state who) →
    ∃ target : (effective.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (effective.decisionInformationAntichain initial horizon scheduler) targetCertificate
        (fun who final => payoff final.state who) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      ((onePacket.information initial horizon scheduler).runBehavioralTerminalFrom
          sourceCertificate source.strategy
          (onePacket.protocol initial horizon scheduler).initHistory).map restriction.history =
        (effective.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
          (effective.protocol initial horizon scheduler).initHistory ∧
      ((onePacket.information initial horizon scheduler).runBehavioralTerminalFrom
          sourceCertificate source.strategy
          (onePacket.protocol initial horizon scheduler).initHistory).map
          (fun final => (restriction.history final, utility final.state)) =
        ((effective.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
          (effective.protocol initial horizon scheduler).initHistory).bind
          (fun final => (settle final.state).map fun payoffs => (final, payoffs)) ∧
      ∀ final ∈ ((effective.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
          (effective.protocol initial horizon scheduler).initHistory).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0 := by
  classical
  intro onePacket effective restriction sourceCertificate targetCertificate observe audit payoff
    settle source equilibrium
  let app := runtime.reactiveApplication leaks
  obtain ⟨target, targetSE, agrees, beliefs, laws, settled, clean⟩ :=
    restriction.sequential_equilibrium_extends_of_terminal_audit
      (onePacket.decisionInformationAntichain initial horizon scheduler)
      sourceCertificate targetCertificate (effective.uniformAssessment initial horizon scheduler)
      (effective.uniform_fullyMixed initial horizon scheduler)
      (effective.decisionRecall initial horizon scheduler)
      (fun final who => utility final.state who) (fun final who => utility final.state who)
      (fun final => observe final.state) audit (fun _ _ => rfl)
      (fun final who => bounds.onePacketMenu_countCharge_zero runtime leaks initial horizon
        scheduler service final who)
      lower upper (fun who => observationRate who * deliveryRate who) deposit
      deposit_nonnegative (fun final who => lower_le final.state who)
      (fun final who => le_upper final.state who)
      (fun who => by linarith [sufficient who])
      (fun profile who site action extra history => by
        rw [TerminalAudit.collection_probability]
        obtain ⟨past, view, material, input, chosen, rejected⟩ :=
          bounds.onePacketRestriction_extra runtime leaks initial horizon scheduler who site
            action extra
        have observed : (effective.information initial horizon scheduler).infoOf who
            (restriction.history history.1).trace = (restriction.site who site).1 :=
          (restriction.observed who history.1).trans history.2
        have observedState : app.observe who (restriction.history history.1).state =
            some (past, view) :=
          (effective.info initial horizon scheduler who
            (restriction.history history.1).trace).symm.trans (observed.trans input)
        cases current : (restriction.history history.1).state with
        | none =>
            rw [current] at observedState
            cases observedState
        | some control =>
            rcases control with ⟨remaining, actor, execution⟩
            rw [current] at observedState
            by_cases active : actor = some who
            · subst actor
              simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq,
                Prod.mk.injEq] at observedState
              obtain ⟨rfl, rfl⟩ := observedState
              exact countForbidden_collection_committed effective initial horizon scheduler
                targetCertificate service observationRate deliveryRate delivery_nonnegative
                coverage profile (restriction.history history.1) who remaining execution current
                (restriction.site who site).1 action observed material chosen rejected
            · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observedState
              cases observedState)
      source equilibrium
  exact ⟨target, targetSE, agrees, beliefs, laws, settled, clean⟩

open Classical in
/-- **One-packet equilibria extend to the bounded raw runtime.** Under the
hypotheses of `onePacket_sequentialEquilibrium_extends`, and a utility that
ignores private response representations, every sequential equilibrium of the
one-packet game extends to a sequential equilibrium of the bounded raw runtime
under the utility minus the deposit for each collected count charge. Its law of
normalized play is the one-packet law of play, its joint law of normalized
terminal state and realized payoffs is the one-packet law of terminal state and
utility, and it charges nobody on its paths. -/
theorem onePacket_raw_sequentialEquilibrium
    [(runtime.reactiveApplication leaks).FiniteNature initial scheduler]
    (service : EvidenceReportService (CountEvidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : CountEvidenceCoverage service observationRate deliveryRate)
    (utility : (runtime.reactiveApplication leaks).ProtocolState → Player → ℝ)
    (normalized : ∀ state,
      utility ((runtime.reactiveNormalization leaks).state state) = utility state)
    (lower upper deposit : Player → ℝ)
    (lower_le : ∀ state who, lower who ≤ utility state who)
    (le_upper : ∀ state who, utility state who ≤ upper who)
    (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      upper who - lower who ≤ observationRate who * deliveryRate who * deposit who) :
    let onePacket := bounds.onePacketMenu runtime leaks
    let raw := bounds.rawMenu runtime leaks
    let sourceCertificate := (onePacket.bounded initial horizon scheduler).wellFoundedHistories
    let normalize := (runtime.reactiveNormalization leaks).state
    let observe := (runtime.reactiveApplication leaks).stateTraffic
    let audit := runtime.countAudit leaks service.sample
    let payoff := TerminalAudit.utility utility observe audit deposit
    let settle := TerminalAudit.settlement utility observe audit deposit
    ∀ source : (onePacket.information initial horizon scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium
        (onePacket.decisionInformationAntichain initial horizon scheduler) sourceCertificate
        (fun who final => utility final.state who) →
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibriumFor
        (raw.decisionInformationAntichain initial horizon scheduler)
        (fun who site => target.truncatedContinuationContext site
          (fun history => payoff history.state who) (2 * horizon + 1)) ∧
      (∀ final ∈ ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0) ∧
      ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).map (fun final => normalize final.state) =
        ((onePacket.information initial horizon scheduler).runBehavioral source.strategy
          (2 * horizon + 1)).map History.state ∧
      ((raw.information initial horizon scheduler).runBehavioral target.strategy
          (2 * horizon + 1)).bind
          (fun final => (settle final.state).map fun payoffs => (normalize final.state, payoffs)) =
        ((onePacket.information initial horizon scheduler).runBehavioral source.strategy
          (2 * horizon + 1)).map (fun final => (final.state, utility final.state)) := by
  classical
  intro onePacket raw sourceCertificate normalize observe audit payoff settle source equilibrium
  let effective := bounds.menu runtime leaks
  obtain ⟨effectiveTarget, effectiveSE, _, _, laws, _, clean⟩ :=
    bounds.onePacket_sequentialEquilibrium_extends runtime leaks initial horizon scheduler service
      observationRate deliveryRate delivery_nonnegative coverage utility lower upper deposit
      lower_le le_upper deposit_nonnegative sufficient source equilibrium
  have truncated := (effectiveTarget.isSequentialEquilibrium_iff_truncated_of_bounded _ _
    (effective.bounded initial horizon scheduler).wellFoundedHistories
    (effective.bounded initial horizon scheduler) _).mp effectiveSE
  obtain ⟨target, _, targetSE, _, stateLaw⟩ :=
    bounds.exists_canonicalRaw_sequentialEquilibrium runtime leaks initial horizon scheduler
      effectiveTarget (fun who state => payoff state who) truncated
  have observation (state : (runtime.reactiveApplication leaks).ProtocolState) :
      observe ((runtime.reactiveNormalization leaks).state state) = observe state :=
    (runtime.reactiveApplication leaks).stateTraffic_normalization
      (runtime.reactiveNormalization leaks) state
  have payoffInvariant (state : (runtime.reactiveApplication leaks).ProtocolState) :
      payoff ((runtime.reactiveNormalization leaks).state state) = payoff state := by
    funext who
    simp only [payoff, TerminalAudit.utility, TerminalAudit.charge, normalized, observation]
  have effectiveLaw := InformationModel.runBehavioralTerminalFrom_initHistory
    (effective.information initial horizon scheduler)
    (effective.bounded initial horizon scheduler).wellFoundedHistories effectiveTarget.strategy
    (effective.bounded initial horizon scheduler)
  have sourceLaw := InformationModel.runBehavioralTerminalFrom_initHistory
    (onePacket.information initial horizon scheduler)
    (onePacket.bounded initial horizon scheduler).wellFoundedHistories source.strategy
    (onePacket.bounded initial horizon scheduler)
  have effectiveStates : ((effective.information initial horizon scheduler).runBehavioral
      effectiveTarget.strategy (2 * horizon + 1)).map History.state =
      ((onePacket.information initial horizon scheduler).runBehavioral source.strategy
        (2 * horizon + 1)).map History.state := by
    rw [← effectiveLaw, ← laws, sourceLaw, PMF.map_comp]
    rfl
  obtain ⟨rawClean, rawSettlement⟩ :=
    TerminalAudit.settlement_transport_of_normalized_law
      (((effective.information initial horizon scheduler).runBehavioral
        effectiveTarget.strategy (2 * horizon + 1)).map
          (fun final : (effective.protocol initial horizon scheduler).History => final.state))
      (((raw.information initial horizon scheduler).runBehavioral target.strategy
        (2 * horizon + 1)).map
          (fun final : (raw.protocol initial horizon scheduler).History => final.state))
      normalize (by simpa only [PMF.map_comp, Function.comp_def] using stateLaw)
      utility observe audit deposit normalized observation
      (fun state supported who => by
        rw [PMF.support_map, ← effectiveLaw] at supported
        obtain ⟨original, reached, rfl⟩ := supported
        exact clean original reached who)
  refine ⟨target, ?_, ?_, stateLaw.trans effectiveStates, ?_⟩
  · simpa only [payoffInvariant] using targetSE
  · intro final reached who
    exact rawClean final.state (by
      rw [PMF.support_map]
      exact ⟨final, reached, rfl⟩) who
  · have transported := rawSettlement.trans
      (congrArg (PMF.map fun state => (state, utility state)) effectiveStates)
    simpa only [PMF.bind_map, PMF.map_comp, Function.comp_def] using transported


end MessageBounds

end Vegas.EventGraphRuntime
