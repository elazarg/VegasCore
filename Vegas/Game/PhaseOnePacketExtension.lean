/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import GameTheory.Math.Probability.ExpectationBind
import GameTheoryExtensions.Analysis.Protocol.TerminalAudit
import Vegas.Pending.PhaseCountCollection
import Interaction.ReactiveLocalContinuation
import Interaction.ReactiveFiniteAssessment
import GameTheoryExtensions.Protocol.ContinuationHorizon
import Interaction.ReactiveAuditContinuation

/-! # Sequential equilibrium extension to the actual phased raw runtime

Coverage of forbidden packets and a deposit covering the payoff spread extend
any phased one-packet equilibrium to the actual bounded raw menu.
The extension preserves the complete terminal-history law and realized payoffs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

open Classical in
/-- Committing, at an actual decision history, a response whose local
envelope the count verdict forbids gives the coverage product as a lower bound
on the expected collection, under arbitrary later behavioral policies of any
response menu. -/
theorem countForbidden_collection_committed
    (menu : (phaseApplication runtime leaks).ResponseMenu)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (service : EvidenceReportService (Evidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : EvidenceCoverage service observationRate deliveryRate)
    (profile : ∀ player, (menu.information initial horizon scheduler).BehavioralPolicy player)
    (history : (menu.protocol initial horizon scheduler).History)
    (who : Player) (remaining : Nat) (execution : (phaseApplication runtime leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (info : (menu.information initial horizon scheduler).InfoState who)
    (choice : (menu.information initial horizon scheduler).Choice who info)
    (observed : (menu.information initial horizon scheduler).infoOf who history.trace = info)
    (material : (phaseApplication runtime leaks).Submission)
    (selected : choice.1 = some ⟨some material⟩)
    (forbidden : permits ((phaseApplication runtime leaks).outputs (execution.recall who))
      (localEnvelope runtime leaks who (execution.recall who)
        (execution.observe (phaseApplication runtime leaks) who) material) = false) :
    observationRate who * deliveryRate who ≤
      expect ((menu.information initial horizon scheduler).runBehavioralTerminalFrom certificate
        (Profile.update (sig := (menu.information initial horizon scheduler).behavioralSignature)
          profile who ((profile who).commit info choice)) history)
        (fun final => TerminalAudit.charge (phaseApplication runtime leaks).stateTraffic
          (audit runtime leaks service.sample) final.state who) := by
  classical
  subst info
  let app := phaseApplication runtime leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  let updated := Profile.update (sig := model.behavioralSignature) profile who
    ((profile who).commit (model.infoOf who history.trace) choice)
  let observe := fun final : protocol.History => app.stateTraffic final.state
  change observationRate who * deliveryRate who ≤
    expect (model.runBehavioralTerminalFrom certificate updated history)
      (fun final => TerminalAudit.charge observe (audit runtime leaks service.sample)
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
  have recalled := countRecall_history runtime leaks activeTrace
  obtain ⟨inputs, fresh, _⟩ := permits_respond runtime leaks execution recalled who material
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
  exact app.audit_collection_continuation menu initial horizon scheduler permits
    (fun left right message same => permits_congr left right message same)
    (audit runtime leaks service.sample) (fun who => observationRate who * deliveryRate who)
    (audit_collection runtime leaks service observationRate deliveryRate
      delivery_nonnegative coverage) updated fuel next
    ⟨remaining, none, execution.respond app who ⟨some material⟩⟩ nextState _
    (by rw [inputs]; exact List.mem_append_right _ (List.mem_singleton_self _))
    (by rw [fresh]; exact forbidden)


variable (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (initial : PMF (PhaseRuntimeState graph)) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

/-- Every excluded raw response emits locally forbidden signed evidence. -/
theorem onePacket_extra (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (available : response ∈ (rawMenu runtime leaks bounds).actions who past view)
    (absent : response ∉ onePacketActions runtime leaks bounds who past view) :
    ∃ material, response.transmission = some material ∧
      permits ((phaseApplication runtime leaks).outputs past)
        (localEnvelope runtime leaks who past view material) = false := by
  rw [mem_onePacketActions] at absent
  cases sent : response.transmission with
  | none => exact (absent ⟨available, Or.inl sent⟩).elim
  | some material =>
      refine ⟨material, rfl, ?_⟩
      cases verdict : permits ((phaseApplication runtime leaks).outputs past)
          (localEnvelope runtime leaks who past view material) with
      | false => rfl
      | true => exact (absent ⟨available, Or.inr ⟨material, sent, verdict⟩⟩).elim

/-- The one-packet game as an action restriction of the bounded raw
game. It changes no application state, observation, response or scheduler
step. -/
def onePacketRestriction :
    ((onePacketMenu runtime leaks bounds).information initial horizon scheduler).ActionRestriction
      ((rawMenu runtime leaks bounds).information initial horizon scheduler) :=
  ReactiveApplication.ResponseMenu.IncludedIn.actionRestriction
    (onePacketMenu_in_raw runtime leaks bounds) initial horizon scheduler

/-- An excluded choice is, at a decision input, a transmission whose local
envelope the count verdict forbids against own earlier packets. -/
theorem onePacketRestriction_extra (who : Player)
    (site : ((onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).InformationSite who)
    (action : ((rawMenu runtime leaks bounds).information initial horizon scheduler).Choice who
      ((onePacketRestriction runtime leaks bounds initial horizon scheduler).site who site).1)
    (extra : action ∉ Set.range
      ((onePacketRestriction runtime leaks bounds initial horizon scheduler).choice who site.1)) :
    ∃ past view material, site.1 = some (past, view) ∧ action.1 = some ⟨some material⟩ ∧
      permits ((phaseApplication runtime leaks).outputs past)
        (localEnvelope runtime leaks who past view material) = false := by
  let raw := rawMenu runtime leaks bounds
  let included := onePacketMenu_in_raw runtime leaks bounds
  rcases site with ⟨info, occurs⟩
  cases info with
  | none =>
      obtain ⟨_, _, response, member⟩ := occurs
      cases member
  | some data =>
      change (raw.information initial horizon scheduler).Choice who (some data) at action
      change action ∉ Set.range ((included.actionRestriction initial horizon scheduler).choice
        who (some data)) at extra
      obtain ⟨response, value, available, absent⟩ := included.extra_choice_response
        initial horizon scheduler who data.1 data.2 action extra
      obtain ⟨material, sent, rejected⟩ := onePacket_extra runtime leaks bounds who data.1 data.2
        response available absent
      refine ⟨data.1, data.2, material, rfl, ?_, rejected⟩
      rw [value]
      rcases response with ⟨transmission⟩
      change transmission = some material at sent
      rw [sent]

local instance rawHistory_nonempty :
    Nonempty ((rawMenu runtime leaks bounds).protocol initial horizon scheduler).History :=
  ⟨((rawMenu runtime leaks bounds).protocol initial horizon scheduler).initHistory⟩

open Classical in
/-- **One-packet equilibria extend to the bounded physical raw runtime.** Under
coverage of forbidden count evidence, if the coverage rate times the deposit
covers the spread of the utility over all protocol states, every sequential
equilibrium of the one-packet game under the utility extends to a sequential
equilibrium of the bounded physical raw runtime under the utility minus the
deposit for each collected count charge. The extension keeps the strategies
and beliefs at every one-packet site, has the same terminal law and the same
joint law of terminal history and realized payoffs, and charges nobody on its
paths. -/
theorem onePacket_raw_sequentialEquilibrium
    [(phaseApplication runtime leaks).FiniteNature initial scheduler]
    (service : EvidenceReportService (Evidence graph))
    (observationRate deliveryRate : Player → ℝ)
    (delivery_nonnegative : ∀ who, 0 ≤ deliveryRate who)
    (coverage : EvidenceCoverage service observationRate deliveryRate)
    (utility : (phaseApplication runtime leaks).ProtocolState → Player → ℝ)
    (lower upper deposit : Player → ℝ)
    (lower_le : ∀ state who, lower who ≤ utility state who)
    (le_upper : ∀ state who, utility state who ≤ upper who)
    (deposit_nonnegative : ∀ who, 0 ≤ deposit who)
    (sufficient : ∀ who,
      upper who - lower who ≤ observationRate who * deliveryRate who * deposit who) :
    let onePacket := onePacketMenu runtime leaks bounds
    let raw := rawMenu runtime leaks bounds
    let restriction := onePacketRestriction runtime leaks bounds initial horizon scheduler
    let sourceCertificate := (onePacket.bounded initial horizon scheduler).wellFoundedHistories
    let targetCertificate := (raw.bounded initial horizon scheduler).wellFoundedHistories
    let observe := (phaseApplication runtime leaks).stateTraffic
    let audit := audit runtime leaks service.sample
    let payoff := TerminalAudit.utility utility observe audit deposit
    let settle := TerminalAudit.settlement utility observe audit deposit
    ∀ source : (onePacket.information initial horizon scheduler).BehavioralAssessment,
      source.IsSequentialEquilibrium
        (onePacket.decisionInformationAntichain initial horizon scheduler) sourceCertificate
        (fun who final => utility final.state who) →
    ∃ target : (raw.information initial horizon scheduler).BehavioralAssessment,
      target.IsSequentialEquilibrium
        (raw.decisionInformationAntichain initial horizon scheduler) targetCertificate
        (fun who final => payoff final.state who) ∧
      restriction.ExtendsProfile source.strategy target.strategy ∧
      (∀ who site, target.belief who (restriction.site who site) =
        (source.belief who site).map (restriction.informationHistory who site)) ∧
      ((onePacket.information initial horizon scheduler).runBehavioralTerminalFrom
          sourceCertificate source.strategy
          (onePacket.protocol initial horizon scheduler).initHistory).map restriction.history =
        (raw.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
          (raw.protocol initial horizon scheduler).initHistory ∧
      ((onePacket.information initial horizon scheduler).runBehavioralTerminalFrom
          sourceCertificate source.strategy
          (onePacket.protocol initial horizon scheduler).initHistory).map
          (fun final => (restriction.history final, utility final.state)) =
        ((raw.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
          (raw.protocol initial horizon scheduler).initHistory).bind
          (fun final => (settle final.state).map fun payoffs => (final, payoffs)) ∧
      ∀ final ∈ ((raw.information initial horizon scheduler).runBehavioralTerminalFrom
          targetCertificate target.strategy
          (raw.protocol initial horizon scheduler).initHistory).support,
        ∀ who, TerminalAudit.charge observe audit final.state who = 0 := by
  classical
  intro onePacket raw restriction sourceCertificate targetCertificate observe audit payoff
    settle source equilibrium
  let app := phaseApplication runtime leaks
  obtain ⟨target, targetSE, agrees, beliefs, laws, settled, clean⟩ :=
    restriction.sequential_equilibrium_extends_of_terminal_audit
      (onePacket.decisionInformationAntichain initial horizon scheduler)
      sourceCertificate targetCertificate (raw.uniformAssessment initial horizon scheduler)
      (raw.uniform_fullyMixed initial horizon scheduler)
      (raw.decisionRecall initial horizon scheduler)
      (fun final who => utility final.state who) (fun final who => utility final.state who)
      (fun final => observe final.state) audit (fun _ _ => rfl)
      (fun final who => onePacketMenu_countCharge_zero runtime leaks bounds initial horizon
        scheduler service final who)
      lower upper (fun who => observationRate who * deliveryRate who) deposit
      deposit_nonnegative (fun final who => lower_le final.state who)
      (fun final who => le_upper final.state who)
      (fun who => by linarith [sufficient who])
      (fun profile who site action extra history => by
        rw [TerminalAudit.collection_probability]
        obtain ⟨past, view, material, input, chosen, rejected⟩ :=
          onePacketRestriction_extra runtime leaks bounds initial horizon scheduler who site
            action extra
        have observed : (raw.information initial horizon scheduler).infoOf who
            (restriction.history history.1).trace = (restriction.site who site).1 :=
          (restriction.observed who history.1).trans history.2
        have observedState : app.observe who (restriction.history history.1).state =
            some (past, view) :=
          (raw.info initial horizon scheduler who
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
              exact countForbidden_collection_committed raw initial horizon scheduler
                targetCertificate service observationRate deliveryRate delivery_nonnegative
                coverage profile (restriction.history history.1) who remaining execution current
                (restriction.site who site).1 action observed material chosen rejected
            · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observedState
              cases observedState)
      source equilibrium
  exact ⟨target, targetSE, agrees, beliefs, laws, settled, clean⟩

end Vegas.EventGraphRuntime.PhaseCount
