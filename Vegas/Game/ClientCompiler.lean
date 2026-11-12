/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialCompilation
import Interaction.ReactiveLedgerAssessment
import Interaction.ReactiveMenuRationality

/-! # A uniform semantic compiler for intended equilibrium clients

The compiler selects a consistent native completion at compile time.
Its output certifies equilibrium within the bounded raw response menu and
uniformly decodes its strategies to physical clients. Deviations leaving that
menu are outside the equilibrium certificate. Ledger clients realize those
decision laws when pending observations are not delivered. The completion
backend is nonconstructive. Ordinary clients retain arbitrary pending
observations admitted by the specification; only ledger-client realization
uses the explicit no-pending-delivery premise.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability GameTheory.Enforcement

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (timeouts : EventTimeouts (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup timeouts leaks).Scheduler)
  {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

local notation "Initial" => initialLaw setup
local notation "app" => application setup timeouts leaks
local notation "raw" => bounds.rawMenu timeouts leaks
local notation "model" => ReactiveApplication.ResponseMenu.information
  (bounds.rawMenu timeouts leaks) Initial horizon scheduler

variable {setup timeouts leaks bounds horizon scheduler parameter utility excludedPayoff}

variable (spec : ClientSpec setup timeouts leaks bounds horizon scheduler
  parameter utility excludedPayoff)

namespace ClientSpec

/-- Select a common consistent bounded-menu completion as part of the semantic
artifact. Runtime clients decode this selected strategy. -/
def compile (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    ClientCompilation spec intended :=
  Classical.choice (intended_raw_sequentialEquilibrium_preserved spec intended equilibrium)

end ClientSpec

namespace ClientCompilation

variable {spec} {intended : setup.intendedModel.BehavioralAssessment}
  (compiled : ClientCompilation spec intended)

/-- Physical clients for every source game and supplied intended equilibrium. -/
def clients : Player → (app).Policy :=
  (raw).decodeProfile Initial horizon scheduler compiled.assessment.strategy

/-- The uniform translation projected through current and recalled leaked fields,
retaining own actions and emitted packets. -/
def ledgerClients : Player → (app).Policy :=
  (raw).ledgerProfile Initial horizon scheduler compiled.assessment.strategy

/-- Applying the ledger projection preserves the callback law, with own actions
and emitted packets retained. -/
theorem ledgerClients_ignoreLeakedFields (who : Player) :
    ReactiveApplication.Policy.IgnoresLeakedFields (app) (compiled.ledgerClients who) :=
  (raw).ledgerProfile_ignoresLeakedFields Initial horizon scheduler
    compiled.assessment.strategy who

/-- Decoding and restriction recover the complete selected strategy. -/
theorem clients_strategy (who : Player) :
    (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who :=
  (raw).restrict_decode_embedPolicy Initial horizon scheduler who
    (compiled.assessment.strategy who)

/-- Ordinary clients remain inside the response menu at every legal decision. -/
theorem clients_admissible (who : Player) :
    (raw).Admissible Initial horizon scheduler who (compiled.clients who) :=
  (raw).decodeProfile_admissible Initial horizon scheduler compiled.assessment.strategy who

/-- Every ordinary callback law has finite support in its bounded response menu. -/
theorem clients_support_finite (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : (compiled.clients who past view).support.Finite := by
  apply ((raw).actions who past view).finite_toSet.subset
  intro response supported
  exact (raw).decode_embedPolicy_covered Initial horizon scheduler who
    (compiled.assessment.strategy who) past view response supported

/-- Erasing pending observations retains finite callback support. -/
theorem ledgerClients_support_finite (who : Player) (past : List (app).PlayerEntry)
    (view : (app).PlayerView) : (compiled.ledgerClients who past view).support.Finite :=
  compiled.clients_support_finite who
    (past.map (ReactiveApplication.PlayerEntry.ledgerOnly (app))) (view.ledgerOnly (app))

/-- Without pending delivery, ledger clients agree at every legal raw history. -/
theorem ledgerClients_agree
    (unobserved : leaks.DeliversNothing)
    (control : (app).Control)
    (trace : ((app).protocol Initial horizon scheduler).Trace (some control)) (who : Player) :
    compiled.ledgerClients who (control.execution.logs who)
      (control.execution.observe (app) who) =
      compiled.clients who (control.execution.logs who) (control.execution.observe (app) who) :=
  (raw).ledgerProfile_agrees Initial horizon scheduler unobserved
    compiled.assessment.strategy control trace who

/-- The actual ledger client's represented strategy is the selected assessment
at every legal decision input, including zero-probability histories. -/
theorem ledgerClients_strategy_at_history
    (unobserved : leaks.DeliversNothing)
    (history : ((raw).protocol Initial horizon scheduler).History) (who : Player) :
    (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
      ((model).infoOf who history.trace) =
    compiled.assessment.strategy who ((model).infoOf who history.trace) :=
  (raw).restrict_ledgerProfile_history Initial horizon scheduler unobserved
    compiled.assessment.strategy history who

/-- Every menu-admissible physical continuation is unprofitable under the
compiled assessment's belief, at on-path and off-path information sets. -/
theorem clients_sequentiallyRational (who : Player) (site : (model).InformationSite who)
    (alternative : (app).Policy)
    (covered : (raw).Admissible Initial horizon scheduler who alternative) :
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler (Function.update compiled.clients who alternative)
        history.1.state) (spec.payoff who) ≤
      expect ((compiled.assessment.belief who site).bind fun history =>
        (app).finish Initial horizon scheduler compiled.clients history.1.state)
        (spec.payoff who) := by
  let := spec.finiteNature
  have rational := (compiled.assessment.isSequentiallyRational_iff_truncated_of_bounded
    ((raw).bounded Initial horizon scheduler).wellFoundedHistories
    ((raw).bounded Initial horizon scheduler) _).mp compiled.equilibrium.1
  exact (raw).sequentiallyRational_finish Initial horizon scheduler compiled.assessment
    compiled.clients compiled.clients_admissible
    (fun history other =>
      congrFun (compiled.clients_strategy other) ((model).infoOf other history.trace))
    spec.payoff rational who site alternative covered

/-- With no pending delivery, ledger clients are rational against every
menu-admissible physical continuation under the same assessment beliefs. -/
theorem ledgerClients_sequentiallyRational (unobserved : leaks.DeliversNothing)
    (who : Player) (site : (model).InformationSite who) (alternative : (app).Policy)
    (covered : (raw).Admissible Initial horizon scheduler who alternative) :
    expect ((compiled.assessment.belief who site).bind fun history =>
      (app).finish Initial horizon scheduler
        (Function.update compiled.ledgerClients who alternative) history.1.state)
        (spec.payoff who) ≤
      expect ((compiled.assessment.belief who site).bind fun history =>
        (app).finish Initial horizon scheduler compiled.ledgerClients history.1.state)
        (spec.payoff who) := by
  let := spec.finiteNature
  have rational := (compiled.assessment.isSequentiallyRational_iff_truncated_of_bounded
    ((raw).bounded Initial horizon scheduler).wellFoundedHistories
    ((raw).bounded Initial horizon scheduler) _).mp compiled.equilibrium.1
  exact (raw).sequentiallyRational_finish Initial horizon scheduler compiled.assessment
    compiled.ledgerClients
    ((raw).ledgerProfile_admissible Initial horizon scheduler unobserved
      compiled.assessment.strategy)
    (fun history other => compiled.ledgerClients_strategy_at_history unobserved history other)
    spec.payoff rational who site alternative covered

/-- Complete physical-state correctness, before applying any outcome reader. -/
theorem clients_stateLaw :
    ((raw).run Initial horizon scheduler compiled.assessment.strategy).map History.state =
      (app).finish Initial horizon scheduler compiled.clients none :=
  (raw).runFrom_stateLaw Initial horizon scheduler compiled.assessment.strategy
    ((raw).protocol Initial horizon scheduler).initHistory

/-- Correctness of the physical clients, including joint typed readout and settled payoff. -/
theorem clients_outcomeLaw :
    ((app).finish Initial horizon scheduler compiled.clients none).bind (spec.observation) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  have same := congrArg (fun law => law.bind (spec.observation)) compiled.clients_stateLaw
  rw [PMF.bind_map] at same
  exact same.symm.trans compiled.outcomeLaw

/-- No player has defaulted in a supported ordinary-client execution, with any
pending-observation rule satisfying the compilation specification. -/
theorem clients_noDefaults (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler compiled.clients none).support)
    (control : (app).Control) (current : state = some control) :
    control.execution.application.config.defaulted = ∅ := by
  rw [← compiled.clients_stateLaw] at supported
  obtain ⟨history, reached, same⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact compiled.noDefaults history reached control (same.trans current)

/-- Supported ordinary-client executions incur no count-audit charge. -/
theorem clients_noCharges (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler compiled.clients none).support)
    (who : Player) :
    TerminalAudit.charge (app).stateTraffic
      ((countAudit timeouts) leaks spec.evidenceService.sample) state who = 0 := by
  rw [← compiled.clients_stateLaw] at supported
  obtain ⟨history, reached, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact compiled.noCharges history reached who

/-- Ledger clients have the same complete continuation law at every legal history. -/
theorem ledgerClients_continuation
    (unobserved : leaks.DeliversNothing)
    (history : ((raw).protocol Initial horizon scheduler).History) :
    ((raw).runFrom Initial horizon scheduler compiled.assessment.strategy history).map
        History.state =
      (app).finish Initial horizon scheduler compiled.ledgerClients history.state := by
  have bound := (app).trace_bound Initial horizon scheduler
    ((raw).toRawTrace Initial horizon scheduler history.trace)
  have enough : (app).rank horizon history.state ≤ 2 * horizon + 1 := by omega
  exact (raw).run_ledgerProfile_eq_finish Initial horizon scheduler unobserved
    compiled.assessment.strategy (2 * horizon + 1) history enough

/-- The initialized physical ledger run has the selected assessment's complete state law. -/
theorem ledgerClients_stateLaw
    (unobserved : leaks.DeliversNothing) :
    ((raw).run Initial horizon scheduler compiled.assessment.strategy).map History.state =
      (app).finish Initial horizon scheduler compiled.ledgerClients none :=
  compiled.ledgerClients_continuation unobserved
    ((raw).protocol Initial horizon scheduler).initHistory

/-- Ledger and ordinary clients have identical initialized physical execution laws. -/
theorem ledgerClients_finish_eq_clients (unobserved : leaks.DeliversNothing) :
    (app).finish Initial horizon scheduler compiled.ledgerClients none =
      (app).finish Initial horizon scheduler compiled.clients none :=
  (compiled.ledgerClients_stateLaw unobserved).symm.trans compiled.clients_stateLaw

/-- Ledger clients preserve the complete source configuration and settled payoff law. -/
theorem ledgerClients_outcomeLaw
    (unobserved : leaks.DeliversNothing) :
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind (spec.observation) =
    (setup.intendedModel.runBehavioral intended.strategy
      (instructionCount setup.program + 1)).map
      (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved]
  exact compiled.clients_outcomeLaw

/-- Every supported physical ledger-client execution leaves the public default set empty. -/
theorem ledgerClients_noDefaults
    (unobserved : leaks.DeliversNothing)
    (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler
      compiled.ledgerClients none).support)
    (control : (app).Control) (current : state = some control) :
    control.execution.application.config.defaulted = ∅ := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved] at supported
  exact compiled.clients_noDefaults state supported control current

/-- Supported ledger-client executions incur no count-audit charge. -/
theorem ledgerClients_noCharges
    (unobserved : leaks.DeliversNothing)
    (state : (app).ProtocolState)
    (supported : state ∈ ((app).finish Initial horizon scheduler
      compiled.ledgerClients none).support) (who : Player) :
    TerminalAudit.charge (app).stateTraffic
      ((countAudit timeouts) leaks spec.evidenceService.sample) state who = 0 := by
  rw [compiled.ledgerClients_finish_eq_clients unobserved] at supported
  exact compiled.clients_noCharges state supported who

end ClientCompilation

namespace ClientSpec

/-- Compiler correctness within the bounded raw menu: equilibrium, exact implemented
strategies, and the joint source-configuration/settled-payoff law. -/
theorem compile_correct (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended) :
    let compiled := spec.compile intended equilibrium
    compiled.assessment.IsSequentialEquilibrium
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      ((raw).bounded Initial horizon scheduler).wellFoundedHistories
      (fun who final => spec.payoff who final.state) ∧
    (∀ who, (raw).restrictPolicy Initial horizon scheduler who (compiled.clients who) =
      compiled.assessment.strategy who) ∧
    ((app).finish Initial horizon scheduler compiled.clients none).bind (spec.observation) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro compiled
  exact ⟨compiled.equilibrium, compiled.clients_strategy, compiled.clients_outcomeLaw⟩

/-- Ledger-client correctness within the bounded raw menu, with strategy agreement at every
legal decision, when the interface does not deliver pending observations. -/
theorem compile_ledger_correct (intended : setup.intendedModel.BehavioralAssessment)
    (equilibrium : setup.IntendedSequentialEquilibrium parameter utility intended)
    (unobserved : leaks.DeliversNothing) :
    let compiled := spec.compile intended equilibrium
    compiled.assessment.IsSequentialEquilibrium
      ((raw).decisionInformationAntichain Initial horizon scheduler)
      ((raw).bounded Initial horizon scheduler).wellFoundedHistories
      (fun who final => spec.payoff who final.state) ∧
    (∀ who, ReactiveApplication.Policy.IgnoresLeakedFields (app) (compiled.ledgerClients who)) ∧
    (∀ (history : ((raw).protocol Initial horizon scheduler).History) who,
      (raw).restrictPolicy Initial horizon scheduler who (compiled.ledgerClients who)
        ((model).infoOf who history.trace) =
      compiled.assessment.strategy who ((model).infoOf who history.trace)) ∧
    ((app).finish Initial horizon scheduler compiled.ledgerClients none).bind (spec.observation) =
      (setup.intendedModel.runBehavioral intended.strategy
        (instructionCount setup.program + 1)).map
        (intendedReadoutExclusion setup parameter utility excludedPayoff) := by
  intro compiled
  exact ⟨compiled.equilibrium, compiled.ledgerClients_ignoreLeakedFields,
    compiled.ledgerClients_strategy_at_history unobserved,
    compiled.ledgerClients_outcomeLaw unobserved⟩

end ClientSpec
end Vegas
