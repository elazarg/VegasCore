module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerFiber
public import Interaction.ReactiveResponseEvaluation

@[expose] public section

/-! # Physical policies of a ledger assessment on observed components -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {Signal : Type*}
  {signal : State L setup.context → Signal}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}

variable (menu : (application setup timeouts leaks).ResponseMenu)
  (supported : ∀ value, value ∈ (setup.initialDistribution.map signal).support)
  (read : Player → (application setup timeouts leaks).Info → Signal)
  (observed : ∀ draw ∈ setup.initialDistribution.support,
    ∀ execution : (application setup timeouts leaks).Execution,
    State.Invariant (graph := setup.informationGraph) (setup.eventInputs draw)
      execution.application → ∀ who,
      read who (some (execution.logs who, execution.observe (application setup timeouts leaks)
        who)) = signal draw)
  (viewRead : Player → (application setup timeouts leaks).PlayerView → Signal)
  (same : ∀ who past view, read who (some (past, view)) = viewRead who view)

local notation "law" k => Vegas.initialDistribution (setup.conditionInitial signal k)

include same in
/-- Decoding the single glued assessment chooses each player's component client
from its existing view, for every callback and every recalled history. -/
theorem decodeProfile_componentAssessment
    (assessments : ∀ k, (menu.information (law k) horizon scheduler).BehavioralAssessment) :
    menu.decodeProfile (Vegas.initialDistribution setup) horizon scheduler
      (ledger_componentAssessment menu supported read observed assessments).strategy =
    signalClients (setup := setup) (timeouts := timeouts) (leaks := leaks) viewRead (fun k =>
      menu.decodeProfile (law k) horizon scheduler (assessments k).strategy) := by
  funext who past view
  exact congrArg (fun k => menu.decodeProfile (law k) horizon scheduler
    (assessments k).strategy who past view) (same who past view)

end Vegas.SourceProgram.Setup
