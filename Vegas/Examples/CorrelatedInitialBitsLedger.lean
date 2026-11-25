module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.CorrelatedInitialBits
public import Vegas.Game.ConditionedLedgerClients

@[expose] public section

/-! # Conditioning ledger clients on private copies of a common bit -/

noncomputable section

namespace Vegas.Examples.CorrelatedInitialBits

open SourceProgram Interaction EventGraphRuntime

variable {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}

local notation "app" => application setup timeouts leaks

/-- Each player reads its own private input cell directly from the native player view. -/
def ledgerBit : Player → (app).PlayerView → Bool
  | false, view => (view.application.observation.store (.inl ⟨0, by decide⟩)).getD false
  | true, view => (view.application.observation.store (.inl ⟨1, by decide⟩)).getD false

private theorem config_inputs {inputs : setup.informationGraph.Inputs}
    {config : setup.informationGraph.Config} (reachable : config.Reachable inputs) :
    config.inputs = inputs := by
  induction reachable with
  | initial => rfl
  | step _ event ready action next supported ih =>
    exact (EventGraph.Config.Step.inputs_eq ⟨event, ready, action, supported⟩).trans ih

/-- All raw responses and builder commands preserve the owner's access to its bit. -/
theorem ledgerBit_observe (draw : State simpleExpr context)
    (member : draw ∈ setup.initialDistribution.support)
    (execution : (app).Execution)
    (valid : EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application)
    (who : Player) : ledgerBit who (execution.observe app who) = signal draw := by
  obtain ⟨bit, rfl⟩ := initialDistribution_support draw member
  have inputs := config_inputs valid.reachable
  cases who
  · change (setup.informationGraph.playerStore false execution.application.config.store
        (.inl ⟨0, by decide⟩)).getD false = bit
    rw [EventGraph.playerStore_of_visible _ _ _ _ (by decide),
      EventGraph.Config.store_input, inputs]
    rfl
  · change (setup.informationGraph.playerStore true execution.application.config.store
        (.inl ⟨1, by decide⟩)).getD false = bit
    rw [EventGraph.playerStore_of_visible _ _ _ _ (by decide),
      EventGraph.Config.store_input, inputs]
    rfl

/-- One locally signal-dependent client profile realizes the exact mixture of the two
component execution laws, for any component clients, scheduler and pending observation. -/
theorem ledgerBit_execution_distribution (scheduler : (app).Scheduler)
    (clients : Bool → Player → (app).Policy) (count : Nat) :
    (app).roundsFrom (Vegas.initialDistribution setup) scheduler
      (Setup.signalClients ledgerBit clients)
        count =
      (setup.initialDistribution.map signal).bind fun bit => (app).roundsFrom
        (Vegas.initialDistribution (setup.conditionInitial signal bit)) scheduler
          (clients bit) count :=
  Setup.roundsFrom_signalClients ledgerBit ledgerBit_observe clients count

end Vegas.Examples.CorrelatedInitialBits
