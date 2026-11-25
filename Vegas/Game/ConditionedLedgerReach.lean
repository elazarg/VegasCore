module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveConditionedReach
public import Vegas.Game.ConditionedLedgerClients
public import Vegas.Game.OnePacketOwnerBase

@[expose] public section

/-! # Reach weights of ledger histories on a locally observed initial component -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol EventGraphRuntime
open GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {Signal : Type*}
  {signal : State L setup.context → Signal}
  {timeouts : EventTimeouts setup.informationGraph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
  {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}

local notation "component" => fun k => Vegas.initialDistribution (setup.conditionInitial signal k)
variable (menu : (application setup timeouts leaks).ResponseMenu)
  (read : Player → (application setup timeouts leaks).Info → Signal)
  (observed : ∀ draw ∈ setup.initialDistribution.support,
    ∀ execution : (application setup timeouts leaks).Execution,
    EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
      (setup.eventInputs draw) execution.application → ∀ who,
      read who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) = signal draw)
  {key : Signal} (supported : key ∈ (setup.initialDistribution.map signal).support)

include supported in
private theorem ledger_component_atom (st : (application setup timeouts leaks).State)
    (member : st ∈ (component key).support) :
    Vegas.initialDistribution setup st = (setup.initialDistribution.map signal) key * component key
      st := by
  obtain ⟨draw, present, rfl⟩ := eq_initial_of_mem_support
    (setup := setup.conditionInitial signal key) member
  have same := (mem_support_fiberPosterior supported present).1
  rw [initialDistribution_initial (setup := setup.conditionInitial signal key)]
  change Vegas.initialDistribution setup (EventGraphRuntime.State.initial
    (setup.eventInputs draw)) = _
  rw [initialDistribution_initial]
  exact (setup.conditionInitial_initialDistribution_scale signal key supported draw same).symm

include observed supported in
/-- Every active menu decision on a component history identifies its initializing signal. -/
theorem ledger_component_active_read
    {state : (application setup timeouts leaks).ProtocolState}
    (trace : (menu.protocol (component key) horizon scheduler).Trace state)
    (who : Player) (active : (menu.protocol (component key) horizon scheduler).active state who) :
    read who ((application setup timeouts leaks).observe who state) = key := by
  cases state with
  | none =>
    change (none : Option Player) = some who at active
    cases active
  | some control =>
    change control.actor = some who at active
    have raw := menu.toRawTrace (component key) horizon scheduler trace
    change (((reactiveApplication timeouts) leaks).protocol
      (Vegas.initialDistribution (setup.conditionInitial signal key)) horizon scheduler).Trace _
        at raw
    rw [Vegas.initialDistribution, serviceInitialDistribution_eq_inputs] at raw
    have valid := reactive_history_invariant timeouts leaks
      ((setup.conditionInitial signal key).initialDistribution.map setup.eventInputs) horizon
        scheduler raw
    obtain ⟨inputs, member, inv⟩ := valid
    obtain ⟨draw, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
    have part := mem_support_fiberPosterior supported present
    simpa only [ReactiveApplication.observe, active, ↓reduceIte] using
      (observed draw part.2 control.execution inv who).trans part.1

include observed in
/-- At every initialized conditional history the original reach weight of the
locally selected raw policies is exactly the signal mass times the component reach. -/
theorem ledger_component_historyReachWeight [Finite Player]
    (strategies : ∀ k who, (menu.information (component k) horizon scheduler).BehavioralPolicy who)
    {control : (application setup timeouts leaks).Control}
    (trace : (menu.protocol (component key) horizon scheduler).Trace (some control)) :
    (menu.information (Vegas.initialDistribution setup) horizon scheduler).historyReachWeight
        (menu.signalStrategy read strategies)
        ⟨_, menu.traceOfInitialSupportSubset
          (setup.conditionInitial_ledgerSupport signal key supported) trace⟩ =
      (setup.initialDistribution.map signal) key *
        (menu.information (component key) horizon scheduler).historyReachWeight
          (strategies key) ⟨_, trace⟩ :=
  menu.signalStrategy_historyReachWeight («component» := component) (key := key)
    (setup.conditionInitial_ledgerSupport signal key supported)
    read strategies _ (PMF.apply_ne_top _ _)
    (ledger_component_atom (timeouts := timeouts) (leaks := leaks) supported)
    (fun trace who => ledger_component_active_read menu read observed supported trace who) trace

end Vegas.SourceProgram.Setup
