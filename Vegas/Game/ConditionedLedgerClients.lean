module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerService
public import Vegas.Pending.ReactiveStateInvariant
public import Interaction.ReactiveRecovery

@[expose] public section

/-! # Physical clients selected by a locally observed initial signal -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
    {setup : Setup (Player := Player) (L := L)}
    {Signal : Type*} {signal : State L setup.context → Signal}
    {timeouts : EventTimeouts setup.informationGraph}
    {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph)}
    {scheduler : (application setup timeouts leaks).Scheduler}

local notation "app" => application setup timeouts leaks

/-- Each player selects its own component policy from the ordinary local player view. -/
def signalClients (read : Player → (app).PlayerView → Signal)
    (clients : Signal → Player → (app).Policy) (who : Player) : (app).Policy :=
  fun past view => clients (read who view) who past view

/-- A unilateral change can be applied before or after selecting local policies. -/
theorem signalClients_update (read : Player → (app).PlayerView → Signal)
    (clients : Signal → Player → (app).Policy) (who : Player) (alternative : (app).Policy) :
    signalClients read (fun key => Function.update (clients key) who alternative) =
      Function.update (signalClients read clients) who alternative := by
  funext player past view
  by_cases same : player = who
  · subst player
    simp [signalClients]
  · simp [signalClients, Function.update_of_ne same]

/-- After initialization, locally selected clients have the entire component continuation
law at every valid control, including controls immediately before a player's response. -/
theorem finish_signalClients (read : Player → (app).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialDistribution.support, ∀ execution : (app).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application → ∀ who,
        read who (execution.observe app who) = signal draw)
    (clients : Signal → Player → (app).Policy)
    (draw : State L setup.context) (member : draw ∈ setup.initialDistribution.support)
    (control : (app).Control)
    (valid : EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
      (setup.eventInputs draw) control.execution.application)
    (horizon : Nat) (initial component : PMF (app).State) :
    (app).finish initial horizon scheduler (signalClients read clients) (some control) =
      (app).finish component horizon scheduler (clients (signal draw)) (some control) := by
  let chosen := signalClients read clients
  let inputs : setup.informationGraph.Inputs := setup.eventInputs draw
  have invariant := ((reactiveStateInvariant timeouts) leaks inputs).policyInvariant _ chosen
  have agree (execution : (app).Execution) (ok : execution.application.Invariant inputs)
      (who : Player) : chosen who (execution.logs who) (execution.observe app who) =
        clients (signal draw) who (execution.logs who) (execution.observe app who) := by
    unfold chosen signalClients
    rw [observed draw member execution ok who]
  have resume : (app).resume chosen control.actor control.execution =
      (app).resume (clients (signal draw)) control.actor control.execution := by
    cases control.actor with
    | none => rfl
    | some who =>
      exact congrArg (fun law => law.map (control.execution.respond app who)) (agree _ valid who)
  simp only [ReactiveApplication.finish]
  change (((app).resume chosen control.actor control.execution).bind _).map _ = _
  rw [← resume]
  congr 1
  apply bind_congr_on_support _
  intro next reached
  exact invariant.runRounds_congr _ agree scheduler _ next (invariant.resume _ _ _ valid reached)

/-- Players who recover the initial signal from their existing views implement the
component execution law at every round, for arbitrary component policies. -/
theorem roundsFrom_signalClients (read : Player → (app).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialDistribution.support, ∀ execution : (app).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application → ∀ who,
        read who (execution.observe app who) = signal draw)
    (clients : Signal → Player → (app).Policy) (count : Nat) :
    (app).roundsFrom (Vegas.initialDistribution setup) scheduler
      (signalClients read clients) count =
      (setup.initialDistribution.map signal).bind fun value => (app).roundsFrom
        (Vegas.initialDistribution (setup.conditionInitial signal value)) scheduler (clients value)
          count := by
  rw [← setup.roundsFrom_conditionInitial_reconstruct signal (signalClients read clients) count]
  apply bind_congr_on_support _
  intro value supported
  unfold ReactiveApplication.roundsFrom
  apply bind_congr_on_support _
  intro state member
  obtain ⟨draw, present, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp member
  have component := mem_support_fiberPosterior supported present
  apply ReactiveApplication.PolicyInvariant.runRounds_congr
    (predicate := fun execution : (app).Execution =>
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application)
  · exact ((reactiveStateInvariant timeouts) leaks _).policyInvariant _ _
  · intro execution valid who
    unfold signalClients
    rw [observed draw component.2 execution valid who, component.1]
  · exact EventGraphRuntime.State.initial_invariant _

end Vegas.SourceProgram.Setup
