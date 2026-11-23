module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.ConditionedLedgerService
public import Vegas.Pending.ReactiveServiceProgress
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

/-- Players who recover the initial signal from their existing views implement the
component execution law at every round, for arbitrary component policies. -/
theorem roundsFrom_signalClients (read : Player → (app).PlayerView → Signal)
    (observed : ∀ draw ∈ setup.initialLaw.support, ∀ execution : (app).Execution,
      EventGraphRuntime.State.Invariant (graph := setup.informationGraph)
        (setup.eventInputs draw) execution.application → ∀ who,
        read who (execution.observe app who) = signal draw)
    (clients : Signal → Player → (app).Policy) (count : Nat) :
    (app).roundsFrom (Vegas.initialLaw setup) scheduler (signalClients read clients) count =
      (setup.initialLaw.map signal).bind fun value => (app).roundsFrom
        (Vegas.initialLaw (setup.conditionInitial signal value)) scheduler (clients value)
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
  · constructor
    · intro execution actor action valid _
      exact (reactive_respond_progress timeouts leaks _ execution actor action valid).invariant
    · intro execution next command valid moved
      exact (reactive_environment_progress timeouts leaks _ execution next command valid
        moved).invariant
  · intro execution valid who
    unfold signalClients
    rw [observed draw component.2 execution valid who, component.1]
  · exact EventGraphRuntime.State.initial_invariant _

end Vegas.SourceProgram.Setup
