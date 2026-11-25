module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Examples.OddsEvensClientPosterior

@[expose] public section

/-! # Odd's first ready commitment callback in the periodic service -/

noncomputable section

namespace Vegas.Examples.OddsEvensLedgerClient

open OddsEvens EventGraphRuntime Interaction GameTheory.Math.Probability

local notation "schedule" => OddsEvensService.scheduler
local notation "leaks" => OddsEvensService.leaks
local notation "horizon" => OddsEvensService.horizon
local notation "oddEvent" => eventId 1

/-- Find the first ready commitment observation in Odd's recorded callbacks. -/
def firstReadyOddObservationOfRecall (entries : List app.PlayerEntry) :
    Option (List app.PlayerEntry × app.PlayerView) :=
  let index := entries.findIdx fun entry =>
    decide (entry.beforeView.application.publicView.ownTurn? odd = some oddEvent)
  (entries[index]?).map fun entry => (entries.take index, entry.beforeView)

/-- Read Odd's preceding recall and exact view from its first recorded
activation at which its own commitment was ready. -/
def firstReadyOddObservation (execution : app.Execution) :
    Option (List app.PlayerEntry × app.PlayerView) :=
  firstReadyOddObservationOfRecall (execution.logs odd)

/-- Continue from a fixed ordinary Even commitment through the Odd commitment
window with both clients silent, so the first ready Odd view can be read back
from recall without choosing Odd's commitment bit. -/
def oddCommitmentWindow (bit : Bool) : PMF app.Execution :=
  (fixedFirstCommitmentRun bit).bind fun start =>
    app.runUntilHorizon schedule (focalPlayers timeouts leaks odd app.silentPolicy)
      (fun final => oddEvent ∈ final.application.config.cut.completed) horizon start

private theorem ready (bit : Bool) (start : app.Execution)
    (reached : start ∈ (fixedFirstCommitmentRun bit).support) :
    start.application.config.cut.Ready oddEvent := by
  rw [fixedFirstCommitmentRun_config bit start reached]
  cases bit <;> decide

/-- The two fixed-bit branches of the periodic service have identical laws
of Odd's preceding recall and view at its first ready commitment callback. -/
theorem oddCommitmentWindow_firstReadyOddObservation :
    (oddCommitmentWindow false).map firstReadyOddObservation =
      (oddCommitmentWindow true).map firstReadyOddObservation := by
  let traffic := bindingTraffic timeouts leaks odd
  let observeTraffic := fun read : MessageNetwork Player app.Payload ×
      List (MessageId Player × Bool) × List app.EnvironmentEntry × List app.PlayerEntry ×
        PlayerView compiled × PublicView compiled => firstReadyOddObservationOfRecall read.2.2.2.1
  have same :
      (oddCommitmentWindow false).map traffic = (oddCommitmentWindow true).map traffic := by
    unfold oddCommitmentWindow
    simp only [PMF.map_bind]
    apply bind_eq_of_map_eq _ _ traffic traffic fixedFirstCommitmentRun_traffic
    intro left leftReached right rightReached equal
    have lengthEq : left.environmentRecall.length = right.environmentRecall.length :=
      congrArg (fun read => read.2.2.1.length) equal
    unfold ReactiveApplication.runUntilHorizon
    rw [← lengthEq]
    exact focalPhase_traffic_congr schedule odd app.silentPolicy (Or.inr rfl)
      (fun cut _ atOdd atOther => setup.dataflowGraph.sequentialize_ready_unique cut atOther atOdd)
      _ left right (fun _ => ready false left leftReached)
      (fun _ => ready true right rightReached) equal
  have projected := congrArg (PMF.map observeTraffic) same
  rw [PMF.map_comp, PMF.map_comp] at projected
  exact projected

private theorem oddCommitmentWindow_stored (bit : Bool) (final : app.Execution)
    (reached : final ∈ (oddCommitmentWindow bit).support) :
    evenBinding.get? final.application.config.store = some (.success bit) := by
  obtain ⟨start, startReached, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have stored := fixedFirstCommitmentRun_stored bit start startReached
  have path := reactive_runUntil_graph_steps timeouts leaks schedule
    (focalPlayers timeouts leaks odd app.silentPolicy)
    (fun execution => oddEvent ∈ execution.application.config.cut.completed)
    _ start final moved
  exact evenBinding.get?_preserved _ _
    (fun field value => EventGraph.Config.Step.path_store_of_some path field value)
    (.success bit) stored

/-- Conditioning on a supported first ready Odd callback preserves the fair
law of Even's bit from the ordinary commitment lottery. -/
theorem firstReadyOddCommitment_posterior
    (observed : List app.PlayerEntry × app.PlayerView)
    (present : some observed ∈
      (((uniformLaw Bool).bind oddCommitmentWindow).map firstReadyOddObservation).support) :
    (fiberPosterior ((uniformLaw Bool).bind oddCommitmentWindow)
      firstReadyOddObservation (some observed)).map
      (fun execution => evenBinding.get? execution.application.config.store) =
      (uniformLaw Bool).map (fun bit => some (.success bit)) :=
  fiberPosterior_evenBinding_of_equal_readouts oddCommitmentWindow firstReadyOddObservation
    oddCommitmentWindow_firstReadyOddObservation oddCommitmentWindow_stored
    (some observed) present

end Vegas.Examples.OddsEvensLedgerClient
