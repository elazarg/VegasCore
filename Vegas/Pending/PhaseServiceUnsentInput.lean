/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseServiceQueryPrefix
import Vegas.Pending.PhaseSeedUnsentQueries
import Interaction.ReactiveAddressedTranscriptRequest

/-! # Actual unsent service inputs from prefixes of the retained own clock word -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseServiceScheduler

open EventGraph Interaction GameTheory.Math.Probability

variable {Player LocalSeed RestSeed : Type} [Fintype Player] [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every actual earlier unsent query consists of its elapsed clock and a
prefix of the final own clock word, with no hidden packet or source value.
Only the request projection is shared with the existing traffic theorem. -/
theorem unsent_queried_input
    (priority : RestSeed → List (app).EnvironmentEntry → (app).EnvironmentView → Nat)
    (decideLocal : PhaseSeedAddress graph → LocalSeed → PhaseSeedOperationalInput graph →
      PhaseSeedDecision)
    (rest : RestSeed) (coordinate : PhaseSeedAddress graph) (owner : Player)
    (actor : graph.actor? coordinate.1.event = some owner)
    (scheduler : (app).Scheduler) (players : Player → (app).Policy) (count : Nat)
    (state : PhaseRuntimeState graph) (execution : (app).Execution)
    (reached : execution ∈ ((app).runRounds scheduler players count
      (ReactiveApplication.Execution.initial app state)).support)
    (unsent : ∀ message ∈ execution.network.inputs,
      PhaseSeedScheduler.ownPacket coordinate.1 owner message = false) :
    ∀ item ∈ (controller runtime leaks priority decideLocal).coordinateTranscriptFrom rest
      coordinate [] execution.environmentRecall,
      item.1 = ⟨item.1.elapsed,
        ((PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
          (execution.recall owner)).map Prod.fst).take item.1.activationClocks.length, []⟩ := by
  have prefixes := initialized_queryOperationalPrefixes runtime leaks priority decideLocal rest
    coordinate owner actor scheduler players count state execution reached
  have empty := PhaseSeedCalendar.queried_emissions_nil_of_unsent runtime leaks (fun _ => 0)
    (fun _ => 0) priority rest coordinate owner actor scheduler players count state execution
      reached unsent
  have transcript :=
    ReactiveApplication.AddressedScheduler.coordinateTranscriptFrom_eq_of_request_eq
    (controller runtime leaks priority decideLocal)
    (PhaseSeedCalendar.controller runtime leaks (fun _ => 0) (fun _ => 0) priority)
    rfl rest coordinate [] execution.environmentRecall
  rw [← transcript] at empty
  intro item member
  obtain ⟨before, isPrefix, operational⟩ := prefixes item member
  have clockEq : item.1.activationClocks = before.map Prod.fst :=
    congrArg PhaseSeedOperationalInput.activationClocks operational
  obtain ⟨suffix, joined⟩ := isPrefix.map Prod.fst
  rw [← clockEq] at joined
  have absent := empty item member
  have take : ((PhaseSeedScheduler.ownerWord runtime leaks coordinate.1 owner
      (execution.recall owner)).map Prod.fst).take item.1.activationClocks.length =
        item.1.activationClocks := by
    rw [← joined]
    exact List.take_left
  cases observed : item.1 with
  | mk tick clocks emissions =>
      rw [observed] at take absent
      change emissions = [] at absent
      change _ = clocks at take
      change PhaseSeedOperationalInput.mk tick clocks emissions = ⟨tick, _, []⟩
      rw [take, absent]

end Vegas.EventGraphRuntime.PhaseServiceScheduler
