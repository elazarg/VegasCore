/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstDecision
import Vegas.Examples.LateOpeningRuntimeAliceOpeningIncentive

/-! # The authentic charge for a nongenuine first late Alice packet

A raw first late submission may modify private preparation and may even be
accepted by the handler. Its actual emitted envelope enters permanent public
traffic. If that complete envelope is not the genuine initial opening, the
authentic terminal audit charges Alice regardless of all later player policies.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstPacket

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Math.Probability GameTheory.Protocol GameTheory.Enforcement
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeAliceContinuation
  LateOpeningRuntimeAliceFirstDecision LateOpeningRuntimeUtility LateOpeningRuntimeReadout

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def responseLaw (decision : DecisionHistory weight nonnegative) (response : app.Action)
    (players : Player → app.Policy) : PMF app.Execution :=
  app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 22
    (decision.execution.respond app alice response)

theorem nongenuine_payoff_upper (decision : DecisionHistory weight nonnegative)
    (submission : app.Submission)
    (nongenuine : ¬ LateOpeningRuntimeAliceFirstDecision.EmitsOpening
      weight nonnegative decision submission)
    (players : Player → app.Policy) {reward forfeit : ℝ}
    (rewardNonnegative : 0 ≤ reward) (forfeitNonnegative : 0 ≤ forfeit)
    (deposit : Player → ℝ) (depositNonnegative : 0 ≤ deposit alice) :
    expect (responseLaw weight nonnegative decision ⟨some submission⟩ players)
      (aliceUtility reward forfeit deposit) ≤ reward - deposit alice := by
  apply expect_le_const _ _
    (aliceUtility_integrable rewardNonnegative forfeitNonnegative deposit depositNonnegative _) _
  intro execution reached
  let packet : Message Player app.Payload :=
    ⟨(alice, 0), app.packet (app.submit decision.execution.application alice submission) alice
      (decision.execution.network.known alice) submission⟩
  have present : packet ∈
      (decision.execution.respond app alice ⟨some submission⟩).network.inputs := by
    change packet ∈ decision.execution.network.inputs ++ [⟨(alice,
      decision.execution.network.nextSerial alice), _⟩]
    rw [decision_serial weight nonnegative decision]
    exact List.mem_append_right _ (List.mem_singleton_self _)
  obtain ⟨after⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 22 decision.execution alice
      ⟨some submission⟩ decision.trace
  obtain ⟨trace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 0 22 _ execution after reached
  have retained := (input_persists players packet).runRounds
    (LateOpeningRuntimeService.scheduler weight nonnegative) 22 _ execution present reached
  have traffic := app.stateTraffic_inputs initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  change (app.executionTraffic execution).map ReactiveApplication.TrafficRecord.envelope =
    execution.network.inputs at traffic
  rw [← traffic] at retained
  obtain ⟨actual, member, envelope⟩ := List.mem_map.mp retained
  have original : decision.execution.application.config.store aliceBinding.field =
      some (.success decision.bit) := decision.bound
  have afterBound := (LateOpeningRuntimeService.runtime.reactiveStoreInvariant
    leaks aliceBinding.field (.success decision.bit)).respond decision.execution alice
      ⟨some submission⟩ original
  have bound := (ReactiveApplication.Invariant.policyInvariant app
    (LateOpeningRuntimeService.runtime.reactiveStoreInvariant leaks aliceBinding.field
      (.success decision.bit)) players).runRounds
        (LateOpeningRuntimeService.scheduler weight nonnegative) 22 _ execution afterBound reached
  have upper := LateOpeningRuntimeAliceOpeningAudit.nongenuine_envelope_utility_bound
    rewardNonnegative forfeitNonnegative deposit depositNonnegative weight nonnegative
      ⟨0, none, execution⟩ trace ⟨rfl, rfl⟩ decision.bit bound actual member
        (by rw [envelope]; rfl) (by rw [envelope]; exact nongenuine)
  exact upper

end Vegas.Examples.LateOpeningRuntimeAliceFirstPacket
