/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationCursor
import Interaction.ReactiveResponseEvaluation

/-! # Reserved inclusion and persistent continuation facts

At each native decision the next service instruction includes that owner's
latest packet for the current event. Any invariant established by this actual
inclusion therefore holds through the complete continuation, with every later
response policy unrestricted.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}

theorem native_inclusion_next_instruction (event : nativeGraph.EventId) :
    nativePlan[(nativeBeforeResponse event).length + 1]? =
      some (.includeLatest event (nativeOwner event)) := by
  fin_cases event <;> rfl

theorem native_reserved_finish (players : Player → (serviceApp observation).Policy)
    (control : (serviceApp observation).Control)
    (trace : (serviceArena observation).Trace (some control))
    (event : nativeGraph.EventId) (response : (serviceApp observation).Action)
    (predicate : State nativeGraph → Prop)
    (invariant : (serviceApp observation).Invariant predicate)
    (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event)
    (chooses : players (nativeOwner event) (control.execution.recall (nativeOwner event))
      (control.execution.observe (serviceApp observation) (nativeOwner event)) =
        FinDist.pure response)
    (included : ∀ middle ∈ (nativeRuntime.interactionStep observation players
      (serviceNetwork observation) (.includeLatest event (nativeOwner event))
      (control.execution.respond (serviceApp observation) (nativeOwner event) response)).support,
        predicate middle.application)
    (result : (serviceApp observation).ProtocolState)
    (supported : result ∈ ((serviceApp observation).finish (FinDist.pure nativeInitial)
      nativeHorizon (serviceScheduler observation) players (some control)).support) :
    ∃ final, result = some final ∧ predicate final.execution.application := by
  have position := (native_decision_cursor event control trace _ active granted).2
  obtain ⟨remainingAccount, _⟩ :=
    native_decision_predecessor event control trace active position
  have positive : 0 < control.remaining := by
    have beforeEnd : (nativeBeforeResponse event).length + 1 < nativeHorizon := by
      fin_cases event <;> decide
    omega
  obtain ⟨remaining, remainingEq⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt positive)
  let responded := control.execution.respond (serviceApp observation) (nativeOwner event) response
  have nextRound : (serviceApp observation).round (serviceScheduler observation) players responded =
      nativeRuntime.interactionStep observation players (serviceNetwork observation)
        (.includeLatest event (nativeOwner event)) responded := by
    have cursor : responded.environmentRecall.length =
        (nativeBeforeResponse event).length + 1 := by
      rw [(serviceApp observation).respond_environmentRecall]
      exact position
    simp only [ReactiveApplication.round, serviceScheduler, cursor,
      native_inclusion_next_instruction, interactionStep]
  simp only [ReactiveApplication.finish, active, ReactiveApplication.resume,
    ReactiveApplication.invoke, chooses, FinDist.map_pure, FinDist.pure_bind,
    remainingEq, ReactiveApplication.runRounds] at supported
  obtain ⟨final, finalMem, rfl⟩ := FinDist.support_map .. ▸ supported
  obtain ⟨middle, middleMem, finalMem⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ finalMem)
  change middle ∈ ((serviceApp observation).round (serviceScheduler observation) players
    responded).support at middleMem
  rw [nextRound] at middleMem
  refine ⟨_, rfl, ?_⟩
  exact (ReactiveApplication.Invariant.policyInvariant (serviceApp observation)
    invariant players).runRounds (serviceScheduler observation) remaining middle final
      (included middle middleMem) finalMem

end VegasTests.SelectiveAssociation
