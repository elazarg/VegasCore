/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationCursor
import Interaction.ReactiveResponseKernel

/-! # Reaching later decision histories in the actual native protocol

The scheduler cursor and active player follow the fixed service calendar even
when packet contents, passive observations, and all player responses vary.
This projection is used only to locate histories within a behavioral run.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability

variable {observation : MessageNetwork.ObservationRule Player (WitnessedPacket nativeGraph)}
open GameTheory.Protocol

def nativePosition (state : (serviceApp observation).ProtocolState) : Option (Nat × Option Player ×
  Nat) :=
  state.map (fun control =>
    (control.remaining, control.actor, control.execution.environmentRecall.length))

def nativeAdvancePosition : Option (Nat × Option Player × Nat) →
    Option (Nat × Option Player × Nat)
  | none => some (nativeHorizon, none, 0)
  | some (remaining, some _, cursor) => some (remaining, none, cursor)
  | some (0, none, cursor) => some (0, none, cursor)
  | some (remaining + 1, none, cursor) =>
      some (remaining, (nativePlan[cursor]?).bind nativeInstructionPlayer, cursor + 1)

theorem native_controlStep_position (players : Player → (serviceApp observation).Policy)
    (state next : (serviceApp observation).ProtocolState)
    (supported : next ∈ ((serviceApp observation).controlStep (FinDist.pure nativeInitial)
      nativeHorizon
      (serviceScheduler observation) players state).support) :
    nativePosition next = nativeAdvancePosition (nativePosition state) := by
  cases state with
  | none =>
      simp only [ReactiveApplication.controlStep, ReactiveApplication.actor,
        Option.bind_none, ReactiveApplication.transition, FinDist.map_pure] at supported
      cases FinDist.mem_support_pure.mp supported
      rfl
  | some control =>
      rcases control with ⟨remaining, actor, execution⟩
      cases actor with
      | some who =>
          obtain ⟨response, _, reached⟩ :=
            Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
          cases FinDist.mem_support_pure.mp reached
          simp only [nativePosition, Option.map_some, nativeAdvancePosition]
          rw [(serviceApp observation).respond_environmentRecall]
      | none =>
          cases remaining with
          | zero => cases FinDist.mem_support_pure.mp supported; rfl
          | succ remaining =>
              obtain ⟨command, commandMem, stepped⟩ :=
                Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
              obtain ⟨result, resultMem, rfl⟩ := FinDist.support_map .. ▸ stepped
              have cursor : result.environmentRecall.length =
                  execution.environmentRecall.length + 1 := by
                obtain ⟨updated, _, rfl⟩ := FinDist.support_map .. ▸ resultMem
                simp
              have actor : command.actor? (serviceApp observation) =
                  (nativePlan[execution.environmentRecall.length]?).bind
                    nativeInstructionPlayer := by
                cases found : nativePlan[execution.environmentRecall.length]? with
                | none =>
                    simp only [serviceScheduler, found, FinDist.mem_support_pure] at commandMem
                    subst command
                    rfl
                | some instruction =>
                    simp only [serviceScheduler, found] at commandMem
                    exact native_instruction_actor instruction _ _ command commandMem
              simp only [nativePosition, Option.map_some, nativeAdvancePosition, cursor, actor]

theorem native_iterate_position (players : Player → (serviceApp observation).Policy) (fuel : Nat)
    (state next : (serviceApp observation).ProtocolState)
    (supported : next ∈ ((fun law => law.bind ((serviceApp observation).controlStep
      (FinDist.pure nativeInitial) nativeHorizon (serviceScheduler observation) players))^[fuel]
        (FinDist.pure state)).support) :
    nativePosition next = nativeAdvancePosition^[fuel] (nativePosition state) := by
  induction fuel generalizing next with
  | zero => cases FinDist.mem_support_pure.mp supported; rfl
  | succ fuel ih =>
      rw [Function.iterate_succ_apply'] at supported
      obtain ⟨middle, middleMem, nextMem⟩ :=
        Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
      rw [native_controlStep_position players middle next nextMem, ih middle middleMem,
        Function.iterate_succ_apply']

theorem native_behavioral_position (profile : ∀ who, (serviceModel observation).BehavioralPolicy
  who)
    (fuel : Nat) (history final : (serviceArena observation).History)
    (supported : final ∈ ((serviceModel observation).runBehavioralFrom profile fuel
      history).support) :
    nativePosition final.state = nativeAdvancePosition^[fuel] (nativePosition history.state) := by
  apply native_iterate_position
    ((serviceMenu observation).decodeProfile (FinDist.pure nativeInitial) nativeHorizon
      (serviceScheduler observation) profile)
    fuel history.state final.state
  have law := (serviceMenu observation).run_map_controlStep (FinDist.pure nativeInitial)
    nativeHorizon
    (serviceScheduler observation) profile fuel history
  apply (congrArg (fun law : FinDist (serviceApp observation).ProtocolState => final.state ∈
    law.support) law).mp
  rw [FinDist.support_map]
  exact ⟨final, supported, rfl⟩

theorem native_grant_of_decision_cursor (event : nativeGraph.EventId)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (active : control.actor = some (nativeOwner event))
    (position : control.execution.environmentRecall.length =
      (nativeBeforeResponse event).length + 1) :
    control.execution.application.serviceGrant = some event := by
  obtain ⟨_, prior, priorMem, activated⟩ :=
    native_decision_predecessor event control trace active position
  rw [native_activation_grant prior control.execution (nativeOwner event) activated]
  exact native_response_prefix_grant (serviceMenu observation).uniformResponses event prior priorMem

private theorem next_position (event next : nativeGraph.EventId)
    (consecutive : next.val = event.val + 1) :
    nativeAdvancePosition^[nativeRuntime.deadline event + 5]
        (some (nativeHorizon - ((nativeBeforeResponse event).length + 1),
          some (nativeOwner event), (nativeBeforeResponse event).length + 1)) =
      some (nativeHorizon - ((nativeBeforeResponse next).length + 1),
        some (nativeOwner next), (nativeBeforeResponse next).length + 1) := by
  fin_cases event <;> fin_cases next <;> cases consecutive <;> decide

/-- The later decision is an actual supported canonical history. No response
or packet-disclosure behavior is fixed by this timing statement. -/
theorem native_next_decision (profile : ∀ who, (serviceModel observation).BehavioralPolicy who)
    (event next : nativeGraph.EventId) (consecutive : next.val = event.val + 1)
    (control : (serviceApp observation).Control) (trace : (serviceArena observation).Trace (some
      control))
    (active : control.actor = some (nativeOwner event))
    (granted : control.execution.application.serviceGrant = some event)
    (later : (serviceArena observation).History)
    (supported : later ∈ ((serviceModel observation).runBehavioralFrom profile
      (nativeRuntime.deadline event + 5) ⟨some control, trace⟩).support) :
    ∃ result, later.state = some result ∧ result.actor = some (nativeOwner next) ∧
      result.execution.application.serviceGrant = some next := by
  have position := (native_decision_cursor event control trace _ active granted).2
  have accounted := (native_decision_predecessor event control trace active position).1
  have remaining : control.remaining =
      nativeHorizon - ((nativeBeforeResponse event).length + 1) := by omega
  have computed := native_behavioral_position profile _ ⟨some control, trace⟩ later supported
  change nativePosition later.state = nativeAdvancePosition^[nativeRuntime.deadline event + 5]
    (some (control.remaining, control.actor, control.execution.environmentRecall.length))
    at computed
  rw [remaining, active, position, next_position event next consecutive] at computed
  rcases later with ⟨state, laterTrace⟩
  cases state with
  | none => cases computed
  | some result =>
      have fields := Option.some.inj computed
      have actor := congrArg (fun value : Nat × Option Player × Nat => value.2.1) fields
      have cursor := congrArg (fun value : Nat × Option Player × Nat => value.2.2) fields
      exact ⟨result, rfl, actor,
        native_grant_of_decision_cursor next result laterTrace actor cursor⟩

end VegasTests.SelectiveAssociation
