/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseReactiveValueSwap
import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingResponseWitness
import Vegas.Pending.PhaseSwapInitialLaw

/-! # Actual nonbinding responses are fixed by hidden preparation swaps -/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- A guarded endpoint of a genuine initialized execution supplies the same
input-restricted hidden-swap guard at every earlier actual callback. -/
theorem phaseSwapGuard_of_tracePrefix (swap : HiddenSwap graph)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)
    (before after : (phaseApplication runtime leaks).Control)
    (beforeTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some before))
    (afterTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some after))
    (isPrefix : TracePrefix beforeTrace afterTrace)
    (guarded : PhaseSwapGuard runtime leaks swap
      (phaseSwapAllowed swap (inputs.map (PhaseRuntimeState.initial plan))) after.execution)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    PhaseSwapGuard runtime leaks swap
      (phaseSwapAllowed swap (inputs.map (PhaseRuntimeState.initial plan))) before.execution := by
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let protocol := (PhaseCount.onePacketMenu runtime leaks bounds).protocol initial horizon scheduler
  let symmetry := phaseOnePacketSwapSymmetry bounds initial
    (phase_initial_support_invariant plan inputs) horizon scheduler swap
      (phaseSwapAllowed swap initial) (phase_initialClosed_swapAllowed swap plan inputs)
        bounded expiry
  have retained : ∀ {state} {trace : protocol.Trace state}, TracePrefix beforeTrace trace →
      symmetry.Guard state → symmetry.Guard (some before) := by
    intro state trace retainedPrefix
    induction retainedPrefix with
    | refl => exact id
    | @extend source target prior _earlier joint legal realized ih =>
        exact fun valid => ih (symmetry.guard_source prior legal realized valid)
  exact retained isPrefix guarded

/-- A genuine counted callback without an unsent binding request can send
only an opening or silence. Swapping hidden preparation fixes its exact action. -/
theorem phaseAction_eq_of_nonbinding_callback (swap : HiddenSwap graph)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (who : Player)
    (execution : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some who, execution⟩))
    (nonbinding : ¬∃ event payload,
      graph.outputLayout event = .binding who payload ∧
      execution.application.SeedRequest who ⟨execution.application.attempt, event⟩ ∧
      ∀ message ∈ (phaseApplication runtime leaks).outputs (execution.recall who),
        PhaseCount.event? message.payload ≠ some ⟨execution.application.attempt, event⟩)
    (response : (phaseApplication runtime leaks).Action)
    (offered : response ∈ PhaseCount.onePacketActions runtime leaks bounds who
      (execution.recall who) (execution.observe (phaseApplication runtime leaks) who)) :
    swap.phaseAction response = response := by
  rcases response with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material =>
      obtain ⟨⟨attempt, event⟩, request⟩ := PhaseCount.onePacket_request_of_nonsilent runtime
        leaks bounds plan inputs horizon scheduler remaining who execution trace material
          offered
      have address : attempt = execution.application.attempt := request.1
      subst attempt
      cases node : nodeView graph event with
      | bind owner payload outputEq codeEq =>
          have ownerEq : owner = who := Option.some.inj
            (((EventCode.actor_cast outputEq _).symm.trans
              (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
          subst owner
          exact (nonbinding ⟨event, payload, outputEq, request,
            PhaseCount.unsent_of_nonsilent runtime leaks bounds plan ordered inputs horizon
              scheduler remaining who execution trace _ request material offered⟩).elim
      | resolve owner payload field checks outputEq codeEq =>
          have ownerEq : owner = who := Option.some.inj
            (((EventCode.actor_cast outputEq _).symm.trans
              (congrArg EventCode.actor codeEq)).symm.trans request.2.2.2.1)
          subst owner
          obtain ⟨candidate, value, named, _stored, _accepted, _openable⟩ :=
            PhaseCount.onePacket_opening_shape runtime leaks bounds plan ordered inputs horizon
              scheduler remaining who execution trace event payload field checks outputEq codeEq
                node request material offered
          rcases material with ⟨⟨packet, preparation⟩, evidence⟩
          change packet = .opening event candidate ⟨payload, value⟩ at named
          cases named
          rfl
      | sample payload law outputEq codeEq =>
          have noOwner : graph.actor? event = none :=
            (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
          have owned := request.2.2.2.1
          rw [noOwner] at owned
          cases owned

end Vegas.EventGraphRuntime.HiddenSwap
