/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapTransition
import Vegas.Pending.PhaseSwapInformation
import GameTheoryExtensions.Protocol.StateSymmetry

/-! # Actual counted phase histories under guarded hidden-value replay -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- The operational native guard at an initialized control; setup has no reads. -/
def PhaseSwapGuardState (swap : HiddenSwap graph) (allowed : Set graph.Inputs) :
    (phaseApplication runtime leaks).ProtocolState → Prop
  | none => True
  | some control => PhaseSwapGuard runtime leaks swap allowed control.execution

namespace HiddenSwap

variable (swap : HiddenSwap graph) {allowed : Set graph.Inputs}

theorem phaseControl_involutive :
    Function.Involutive (swap.phaseControl (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨remaining, actor, execution⟩
  change (⟨remaining, actor, swap.phaseExecution (swap.phaseExecution execution)⟩ :
    (phaseApplication runtime leaks).Control) = _
  rw [swap.phaseExecution_involutive]

theorem phaseProtocolState_involutive :
    Function.Involutive (swap.phaseProtocolState (runtime := runtime) (leaks := leaks)) := by
  intro state
  cases state with
  | none => rfl
  | some control => exact congrArg some (swap.phaseControl_involutive control)

theorem phaseJoint_involutive :
    Function.Involutive (swap.phaseJoint (runtime := runtime) (leaks := leaks)) := by
  intro joint
  funext who
  simp only [phaseJoint, Option.map_map]
  cases joint who with
  | none => rfl
  | some response => exact congrArg some (swap.phaseAction_involutive response)

/-- Every primitive read condition is preserved by applying its own swap. -/
theorem phaseSwapGuard_map (current : (phaseApplication runtime leaks).Execution)
    (allowedClosed : ∀ inputs ∈ allowed,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈ allowed)
    (valid : PhaseSwapGuard runtime leaks swap allowed current) :
    PhaseSwapGuard runtime leaks swap allowed (swap.phaseExecution current) := by
  refine ⟨valid.clear, allowedClosed _ valid.inputs, valid.compatible, valid.completed,
    valid.active, ?_⟩
  intro who entry member submission transmitted
  change entry ∈ (current.recall who).map swap.phaseEntry at member
  obtain ⟨original, recorded, rfl⟩ := List.mem_map.mp member
  change original.action.transmission.map (WitnessedSubmission.swap swap) = some submission
    at transmitted
  cases chosen : original.action.transmission with
  | none => rw [chosen] at transmitted; cases transmitted
  | some material =>
      rw [chosen] at transmitted
      cases Option.some.inj transmitted
      exact valid.requests who original recorded material chosen

end HiddenSwap

variable [Fintype Player]

/-- The existing guarded protocol symmetry is instantiated with actual phase
operations. Its guard contains the allowed original input tuple, native read
conditions and fixed requests. No desired observation or probability equality
is assumed. -/
def phaseOnePacketSwapSymmetry (bounds : MessageBounds graph)
    (initial : PMF (phaseApplication runtime leaks).State)
    (initialized : ∀ state ∈ initial.support, ∃ draw, state.Invariant draw) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (swap : HiddenSwap graph)
    (allowed : Set graph.Inputs)
    (initialClosed : ∀ state ∈ initial.support,
      state.current.native.config.inputs ∈ allowed → state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).protocol initial
      horizon scheduler).StateSymmetry where
  map := swap.phaseProtocolState
  act _ := swap.phaseJoint
  Guard := PhaseSwapGuardState swap allowed
  map_init := rfl
  guard_source := by
    intro source target joint prior legal reached guarded
    cases source with
    | none => trivial
    | some before =>
        obtain ⟨after, rfl, _⟩ := (phaseApplication runtime leaks).transition_recall_prefix
          initial horizon scheduler before target joint reached
        exact phaseSwapGuard_of_transition runtime leaks swap allowed initial horizon scheduler
          before after joint reached
            (phaseNativeInvariant_of_initialized_history runtime leaks initial initialized horizon
              scheduler ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial
                horizon scheduler prior)) guarded
  legal := by
    intro source target joint _prior legal reached guarded
    cases source with
    | none =>
        refine ⟨legal.1, fun who => ?_⟩
        have localLegal := legal.2 who
        cases chosen : joint who with
        | none =>
            simp only [HiddenSwap.phaseJoint, chosen, Option.map_none]
            rw [chosen] at localLegal
            exact localLegal
        | some response =>
            simp only [HiddenSwap.phaseJoint, chosen, Option.map_some]
            rw [chosen] at localLegal
            exact absurd localLegal.1 (by intro impossible; cases impossible)
    | some before =>
        obtain ⟨after, rfl, _⟩ := (phaseApplication runtime leaks).transition_recall_prefix
          initial horizon scheduler before target joint reached
        rcases before with ⟨remaining, actor, current⟩
        refine ⟨legal.1, fun who => ?_⟩
        have localLegal := legal.2 who
        cases chosen : joint who with
        | none =>
            simp only [HiddenSwap.phaseJoint, chosen, Option.map_none]
            rw [chosen] at localLegal
            exact localLegal
        | some response =>
            simp only [HiddenSwap.phaseJoint, chosen, Option.map_some]
            rw [chosen] at localLegal
            obtain ⟨active, available⟩ := localLegal
            refine ⟨active, ?_⟩
            have actorEq : actor = some who := active
            subst actorEq
            cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
            have fixed := swap.phaseRequestFixed_of_respond current who _ guarded
            change ∀ submission, ((joint who).getD ⟨none⟩).transmission = some submission →
              submission.evidence.FixedBy swap at fixed
            rw [chosen] at fixed
            change swap.phaseAction response ∈ PhaseCount.onePacketActions runtime leaks bounds
              who ((current.recall who).map swap.phaseEntry)
                ((swap.phaseExecution current).observe (phaseApplication runtime leaks) who)
            rw [swap.observe_phaseExecution]
            exact PhaseCount.swap_mem_onePacketActions bounds swap who _ _ rfl response
              available fixed bounded
  realized := by
    intro source target joint prior _legal reached guarded
    apply swap.phaseTransition_swap initial initialClosed horizon scheduler source target joint
      reached expiry
    · intro control same
      cases same
      exact phaseNativeInvariant_of_initialized_history runtime leaks initial initialized horizon
        scheduler ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace initial
          horizon scheduler prior)
    · intro control same
      cases same
      exact guarded

/-- This actual history map is an involution on its primitive guarded domain. -/
theorem phaseOnePacketSwapSymmetry_involutive (bounds : MessageBounds graph)
    (initial : PMF (phaseApplication runtime leaks).State)
    (initialized : ∀ state ∈ initial.support, ∃ draw, state.Invariant draw) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (swap : HiddenSwap graph)
    (allowed : Set graph.Inputs)
    (initialClosed : ∀ state ∈ initial.support,
      state.current.native.config.inputs ∈ allowed → state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (allowedClosed : ∀ inputs ∈ allowed,
      (fun input => swap.values.value (.inl input) (inputs input)) ∈ allowed) :
    (phaseOnePacketSwapSymmetry bounds initial initialized horizon scheduler swap
      allowed initialClosed bounded expiry).Involutive where
  map_map state _ := swap.phaseProtocolState_involutive state
  guard_map state valid := by
    cases state with
    | none => trivial
    | some control => exact swap.phaseSwapGuard_map control.execution allowedClosed valid
  act_act _prior _legal _reached _guarded := swap.phaseJoint_involutive _

/-- The map fixes the complete actual information fiber of an observer whose
visible fields, owned actions and candidate handles are fixed by the swap. -/
theorem phase_infoOf_mapTrace_of_fixed (bounds : MessageBounds graph)
    (initial : PMF (phaseApplication runtime leaks).State)
    (initialized : ∀ state ∈ initial.support, ∃ draw, state.Invariant draw) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (swap : HiddenSwap graph)
    (allowed : Set graph.Inputs)
    (initialClosed : ∀ state ∈ initial.support,
      state.current.native.config.inputs ∈ allowed → state.swap swap ∈ initial.support)
    (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
    (expiry : ∀ event, swap.values.ExpiryFixed event) (who : Player)
    (fields : ∀ field, graph.fieldVisibleTo who field → swap.values.value field = id)
    (actions : ∀ event, graph.actor? event = some who → swap.values.action event = id)
    (handles : ∀ slot, swap.raw (who, slot) = id)
    (history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      initial horizon scheduler).History)
    (guarded : PhaseSwapGuardState swap allowed history.state) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial
      horizon scheduler).infoOf who ((phaseOnePacketSwapSymmetry bounds initial initialized horizon
          scheduler swap
          allowed initialClosed bounded expiry).mapTrace history.trace guarded) =
      ((PhaseCount.onePacketMenu runtime leaks bounds).information initial
      horizon scheduler).infoOf who history.trace := by
  have mapped :
      ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).infoOf
        who ((phaseOnePacketSwapSymmetry bounds initial initialized horizon scheduler swap allowed
          initialClosed bounded expiry).mapTrace history.trace guarded) =
        (phaseApplication runtime leaks).observe who (swap.phaseProtocolState history.state) :=
    (PhaseCount.onePacketMenu runtime leaks bounds).info initial horizon scheduler who _
  have original :
      ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon scheduler).infoOf
        who history.trace = (phaseApplication runtime leaks).observe who history.state :=
    (PhaseCount.onePacketMenu runtime leaks bounds).info initial horizon scheduler who _
  have same : (phaseApplication runtime leaks).observe who (swap.phaseProtocolState history.state) =
      (phaseApplication runtime leaks).observe who history.state := by
    rcases history with ⟨state, trace⟩
    cases state with
    | none => rfl
    | some control =>
        change (if control.actor = some who then
          some ((swap.phaseExecution control.execution).recall who,
            (swap.phaseExecution control.execution).observe (phaseApplication runtime leaks) who)
          else none) = _
        rw [swap.phaseInput_eq_of_fixed bounds initial horizon scheduler control trace
          who fields actions handles]
        rfl
  exact mapped.trans (same.trans original.symm)

end Vegas.EventGraphRuntime
