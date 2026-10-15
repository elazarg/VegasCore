/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseNativeConsistency
import Interaction.ReactiveHistory
import Interaction.ReactiveRecordedResponse

/-! # Local policy matching propagates native recall consistency -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseNativeProjection

open Interaction EventGraph GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (plan : RuntimePhasePlan graph)

local notation "P" => phaseApplication runtime leaks
local notation "N" => runtime.reactiveApplication (nativeLeaks leaks plan)

/-- Agreement need only be proved while both complete recalls are consistent.
Actual-history induction supplies that premise at every earlier callback; no
native consistency assumption is imposed on the final history. -/
theorem nativePolicies_consistent_of_local_agreement (bounds : MessageBounds graph)
    (inputs : PMF graph.Inputs) (horizon : Nat) (scheduler : (P).Scheduler)
    (players : Player → (P).Policy) (nativePlayers : Player → (N).Policy)
    (agreement : ∀ (current : (P).Control)
      (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current)),
      current.execution.application.current.excluded = ∅ →
      (∀ who, (players who).Consistent (current.execution.recall who)) →
      (∀ who, (nativePlayers who).Consistent
        ((execution runtime leaks plan current.execution).recall who)) →
      ∀ who, current.actor = some who → nativePlayers who
          ((execution runtime leaks plan current.execution).recall who)
          ((execution runtime leaks plan current.execution).observe N who) =
        nativePolicy runtime leaks plan (players who)
          ((execution runtime leaks plan current.execution).recall who)
          ((execution runtime leaks plan current.execution).observe N who))
    {current : (P).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ who, (players who).Consistent (current.execution.recall who)) :
    ∀ who, (nativePlayers who).Consistent
      ((execution runtime leaks plan current.execution).recall who) := by
  have result : ∀ {state}
      (history : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace state),
      ∀ final : (P).Control, state = some final →
        final.execution.application.current.excluded = ∅ →
        (∀ who, (players who).Consistent (final.execution.recall who)) →
        ∀ who, (nativePlayers who).Consistent
          ((execution runtime leaks plan final.execution).recall who) := by
    intro state history
    induction history with
    | start => intro final impossible; cases impossible
    | @extend before after prior joint legal reached ih =>
        intro final finalEq finalClear faithful
        subst after
        change some final ∈ ((P).transition (inputs.map (PhaseRuntimeState.initial plan))
          horizon scheduler before joint).support at reached
        cases before with
        | none =>
            obtain ⟨initial, _supported, same⟩ := PMF.support_map .. ▸ reached
            cases Option.some.inj same
            exact fun _ => .nil
        | some previous =>
            have priorClear : previous.execution.application.current.excluded = ∅ :=
              Finset.subset_empty.mp (finalClear ▸
                (phaseApplication_exclusion_monotone runtime leaks).transition
                  (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
                  previous final joint reached)
            have priorFaithful : ∀ who,
                (players who).Consistent (previous.execution.recall who) := by
              obtain ⟨next, same, past⟩ := (P).transition_recall_prefix
                (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler
                  previous (some final) joint reached
              cases Option.some.inj same
              intro who
              obtain ⟨tail, retained⟩ := past who
              have valid := faithful who
              rw [← retained] at valid
              exact valid.of_append
            have nativeFaithful := ih previous rfl priorClear priorFaithful
            have kernels := agreement previous prior priorClear priorFaithful nativeFaithful
            rcases previous with ⟨remaining, actor, original⟩
            cases actor with
            | some who =>
                have available := legal.2 who
                cases chosen : joint who with
                | none =>
                    rw [chosen] at available
                    exact False.elim (available rfl)
                | some response =>
                    rw [chosen] at available
                    simp only [ReactiveApplication.transition, chosen, Option.getD_some] at reached
                    cases Option.some.inj ((PMF.mem_support_pure_iff _ _).mp reached)
                    obtain ⟨emitted, recalled⟩ := (P).respond_recall_entry original who response
                    have sampled := faithful who
                    rw [recalled] at sampled
                    have supported := ((players who).consistent_snoc_iff _ _).mp sampled |>.2
                    have nativeSupported : action runtime leaks plan response ∈
                        (nativePlayers who ((execution runtime leaks plan original).recall who)
                          ((execution runtime leaks plan original).observe N who)).support := by
                      rw [kernels who rfl, nativePolicy_at_clear runtime leaks plan bounds inputs
                        horizon scheduler prior priorClear who]
                      exact (PMF.mem_support_map_iff _ _ _).mpr ⟨response, supported, rfl⟩
                    have transported := ((N).consistentRecall_policyInvariant nativePlayers).respond
                      (execution runtime leaks plan original) who
                      (action runtime leaks plan response) nativeFaithful nativeSupported
                    rw [respond_of_onePacket runtime leaks plan bounds original
                      (PhaseCount.countRecall_history runtime leaks
                        ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ horizon
                          scheduler prior)) who response available.2]
                    exact transported
            | none =>
                cases remaining with
                | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
                | succ remaining =>
                    obtain ⟨command, _selected, moved⟩ :=
                      Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                    obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ moved
                    cases Option.some.inj same
                    intro who
                    change (nativePlayers who).Consistent
                      (((next.recall who).map (playerEntry runtime leaks plan)))
                    rw [(P).environmentStep_recall original next command supported]
                    exact nativeFaithful who
  exact result trace current rfl clear consistent

end Vegas.EventGraphRuntime.PhaseNativeProjection
