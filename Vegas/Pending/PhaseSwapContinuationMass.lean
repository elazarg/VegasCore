/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapCallback
import Vegas.Pending.PhaseSwapTransitionMass
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay

/-! # A common actual nature coefficient for hidden-swap continuations -/

noncomputable section

namespace Vegas.EventGraphRuntime.HiddenSwap

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
  (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "app" => phaseApplication runtime leaks
local notation "initial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler
local notation "N" => ReactiveApplication.ResponseMenu.information
  (PhaseCount.onePacketMenu runtime leaks bounds) initial horizon scheduler

private theorem control_of_prefix (entry : (app).Control)
    (entryTrace : (E).Trace (some entry)) {state : (app).ProtocolState}
    (trace : (E).Trace state) (isPrefix : TracePrefix entryTrace trace) :
    ∃ control, state = some control := by
  have retained : ∀ {state} {trace : (E).Trace state}, TracePrefix entryTrace trace →
      ∃ control, state = some control := by
    intro state trace retainedPrefix
    induction retainedPrefix with
    | refl => exact ⟨entry, rfl⟩
    | @extend source target prior earlier joint legal realized ih =>
        obtain ⟨before, rfl⟩ := ih
        obtain ⟨after, same, _recalled⟩ := (app).transition_recall_prefix initial horizon scheduler
          before target joint realized
        exact ⟨after, same⟩
  exact retained isPrefix

variable (swap : HiddenSwap graph)
  (bounded : ∀ handle raw, raw ∈ bounds.values → swap.raw handle raw ∈ bounds.values)
  (expiry : ∀ event, swap.values.ExpiryFixed event)

local notation "S" => phaseOnePacketSwapSymmetry bounds initial
  (phase_initial_support_invariant plan inputs) horizon scheduler swap
    (phaseSwapAllowed swap initial) (phase_initialClosed_swapAllowed swap plan inputs)
      bounded expiry

private theorem mapped_prefix_mass (entry : (app).Control)
    (entryTrace : (E).Trace (some entry)) {state : (app).ProtocolState}
    (finalTrace : (E).Trace state)
    (isPrefix : TracePrefix entryTrace finalTrace)
    (entryGuard : (S).Guard (some entry)) (finalGuard : (S).Guard state) :
    TracePrefix ((S).mapTrace entryTrace entryGuard) ((S).mapTrace finalTrace finalGuard) ∧
      ((S).mapTrace finalTrace finalGuard).transitionMass * entryTrace.transitionMass =
        finalTrace.transitionMass * ((S).mapTrace entryTrace entryGuard).transitionMass := by
  have retained : ∀ {state} {trace : (E).Trace state}, TracePrefix entryTrace trace →
      ∀ guarded : (S).Guard state,
        TracePrefix ((S).mapTrace entryTrace entryGuard) ((S).mapTrace trace guarded) ∧
          ((S).mapTrace trace guarded).transitionMass * entryTrace.transitionMass =
            trace.transitionMass * ((S).mapTrace entryTrace entryGuard).transitionMass := by
    intro state trace retainedPrefix
    induction retainedPrefix with
    | refl =>
        intro finalGuard
        exact ⟨.refl, by ring⟩
    | @extend source target prior earlier joint legal realized ih =>
        intro finalGuard
        have priorGuard := (S).guard_source prior legal realized finalGuard
        obtain ⟨mappedPrefix, mass⟩ := ih priorGuard
        obtain ⟨before, rfl⟩ := control_of_prefix bounds plan inputs horizon scheduler entry
          entryTrace prior earlier
        obtain ⟨after, rfl, _recalled⟩ := (app).transition_recall_prefix initial horizon scheduler
          before target joint realized
        have native := phaseNativeInvariant_history runtime leaks plan inputs horizon scheduler
          ((menu).toRawTrace initial horizon scheduler prior)
        have stepMass := swap.phaseTransition_apply_swap initial horizon scheduler before after
          joint realized native finalGuard expiry
        refine ⟨?_, ?_⟩
        · simpa only [StateSymmetry.mapTrace_extend] using
            TracePrefix.extend mappedPrefix ((S).act _ joint)
              ((S).legal prior legal realized finalGuard)
              ((S).realized prior legal realized finalGuard)
        · rw [StateSymmetry.mapTrace_extend, Trace.transitionMass_extend,
            Trace.transitionMass_extend]
          change (((S).mapTrace prior priorGuard).transitionMass *
            ((app).transition initial horizon scheduler (some (swap.phaseControl before))
              (swap.phaseJoint joint) (some (swap.phaseControl after))).toReal) *
                entryTrace.transitionMass = _
          rw [stepMass]
          change (_ * _ : ℝ) * entryTrace.transitionMass =
            (prior.transitionMass *
              ((app).transition initial horizon scheduler
                (some before) joint (some after)).toReal) *
                ((S).mapTrace entryTrace entryGuard).transitionMass
          simpa only [mul_assoc, mul_left_comm, mul_comm] using
            congrArg (fun value : ℝ => value *
              ((app).transition initial horizon scheduler (some before) joint (some after)).toReal)
                mass
  exact retained isPrefix finalGuard

/-- After the actual initial draw, the native continuation and its guarded
hidden-swap image have one common strictly positive nature coefficient for
ALL behavioral profiles. Each side retains its original full entry history. -/
theorem exists_phase_continuation_common_factor (entry final : (app).Control)
    (entryTrace : (E).Trace (some entry)) (finalTrace : (E).Trace (some final))
    (isPrefix : TracePrefix entryTrace finalTrace)
    (guarded : PhaseSwapGuard runtime leaks swap (phaseSwapAllowed swap initial) final.execution) :
    let entryGuard := swap.phaseSwapGuard_of_tracePrefix bounds plan inputs horizon scheduler
      entry final entryTrace finalTrace isPrefix guarded bounded expiry
    let mappedEntry := (S).mapTrace entryTrace entryGuard
    let mappedFinal := (S).mapTrace finalTrace guarded
    ∃ (records mappedRecords : ∀ who, List ((N).InfoState who × (E).Action who)) (chance : ℝ),
      0 < chance ∧
      (∀ who, (N).ownPlay who finalTrace = records who ++ (N).ownPlay who entryTrace) ∧
      (∀ who, (N).ownPlay who mappedFinal =
        mappedRecords who ++ (N).ownPlay who mappedEntry) ∧
      (∀ profile : ∀ who, (N).BehavioralPolicy who,
        (((N).runBehavioralFrom profile (finalTrace.length - entryTrace.length)
          ⟨some entry, entryTrace⟩) ⟨some final, finalTrace⟩).toReal =
            chance * ∏ who, (N).ownPlayReachProbability (profile who) (records who)) ∧
      (∀ profile : ∀ who, (N).BehavioralPolicy who,
        (((N).runBehavioralFrom profile (mappedFinal.length - mappedEntry.length)
          ⟨(S).map (some entry), mappedEntry⟩) ⟨(S).map (some final), mappedFinal⟩).toReal =
            chance * ∏ who, (N).ownPlayReachProbability (profile who) (mappedRecords who)) := by
  intro entryGuard mappedEntry mappedFinal
  obtain ⟨mappedPrefix, crossMass⟩ := mapped_prefix_mass bounds plan inputs horizon scheduler swap
    bounded expiry entry entryTrace finalTrace isPrefix entryGuard guarded
  obtain ⟨records, recorded, _provenance, chance, _nonnegative, mass, factor⟩ :=
    (N).exists_continuation_ownPlay_factor entryTrace finalTrace isPrefix
  obtain ⟨mappedRecords, mappedRecorded, _mappedProvenance, mappedChance, _mappedNonnegative,
      mappedMass, mappedFactor⟩ :=
    (N).exists_continuation_ownPlay_factor mappedEntry mappedFinal mappedPrefix
  have chanceEq : chance = mappedChance := by
    have first := (eq_div_iff (ne_of_gt entryTrace.transitionMass_pos)).mpr mass
    have second := (eq_div_iff (ne_of_gt mappedEntry.transitionMass_pos)).mpr mappedMass
    rw [first, second]
    exact (div_eq_div_iff (ne_of_gt entryTrace.transitionMass_pos)
      (ne_of_gt mappedEntry.transitionMass_pos)).mpr crossMass.symm
  have positive : 0 < chance := by
    have productPositive : 0 < chance * entryTrace.transitionMass := by
      rw [mass]
      exact finalTrace.transitionMass_pos
    exact (mul_pos_iff_of_pos_right entryTrace.transitionMass_pos).mp productPositive
  refine ⟨records, mappedRecords, chance, positive, recorded, mappedRecorded, factor, ?_⟩
  intro profile
  rw [chanceEq]
  exact mappedFactor profile

end Vegas.EventGraphRuntime.HiddenSwap
