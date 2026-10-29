/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionEvidence

/-! # Public failure owners in native execution -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- Owners of completed public failures, enumerated by the finite event set. -/
def State.failureOwners (state : State graph) : Finset Player := by
  classical
  exact Finset.univ.biUnion fun event =>
    if state.PublicFailure event then (graph.actor? event).toFinset else ∅

/-- Public failure labels require no finite-player hypothesis. -/
theorem State.mem_failureOwners (state : State graph) (owner : Player) :
    owner ∈ state.failureOwners ↔
      ∃ event, graph.actor? event = some owner ∧ state.PublicFailure event := by
  classical
  simp only [State.failureOwners, Finset.mem_biUnion, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨event, member⟩
    by_cases failed : state.PublicFailure event
    · rw [ite_eq_left failed] at member
      exact ⟨event, by simpa using member, failed⟩
    · rw [ite_eq_right failed] at member
      exact (Finset.notMem_empty _ member).elim
  · rintro ⟨event, acting, failed⟩
    refine ⟨event, ?_⟩
    rw [ite_eq_left failed]
    simpa using acting

/-- The native failure readout equals the authoritative graph default set. -/
theorem ExclusionEvidence.failureOwners_eq {state : State graph}
    (valid : ExclusionEvidence 0 ∅ state) : state.failureOwners = state.config.defaulted := by
  ext owner
  exact (state.mem_failureOwners owner).trans (valid.defaulted_zero owner).symm

/-- Initialized native histories identify failure owners with graph default membership. -/
theorem ExclusionEvidence.history_failureOwners_eq (runtime : EventGraphRuntime graph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))
    (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (runtime.reactiveApplication leaks).Scheduler)
    {state : (runtime.reactiveApplication leaks).ProtocolState}
    (trace : ((runtime.reactiveApplication leaks).protocol (inputs.map State.initial)
      horizon scheduler).Trace state) :
    ReactiveApplication.stateInvariant
      (fun native : State graph => native.failureOwners = native.config.defaulted) state := by
  have valid := ExclusionEvidence.history runtime leaks inputs horizon scheduler trace
  cases state with
  | none => trivial
  | some control => exact valid.failureOwners_eq

end Vegas.EventGraphRuntime
