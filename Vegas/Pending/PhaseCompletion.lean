/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.RuntimePhase
import Vegas.Pending.ExclusionInvariant

/-! # Automatic failure confined to the current source phase

Every drained transition is the native failure completion of an excluded owner.
No event outside the current rank interval is completed by this operation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.RuntimePhase

open EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

variable (phase : RuntimePhase graph)

open Classical in
/-- Bounded deterministic automatic service; no scheduler or owner is queried. -/
def drainFuel (phase : RuntimePhase graph) : Nat → RecoveryState graph → RecoveryState graph
  | 0, state => state
  | fuel + 1, state =>
      if pending : ∃ event, (event ∈ phase.events ∧ state.AutomaticReady event) then
        drainFuel phase fuel (state.completeAutomatic (Classical.choose pending)
          (Classical.choose_spec pending).2)
      else state

/-- Automatic completions form an actual native graph-step path. -/
def AutomaticStep (phase : RuntimePhase graph) (before after : RecoveryState graph) : Prop :=
  ∃ event, ∃ eligible : event ∈ phase.events ∧ before.AutomaticReady event,
    after = before.completeAutomatic event eligible.2

theorem drainFuel_trace (fuel : Nat) (state : RecoveryState graph) :
    Relation.ReflTransGen (AutomaticStep phase) state (drainFuel phase fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        exact (Relation.ReflTransGen.single ⟨_, Classical.choose_spec pending, rfl⟩).trans (ih _)
      · exact .refl

theorem drainFuel_quiescent (fuel : Nat) (state : RecoveryState graph)
    (enough : state.native.config.remaining ≤ fuel) :
    ∀ event, ¬ (event ∈ phase.events ∧ (drainFuel phase fuel state).AutomaticReady event) := by
  induction fuel generalizing state with
  | zero =>
      intro event eligible
      have progress := state.completeAutomatic_progress event eligible.2
      omega
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        apply ih
        have progress := state.completeAutomatic_progress _ (Classical.choose_spec pending).2
        omega
      · rename_i clear
        exact fun event eligible => clear ⟨event, eligible⟩

theorem drainFuel_eq_of_clear (fuel : Nat) (state : RecoveryState graph)
    (clear : ∀ event, ¬ (event ∈ phase.events ∧ state.AutomaticReady event)) :
    drainFuel phase fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel =>
      simp only [drainFuel, show ¬ (∃ event, event ∈ phase.events ∧ state.AutomaticReady event)
        from fun ⟨event, eligible⟩ => clear event eligible, ↓reduceDIte]

def drain (phase : RuntimePhase graph) (state : RecoveryState graph) : RecoveryState graph :=
  drainFuel phase state.native.config.remaining state

theorem drain_quiescent (state : RecoveryState graph) :
    ∀ event, ¬ (event ∈ phase.events ∧ (drain phase state).AutomaticReady event) :=
  drainFuel_quiescent phase _ _ le_rfl

theorem drain_eq_of_clear (state : RecoveryState graph)
    (clear : ∀ event, ¬ (event ∈ phase.events ∧ state.AutomaticReady event)) :
    drain phase state = state :=
  drainFuel_eq_of_clear phase _ _ clear

theorem drainFuel_excluded (fuel : Nat) (state : RecoveryState graph) :
    (drainFuel phase fuel state).excluded = state.excluded := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · exact ih _
      · rfl

theorem drainFuel_tables (fuel : Nat) (state : RecoveryState graph) :
    (drainFuel phase fuel state).native.accepted = state.native.accepted ∧
      (drainFuel phase fuel state).native.candidates = state.native.candidates ∧
      (drainFuel phase fuel state).native.clock = state.native.clock := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨accepted, candidates, clock⟩ := state.native.completeFailure_tables
          (Classical.choose pending) (Classical.choose_spec pending).2.1
        obtain ⟨laterAccepted, laterCandidates, laterClock⟩ := ih
          (state.completeAutomatic (Classical.choose pending) (Classical.choose_spec pending).2)
        exact ⟨laterAccepted.trans accepted, laterCandidates.trans candidates,
          laterClock.trans clock⟩
      · exact ⟨rfl, rfl, rfl⟩

theorem drainFuel_reachable (fuel : Nat) (state : RecoveryState graph) {inputs : graph.Inputs}
    (reachable : state.native.config.Reachable inputs) :
    (drainFuel phase fuel state).native.config.Reachable inputs := by
  induction fuel generalizing state with
  | zero => exact reachable
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨action, realized⟩ := state.completeAutomatic_step (Classical.choose pending)
          (Classical.choose_spec pending).2
        exact ih _ (.step reachable _ (Classical.choose_spec pending).2.1 action _ realized)
      · exact reachable

theorem drain_trace (state : RecoveryState graph) :
    Relation.ReflTransGen (AutomaticStep phase) state (drain phase state) :=
  drainFuel_trace phase _ _

theorem drain_excluded (state : RecoveryState graph) :
    (drain phase state).excluded = state.excluded :=
  drainFuel_excluded phase _ _

theorem drain_tables (state : RecoveryState graph) :
    (drain phase state).native.accepted = state.native.accepted ∧
      (drain phase state).native.candidates = state.native.candidates ∧
      (drain phase state).native.clock = state.native.clock := drainFuel_tables phase _ _

theorem drain_reachable (state : RecoveryState graph) {inputs : graph.Inputs}
    (reachable : state.native.config.Reachable inputs) :
    (drain phase state).native.config.Reachable inputs := drainFuel_reachable phase _ _ reachable


theorem drainFuel_invariant (fuel : Nat) (state : RecoveryState graph) {inputs : graph.Inputs}
    (valid : state.native.Invariant inputs) :
    (drainFuel phase fuel state).native.Invariant inputs := by
  induction fuel generalizing state with
  | zero => exact valid
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨owner, acting, _⟩ := (Classical.choose_spec pending).2.owned
        exact ih _ (State.completeFailure_invariant valid _
          (Classical.choose_spec pending).2.1 acting)
      · exact valid

theorem drain_invariant (state : RecoveryState graph) {inputs : graph.Inputs}
    (valid : state.native.Invariant inputs) : (phase.drain state).native.Invariant inputs :=
  phase.drainFuel_invariant _ _ valid

/-- Phase-local completion cannot advance the semantic frontier beyond its end. -/
theorem drainFuel_within (fuel : Nat) (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high) :
    (phase.drainFuel fuel state).native.config.cut.Within phase.low phase.high := by
  induction fuel generalizing state with
  | zero => exact within
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        apply ih
        obtain ⟨action, supported⟩ := state.completeAutomatic_step
          (Classical.choose pending) (Classical.choose_spec pending).2
        rw [Config.step_cut _ _ _ _ _ supported]
        exact within.complete _ (Classical.choose_spec pending).2.1
          ((phase.mem_events _).mp (Classical.choose_spec pending).1).2
      · exact within

theorem drain_within (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high) :
    (phase.drain state).native.config.cut.Within phase.low phase.high :=
  phase.drainFuel_within _ _ within

/-- If every event in a binding phase belongs to an excluded principal,
automatic completion settles the entire phase without a new attempt. -/
theorem drain_finished_of_excluded (state : RecoveryState graph)
    (within : state.native.config.cut.Within phase.low phase.high)
    (kind : phase.kind = .commitment) (excluded : phase.owners ⊆ state.excluded) :
    phase.Finished (phase.drain state) := by
  intro event member
  by_contra missing
  obtain ⟨readyEvent, ready, below⟩ :=
    (phase.drain state).native.config.cut.exists_ready_le_of_unfinished event missing
  have inside : readyEvent ∈ phase.events := by
    apply (phase.mem_events _).mpr
    refine ⟨?_, lt_of_le_of_lt below ((phase.mem_events _).mp member).2⟩
    by_contra lower
    exact ready.1 ((phase.drain_within state within).1 _ (by omega))
  have fields := phase.fields readyEvent ((phase.mem_events _).mp inside).1
    ((phase.mem_events _).mp inside).2
  rw [kind] at fields
  obtain ⟨owner, payload, outputEq⟩ := fields
  have acting : graph.actor? readyEvent = some owner := by
    cases viewed : nodeView graph readyEvent with
    | bind actor ty typed code =>
        obtain ⟨rfl, rfl⟩ := EventField.binding.inj (typed.symm.trans outputEq)
        exact (EventCode.actor_cast typed (graph.nodes readyEvent)).symm.trans
          (congrArg EventCode.actor code)
    | resolve actor ty binding checks typed code => cases typed.symm.trans outputEq
    | sample ty law typed code => cases typed.symm.trans outputEq
  have ownerMember : owner ∈ phase.owners := by
    exact Finset.mem_biUnion.mpr ⟨readyEvent, inside, by simp only [acting,
      Option.toFinset_some, Finset.mem_singleton]⟩
  apply phase.drain_quiescent state readyEvent
  refine ⟨inside, ready, ?_⟩
  rw [acting, phase.drain_excluded]
  exact excluded ownerMember

end Vegas.EventGraphRuntime.RuntimePhase
