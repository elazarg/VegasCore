/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventInvariant

/-! # Automatic completion of excluded owners' events

Excluded owners do not receive a new ready event. The recovery carrier drains
all such structural graph readiness before exposing its next observation.
Each automatic completion is an actual binding-failure or false-reveal graph step.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

/-- Complete an owned event as failure, independently of clocks and packets.
Samples are unchanged and are never selected for automatic exclusion service. -/
def completeFailure (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) : State graph :=
  match nodeView graph event with
  | .bind _owner payload outputEq _ =>
      state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))
  | .resolve _owner payload _binding _checks outputEq _ =>
      state.complete event ready (cast (congrArg EventField.Action outputEq.symm) false)
        (cast (congrArg EventField.Value outputEq.symm)
          (PublicationResult.failure : PublicationResult (L.Val payload)))
  | .sample .. => state

omit [DecidableEq Player] in
private theorem false_resolution_available (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks) :
    EventCode.resolveOutput? binding checks false state.config.store = some .failure := by
  apply EventCode.resolveOutput?_false_eq_failure binding checks state.config.store
  intro field read
  apply state.config.read_available ready
  rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
  exact read

omit [DecidableEq Player] in
/-- Automatic exclusion service uses the original graph law, with its guard semantics. -/
theorem completeFailure_step (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    ∃ action : graph.Action event,
      (state.completeFailure event ready).config ∈ (state.config.step event ready action).support :=
    by
  cases view : nodeView graph event with
  | bind actor payload outputEq codeEq =>
      refine ⟨cast (congrArg EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload)), ?_⟩
      rw [state.config.step_eq_map_of_code event ready outputEq (.bind actor payload) codeEq
        PublicationResult.failure (PMF.pure PublicationResult.failure) rfl]
      simp [completeFailure, view, complete]
  | resolve actor payload binding checks outputEq codeEq =>
      refine ⟨cast (congrArg EventField.Action outputEq.symm) false, ?_⟩
      rw [state.config.step_eq_map_of_code event ready outputEq
        (.resolve actor payload binding checks) codeEq false (PMF.pure PublicationResult.failure)]
      · simp [completeFailure, view, complete]
      · rw [EventCode.resolve_eval?, false_resolution_available state event ready actor payload
          binding checks outputEq codeEq]
        rfl
  | sample payload law outputEq codeEq =>
      have actorEq : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [actorEq] at acting
      cases acting

omit [DecidableEq Player] in
theorem completeFailure_tables (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) :
    (state.completeFailure event ready).accepted = state.accepted ∧
      (state.completeFailure event ready).candidates = state.candidates ∧
      (state.completeFailure event ready).clock = state.clock := by
  cases view : nodeView graph event <;> simp [completeFailure, view, complete]

end State

/-- Native recovery keeps permanent exclusion separately from hidden binding values. -/
structure RecoveryState (graph : Vegas.EventGraph Player L) where
  native : State graph
  excluded : Finset Player

namespace RecoveryState

/-- Structural readiness of an excluded owner is serviced automatically. -/
def AutomaticReady (state : RecoveryState graph) (event : graph.EventId) : Prop :=
  state.native.config.cut.Ready event ∧
    match graph.actor? event with
    | none => False
    | some owner => owner ∈ state.excluded

instance (state : RecoveryState graph) : DecidablePred state.AutomaticReady := fun event => by
  unfold AutomaticReady
  cases graph.actor? event <;> infer_instance

omit [DecidableEq Player] in
theorem AutomaticReady.owned {state : RecoveryState graph} {event : graph.EventId}
    (eligible : state.AutomaticReady event) :
    ∃ owner, graph.actor? event = some owner ∧ owner ∈ state.excluded := by
  rcases eligible with ⟨_, eligible⟩
  cases acting : graph.actor? event with
  | none => rw [acting] at eligible; exact eligible.elim
  | some owner => exact ⟨owner, rfl, by simpa only [acting] using eligible⟩

def completeAutomatic (state : RecoveryState graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) : RecoveryState graph :=
  { state with native := state.native.completeFailure event eligible.1 }

omit [DecidableEq Player] in
/-- Every automatic service is a supported graph completion of an excluded owner. -/
theorem completeAutomatic_step (state : RecoveryState graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    ∃ action : graph.Action event,
      (state.completeAutomatic event eligible).native.config ∈
        (state.native.config.step event eligible.1 action).support := by
  obtain ⟨owner, acting, _⟩ := eligible.owned
  exact state.native.completeFailure_step event eligible.1 acting

omit [DecidableEq Player] in
theorem completeAutomatic_progress (state : RecoveryState graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).native.config.remaining + 1 =
      state.native.config.remaining := by
  obtain ⟨action, realized⟩ := state.completeAutomatic_step event eligible
  exact state.native.config.remaining_step event eligible.1 action _ realized

open Classical in
/-- Bounded deterministic automatic service; no scheduler or owner is queried. -/
def drainFuel : Nat → RecoveryState graph → RecoveryState graph
  | 0, state => state
  | fuel + 1, state =>
      if pending : ∃ event, state.AutomaticReady event then
        drainFuel fuel (state.completeAutomatic (Classical.choose pending)
          (Classical.choose_spec pending))
      else state

/-- Automatic completions form an actual native graph-step path. -/
def AutomaticStep (before after : RecoveryState graph) : Prop :=
  ∃ event, ∃ eligible : before.AutomaticReady event,
    after = before.completeAutomatic event eligible

theorem drainFuel_trace (fuel : Nat) (state : RecoveryState graph) :
    Relation.ReflTransGen AutomaticStep state (drainFuel fuel state) := by
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
    ∀ event, ¬ (drainFuel fuel state).AutomaticReady event := by
  induction fuel generalizing state with
  | zero =>
      intro event eligible
      have progress := state.completeAutomatic_progress event eligible
      omega
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        apply ih
        have progress := state.completeAutomatic_progress _ (Classical.choose_spec pending)
        omega
      · rename_i clear
        exact fun event eligible => clear ⟨event, eligible⟩

theorem drainFuel_eq_of_clear (fuel : Nat) (state : RecoveryState graph)
    (clear : ∀ event, ¬ state.AutomaticReady event) : drainFuel fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [drainFuel, show ¬ (∃ event, state.AutomaticReady event) from
      fun ⟨event, eligible⟩ => clear event eligible, ↓reduceDIte]

def drain (state : RecoveryState graph) : RecoveryState graph :=
  drainFuel state.native.config.remaining state

theorem drain_quiescent (state : RecoveryState graph) :
    ∀ event, ¬ state.drain.AutomaticReady event :=
  drainFuel_quiescent _ _ le_rfl

theorem drain_eq_of_clear (state : RecoveryState graph)
    (clear : ∀ event, ¬ state.AutomaticReady event) : state.drain = state :=
  drainFuel_eq_of_clear _ _ clear

theorem drainFuel_excluded (fuel : Nat) (state : RecoveryState graph) :
    (drainFuel fuel state).excluded = state.excluded := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      unfold drainFuel
      split
      · exact ih _
      · rfl

theorem drainFuel_tables (fuel : Nat) (state : RecoveryState graph) :
    (drainFuel fuel state).native.accepted = state.native.accepted ∧
      (drainFuel fuel state).native.candidates = state.native.candidates ∧
      (drainFuel fuel state).native.clock = state.native.clock := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, rfl, rfl⟩
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨accepted, candidates, clock⟩ := state.native.completeFailure_tables
          (Classical.choose pending) (Classical.choose_spec pending).1
        obtain ⟨laterAccepted, laterCandidates, laterClock⟩ := ih
          (state.completeAutomatic (Classical.choose pending) (Classical.choose_spec pending))
        exact ⟨laterAccepted.trans accepted, laterCandidates.trans candidates,
          laterClock.trans clock⟩
      · exact ⟨rfl, rfl, rfl⟩

theorem drainFuel_reachable (fuel : Nat) (state : RecoveryState graph) {inputs : graph.Inputs}
    (reachable : state.native.config.Reachable inputs) :
    (drainFuel fuel state).native.config.Reachable inputs := by
  induction fuel generalizing state with
  | zero => exact reachable
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        obtain ⟨action, realized⟩ := state.completeAutomatic_step (Classical.choose pending)
          (Classical.choose_spec pending)
        exact ih _ (.step reachable _ (Classical.choose_spec pending).1 action _ realized)
      · exact reachable

theorem drain_trace (state : RecoveryState graph) :
    Relation.ReflTransGen AutomaticStep state state.drain := drainFuel_trace _ _

theorem drain_excluded (state : RecoveryState graph) : state.drain.excluded = state.excluded :=
  drainFuel_excluded _ _

theorem drain_tables (state : RecoveryState graph) :
    state.drain.native.accepted = state.native.accepted ∧
      state.drain.native.candidates = state.native.candidates ∧
      state.drain.native.clock = state.native.clock := drainFuel_tables _ _

theorem drain_reachable (state : RecoveryState graph) {inputs : graph.Inputs}
    (reachable : state.native.config.Reachable inputs) :
    state.drain.native.config.Reachable inputs := drainFuel_reachable _ _ reachable

/-- The wrapper agrees exactly with the default native state before any exclusion. -/
theorem drain_eq_of_empty (state : RecoveryState graph) (empty : state.excluded = ∅) :
    state.drain = state := by
  apply state.drain_eq_of_clear
  intro event eligible
  obtain ⟨owner, _, member⟩ := eligible.owned
  simp only [empty, Finset.notMem_empty] at member

end RecoveryState
end Vegas.EventGraphRuntime
