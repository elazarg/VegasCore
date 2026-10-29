/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventApplication

/-! # Native automatic completion after public default

Automatic service uses the default record retained by the graph configuration.
Each completion is an actual graph step and preserves public default membership.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

namespace State

/-- Complete an owned event as failure, independently of clocks and packets.
Samples are unchanged and are never selected for automatic default service. -/
def completeFailure (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) : State graph :=
  match nodeView graph event with
  | .bind _owner payload outputEq _ =>
      state.complete event ready
        (cast (congrArg EventField.Action outputEq.symm)
          (none : Option (PublicationResult (L.Val payload))))
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

/-- Automatic default service uses the original graph law, with its guard semantics. -/
theorem completeFailure_step (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) {owner : Player}
    (acting : graph.actor? event = some owner) :
    ∃ action : graph.Action event,
      (state.completeFailure event ready).config ∈ (state.config.step event ready action).support :=
    by
  cases view : nodeView graph event with
  | bind actor payload outputEq codeEq =>
      refine ⟨cast (congrArg EventField.Action outputEq.symm)
        (none : Option (PublicationResult (L.Val payload))), ?_⟩
      rw [state.config.step_eq_map_of_code event ready outputEq (.bind actor payload) codeEq
        none (PMF.pure PublicationResult.failure)
        (by simp [EventCode.effectiveAction, EventCode.actor, EventCode.failureAction])]
      simp [completeFailure, view, complete]
  | resolve actor payload binding checks outputEq codeEq =>
      refine ⟨cast (congrArg EventField.Action outputEq.symm) false, ?_⟩
      rw [state.config.step_eq_map_of_code event ready outputEq
        (.resolve actor payload binding checks) codeEq false (PMF.pure PublicationResult.failure)]
      · simp [completeFailure, view, complete]
      · simp only [EventCode.effectiveAction, EventCode.actor, EventCode.failureAction, ite_self]
        rw [EventCode.resolve_eval?, false_resolution_available state event ready actor payload
          binding checks outputEq codeEq]
        rfl
  | sample payload law outputEq codeEq =>
      have actorEq : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [actorEq] at acting
      cases acting

theorem completeFailure_tables (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) :
    (state.completeFailure event ready).accepted = state.accepted ∧
      (state.completeFailure event ready).candidates = state.candidates ∧
      (state.completeFailure event ready).clock = state.clock := by
  cases view : nodeView graph event <;> simp [completeFailure, view, complete]

/-- Structural readiness of a defaulted owner is serviced automatically. -/
def AutomaticReady (state : State graph) (event : graph.EventId) : Prop :=
  state.config.cut.Ready event ∧
    match graph.actor? event with
    | none => False
    | some owner => owner ∈ state.config.defaulted

instance (state : State graph) : DecidablePred state.AutomaticReady := fun event => by
  unfold AutomaticReady
  cases graph.actor? event <;> infer_instance

theorem AutomaticReady.owned {state : State graph} {event : graph.EventId}
    (eligible : state.AutomaticReady event) :
    ∃ owner, graph.actor? event = some owner ∧ owner ∈ state.config.defaulted := by
  rcases eligible with ⟨_, eligible⟩
  cases acting : graph.actor? event with
  | none => rw [acting] at eligible; exact eligible.elim
  | some owner => exact ⟨owner, rfl, by simpa only [acting] using eligible⟩

def completeAutomatic (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) : State graph :=
  state.completeFailure event eligible.1

/-- Completing an already defaulted owner records chronology without a new default. -/
theorem completeFailure_defaults_of_defaulted (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (owner : Player)
    (acting : graph.actor? event = some owner) (inactive : owner ∈ state.config.defaulted) :
    (state.completeFailure event ready).config.defaults = state.config.defaults.record none := by
  have owned : (graph.nodes event).actor = some owner := acting
  cases view : nodeView graph event with
  | bind actor payload outputEq codeEq =>
      simp only [completeFailure, view, complete]
      rw [EventGraph.Config.complete_defaults,
        state.config.actualDecision_of_defaulted event owner owned inactive]
      rfl
  | resolve actor payload binding checks outputEq codeEq =>
      simp only [completeFailure, view, complete]
      rw [EventGraph.Config.complete_defaults,
        state.config.actualDecision_of_defaulted event owner owned inactive]
      rfl
  | sample payload law outputEq codeEq =>
      have actorEq : graph.actor? event = none :=
        (EventCode.actor_cast outputEq (graph.nodes event)).symm.trans
          (congrArg EventCode.actor codeEq)
      rw [actorEq] at acting
      cases acting

/-- Automatic completion retains the public history of one silent instruction. -/
theorem completeAutomatic_defaults (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).config.defaults =
      state.config.defaults.record none := by
  obtain ⟨owner, acting, inactive⟩ := eligible.owned
  exact state.completeFailure_defaults_of_defaulted event eligible.1 owner acting inactive

/-- Automatic service cannot add or remove publicly defaulted owners. -/
theorem completeAutomatic_defaulted (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).config.defaulted = state.config.defaulted := by
  change (state.completeAutomatic event eligible).config.defaults.defaulted =
    state.config.defaults.defaulted
  rw [state.completeAutomatic_defaults event eligible]
  exact DefaultHistory.defaulted_record_none _

/-- Every automatic service is a supported graph completion of a defaulted owner. -/
theorem completeAutomatic_step (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    ∃ action : graph.Action event,
      (state.completeAutomatic event eligible).config ∈
        (state.config.step event eligible.1 action).support := by
  obtain ⟨owner, acting, _⟩ := eligible.owned
  exact state.completeFailure_step event eligible.1 acting

theorem completeAutomatic_progress (state : State graph) (event : graph.EventId)
    (eligible : state.AutomaticReady event) :
    (state.completeAutomatic event eligible).config.remaining + 1 =
      state.config.remaining := by
  obtain ⟨action, realized⟩ := state.completeAutomatic_step event eligible
  exact state.config.remaining_step event eligible.1 action _ realized

open Classical in
/-- Bounded deterministic automatic service; no scheduler or owner is queried. -/
def drainFuel : Nat → State graph → State graph
  | 0, state => state
  | fuel + 1, state =>
      if pending : ∃ event, state.AutomaticReady event then
        drainFuel fuel (state.completeAutomatic (Classical.choose pending)
          (Classical.choose_spec pending))
      else state

/-- Automatic completions form an actual native graph-step path. -/
def AutomaticStep (before after : State graph) : Prop :=
  ∃ event, ∃ eligible : before.AutomaticReady event,
    after = before.completeAutomatic event eligible

theorem drainFuel_trace (fuel : Nat) (state : State graph) :
    Relation.ReflTransGen AutomaticStep state (drainFuel fuel state) := by
  induction fuel generalizing state with
  | zero => exact .refl
  | succ fuel ih =>
      unfold drainFuel
      split
      · rename_i pending
        exact (Relation.ReflTransGen.single ⟨_, Classical.choose_spec pending, rfl⟩).trans (ih _)
      · exact .refl

/-- Every predicate preserved by a single automatic completion is preserved
by the bounded drain's existing native step trace. -/
theorem drainFuel_induction (predicate : State graph → Prop)
    (preserves : ∀ (before : State graph) (event : graph.EventId)
      (eligible : before.AutomaticReady event), predicate before →
      predicate (before.completeAutomatic event eligible))
    (fuel : Nat) (state : State graph) (initial : predicate state) :
    predicate (drainFuel fuel state) := by
  have closed : ∀ {before after}, Relation.ReflTransGen AutomaticStep before after →
      predicate before → predicate after := by
    intro before after path
    induction path using Relation.ReflTransGen.head_induction_on with
    | refl => exact id
    | @head before middle moved _ ih =>
        obtain ⟨event, eligible, rfl⟩ := moved
        exact fun valid => ih (preserves before event eligible valid)
  exact closed (drainFuel_trace fuel state) initial

theorem drainFuel_quiescent (fuel : Nat) (state : State graph)
    (enough : state.config.remaining ≤ fuel) :
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

theorem drainFuel_eq_of_clear (fuel : Nat) (state : State graph)
    (clear : ∀ event, ¬ state.AutomaticReady event) : drainFuel fuel state = state := by
  cases fuel with
  | zero => rfl
  | succ fuel => simp only [drainFuel, show ¬ (∃ event, state.AutomaticReady event) from
      fun ⟨event, eligible⟩ => clear event eligible, ↓reduceDIte]

def drain (state : State graph) : State graph :=
  drainFuel state.config.remaining state

theorem drain_quiescent (state : State graph) :
    ∀ event, ¬ state.drain.AutomaticReady event :=
  drainFuel_quiescent _ _ le_rfl

theorem drain_eq_of_clear (state : State graph)
    (clear : ∀ event, ¬ state.AutomaticReady event) : state.drain = state :=
  drainFuel_eq_of_clear _ _ clear

theorem drainFuel_defaulted (fuel : Nat) (state : State graph) :
    (drainFuel fuel state).config.defaulted = state.config.defaulted := by
  exact drainFuel_induction (fun next => next.config.defaulted = state.config.defaulted)
    (fun before event eligible previous =>
      (before.completeAutomatic_defaulted event eligible).trans previous) fuel state rfl

theorem drainFuel_tables (fuel : Nat) (state : State graph) :
    (drainFuel fuel state).accepted = state.accepted ∧
      (drainFuel fuel state).candidates = state.candidates ∧
      (drainFuel fuel state).clock = state.clock := by
  apply drainFuel_induction (fun next => next.accepted = state.accepted ∧
    next.candidates = state.candidates ∧ next.clock = state.clock)
    (fun before event eligible previous => ?_) fuel state ⟨rfl, rfl, rfl⟩
  obtain ⟨accepted, candidates, clock⟩ := before.completeFailure_tables event eligible.1
  exact ⟨accepted.trans previous.1, candidates.trans previous.2.1, clock.trans previous.2.2⟩

theorem drainFuel_reachable (fuel : Nat) (state : State graph) {inputs : graph.Inputs}
    (reachable : state.config.Reachable inputs) :
    (drainFuel fuel state).config.Reachable inputs := by
  apply drainFuel_induction (fun next => next.config.Reachable inputs)
    (fun before event eligible previous => ?_) fuel state reachable
  obtain ⟨action, realized⟩ := before.completeAutomatic_step event eligible
  exact .step previous event eligible.1 action _ realized

theorem drain_trace (state : State graph) :
    Relation.ReflTransGen AutomaticStep state state.drain := drainFuel_trace _ _

theorem drain_defaulted (state : State graph) :
    state.drain.config.defaulted = state.config.defaulted :=
  drainFuel_defaulted _ _

theorem drain_tables (state : State graph) :
    state.drain.accepted = state.accepted ∧
      state.drain.candidates = state.candidates ∧
      state.drain.clock = state.clock := drainFuel_tables _ _

theorem drain_reachable (state : State graph) {inputs : graph.Inputs}
    (reachable : state.config.Reachable inputs) :
    state.drain.config.Reachable inputs := drainFuel_reachable _ _ reachable

/-- Without a public default, automatic service changes nothing. -/
theorem drain_eq_of_empty (state : State graph) (empty : state.config.defaulted = ∅) :
    state.drain = state := by
  apply state.drain_eq_of_clear
  intro event eligible
  obtain ⟨owner, _, member⟩ := eligible.owned
  simp only [empty, Finset.notMem_empty] at member

/-- Draining native automatic completions follows a finite supported graph path. -/
theorem drain_graph_steps (state : State graph) :
    Relation.ReflTransGen EventGraph.Config.Step state.config state.drain.config := by
  apply Relation.ReflTransGen.lift (fun current : State graph => current.config) _
    state state.drain state.drain_trace
  intro before after moved
  obtain ⟨event, eligible, rfl⟩ := moved
  obtain ⟨action, supported⟩ := before.completeAutomatic_step event eligible
  exact ⟨event, eligible.1, action, supported⟩

end State
end Vegas.EventGraphRuntime
