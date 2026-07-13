import Vegas.EventGraph.Batch
import Vegas.Machine.Basic
import Vegas.Machine.Trace

/-!
# EventGraph primitive machine adapter

The graph execution layer steps witness-carrying available events.  The generic
`Machine` interface has total step functions over raw action names, so this
adapter totalizes unavailable raw machine events by stuttering.  Legal machine
event laws quantify over `available`, so the stutter branch is outside the
semantic execution surface.

This adapter is a primitive protocol machine, not the compiled-game surface.
Game-facing code should use a checkpoint presentation instead.
-/

namespace Vegas

namespace EventGraph

namespace ToMachine

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Event-graph data needed to expose a graph as a primitive protocol machine.

This lives at the EventGraph layer: source compilation is one producer of this
spec, but backends or hand-written graphs can provide the same evidence
directly. -/
structure GraphMachineSpec (G : Graph P L) where
  graphWF : G.WF
  payoffs : List (P × EventPayoff L)
  payoffsWF :
    ∀ payoff, payoff ∈ payoffs →
      ∀ ref, ref ∈ payoff.2.reads →
        G.fieldRefPublic ref ∧
        G.fieldAvailableBefore G.nodeCount ref.field = true

/-- Machine utility is the real-valued coercion of integer outcomes. -/
noncomputable def utility (outcome : Outcome P) : Payoff P :=
  fun player => (outcome player : ℝ)

/-- Reachable terminal states of a graph machine always have a defined payoff
projection. -/
theorem terminalPayoffTotal
    {G : Graph P L} (spec : GraphMachineSpec G)
    (state : ReachableConfig G)
    (hterminal : Terminal G state.1) :
    ∃ outcome, evalPayoffs? spec.payoffs state.1.store = some outcome := by
  have hcoherent :=
    reachable_storeCoherent spec.graphWF state.2
  exact
    evalPayoffs?_isSome_of_available spec.payoffs state.1.store
      (by
        intro payoff hpayoff ref href
        rcases spec.payoffsWF payoff hpayoff ref href with
          ⟨hpublic, havailable⟩
        exact hcoherent.hasRefOfAvailable hterminal hpublic havailable)

/-- Adapter from the generic machine's total player-step surface to the
graph's evidence-carrying available-event step. -/
private noncomputable def stepPlay
    (G : Graph P L)
    (who : P) (action : CommitAction G who)
    (state : ReachableConfig G) :
    PMF (ReachableConfig G) := by
  classical
  exact
    if h : CommitAvailable G state.1 who action then
      stepAvailable G state
        (.commit who action (Classical.choice h))
    else
      PMF.pure state

/-- Adapter from the generic machine's total internal-step surface to the
graph's evidence-carrying available-event step. -/
private noncomputable def stepInternal
    (G : Graph P L)
    (event : InternalEvent G)
    (state : ReachableConfig G) :
    PMF (ReachableConfig G) := by
  classical
  exact
    if h : InternalAvailable G state.1 event then
      stepAvailable G state
        (.internal event (Classical.choice h))
    else
      PMF.pure state

/-- Package an event graph as a primitive protocol information machine.

The resulting machine's available events are exactly the graph events whose
prerequisites are satisfied and whose local computation is defined.  Schedule
choice remains external through legal `Machine.EventLaw`s.

Terminality is graph terminality: all graph events are complete. Outcomes are
partial only for nonterminal states; reachable terminal compiled states use the
compiled payoff-totality proof. -/
noncomputable def primitiveMachine
    {G : Graph P L} (spec : GraphMachineSpec G) :
    Machine P where
  State := ReachableConfig G
  Action := fun who => CommitAction G who
  Internal := InternalEvent G
  Public := PublicObservation G
  Obs := fun who => Observation G who
  Outcome := Outcome P
  init := ⟨Config.initial G, Reachable.initial⟩
  available := fun state who =>
    { action | CommitAvailable G state.1 who action }
  availableInternal := fun state =>
    { event | InternalAvailable G state.1 event }
  stepPlay := fun who action state =>
    stepPlay G who action state
  stepInternal := fun event state =>
    stepInternal G event state
  terminal := fun state =>
    Terminal G state.1
  publicView := fun state => publicObserve G state.1
  observe := fun who state => EventGraph.observe G state.1 who
  outcome := fun state => by
    classical
    exact
      if hterminal : Terminal G state.1 then
        some (Classical.choose
          (terminalPayoffTotal spec state hterminal))
      else
        none
  utility := utility

/-- The graph node named by a primitive event of the EventGraph machine. -/
def primitiveMachineEventNode
    {G : Graph P L} (spec : GraphMachineSpec G) :
    (primitiveMachine spec).Event → Fin G.nodeCount
  | .play _ action => action.node
  | .internal event => event.node

/-- A graph-available commit action has positive support in the primitive
machine adapter, and every exposed successor completes that commit node with
the value produced by the concrete guard witness. -/
theorem primitiveMachine_step_play_available_support
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state : ReachableConfig G}
    {who : P} {action : CommitAction G who}
    (havailable : CommitAvailable G state.1 who action) :
    ∃ written : TypedValue L,
      ∃ next : ReachableConfig G,
        next ∈
          ((primitiveMachine spec).step
            (.play who action) state).support ∧
        next.1 = state.1.completeNode action.node written := by
  classical
  let step := Classical.choice havailable
  let written : TypedValue L :=
    { ty := step.guard.ty, value := step.value }
  have hraw :
      state.1.completeNode action.node written ∈
        (stepAvailableEvent G state.1
          (.commit who action step)).support := by
    simp [stepAvailableEvent, stepCommit, written]
  let next : ReachableConfig G :=
    ⟨state.1.completeNode action.node written,
      Reachable.step state.2 (.commit who action step) hraw⟩
  refine ⟨written, next, ?_, rfl⟩
  change next ∈ (stepPlay G who action state).support
  unfold stepPlay
  rw [dif_pos havailable]
  unfold stepAvailable
  rw [PMF.mem_support_bindOnSupport_iff]
  exact ⟨state.1.completeNode action.node written, hraw, by simp [next]⟩

/-- A graph-available internal event has positive support in the primitive
machine adapter, and every exposed successor completes that internal node with
the value produced by the concrete internal-step witness. -/
theorem primitiveMachine_step_internal_available_support
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state : ReachableConfig G}
    {event : InternalEvent G}
    (havailable : InternalAvailable G state.1 event) :
    ∃ written : TypedValue L,
      ∃ next : ReachableConfig G,
        next ∈
          ((primitiveMachine spec).step
            (.internal event) state).support ∧
        next.1 = state.1.completeNode event.node written := by
  classical
  let step := Classical.choice havailable
  have hex :
      ∃ written : TypedValue L,
        state.1.completeNode event.node written ∈
          (stepAvailableEvent G state.1
            (.internal event step)).support := by
    cases step with
    | sample row dist row_get sem_eq ready env env_ok =>
      rcases (dist.eval env).support_nonempty with ⟨value, hvalue⟩
      let written : TypedValue L := { ty := dist.ty, value := value }
      refine ⟨written, ?_⟩
      dsimp [stepAvailableEvent, stepInternal, written]
      exact
        (PMF.mem_support_map_iff _ _ _).mpr
          ⟨value, hvalue, rfl⟩
    | reveal row source row_get sem_eq ready value value_ok =>
      let written : TypedValue L := { ty := row.ty, value := value }
      refine ⟨written, ?_⟩
      dsimp [stepAvailableEvent, EventGraph.stepInternal]
      rw [PMF.support_pure]
      simp [written]
  rcases hex with ⟨written, hraw⟩
  let next : ReachableConfig G :=
    ⟨state.1.completeNode event.node written,
      Reachable.step state.2 (.internal event step) hraw⟩
  refine ⟨written, next, ?_, rfl⟩
  change next ∈ (stepInternal G event state).support
  unfold stepInternal
  rw [dif_pos havailable]
  unfold stepAvailable
  rw [PMF.mem_support_bindOnSupport_iff]
  exact ⟨state.1.completeNode event.node written, hraw, by simp [next]⟩

/-- Every supported successor of an available player primitive-machine step
is obtained by completing that commit node. -/
theorem primitiveMachine_step_play_support_completeNode
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state next : ReachableConfig G}
    {who : P} {action : CommitAction G who}
    (havailable : CommitAvailable G state.1 who action)
    (hstep :
      next ∈
        ((primitiveMachine spec).step
          (.play who action) state).support) :
    ∃ written : TypedValue L,
      next.1 = state.1.completeNode action.node written := by
  classical
  let step := Classical.choice havailable
  have hstep' := hstep
  change next ∈ (stepPlay G who action state).support at hstep'
  unfold stepPlay at hstep'
  rw [dif_pos havailable] at hstep'
  unfold stepAvailable at hstep'
  rw [PMF.mem_support_bindOnSupport_iff] at hstep'
  rcases hstep' with ⟨rawNext, hrawNext, hnext⟩
  rw [PMF.support_pure, Set.mem_singleton_iff] at hnext
  subst next
  rcases
      stepAvailableEvent_support_completeNode
        (.commit who action step) hrawNext with
    ⟨written, hrawEq⟩
  exact ⟨written, hrawEq⟩

/-- Every supported successor of an available internal primitive-machine step
is obtained by completing that internal node with one of the values sampled or
revealed by the graph event. -/
theorem primitiveMachine_step_internal_support_completeNode
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state next : ReachableConfig G}
    {event : InternalEvent G}
    (havailable : InternalAvailable G state.1 event)
    (hstep :
      next ∈
        ((primitiveMachine spec).step
          (.internal event) state).support) :
    ∃ written : TypedValue L,
      next.1 = state.1.completeNode event.node written := by
  classical
  have hstep' := hstep
  change next ∈ (stepInternal G event state).support at hstep'
  unfold stepInternal at hstep'
  rw [dif_pos havailable] at hstep'
  unfold stepAvailable at hstep'
  rw [PMF.mem_support_bindOnSupport_iff] at hstep'
  rcases hstep' with ⟨rawNext, hrawNext, hnext⟩
  rw [PMF.support_pure, Set.mem_singleton_iff] at hnext
  subst next
  rcases
      stepAvailableEvent_support_completeNode
        (.internal event (Classical.choice havailable)) hrawNext with
    ⟨written, hrawEq⟩
  exact ⟨written, hrawEq⟩

/-- Every supported successor of an available primitive-machine step completes
the node named by that primitive machine event. -/
theorem primitiveMachine_step_support_completeNode
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state next : ReachableConfig G}
    {event : (primitiveMachine spec).Event}
    (havailable :
      (primitiveMachine spec).EventAvailable state event)
    (hstep :
      next ∈ ((primitiveMachine spec).step event state).support) :
    ∃ node : Fin G.nodeCount,
      ∃ written : TypedValue L,
        next.1 = state.1.completeNode node written := by
  cases event with
  | play who action =>
      rcases primitiveMachine_step_play_support_completeNode
          spec havailable hstep with
        ⟨written, hnext⟩
      exact ⟨action.node, written, hnext⟩
  | internal event =>
      rcases primitiveMachine_step_internal_support_completeNode
          spec havailable hstep with
        ⟨written, hnext⟩
      exact ⟨event.node, written, hnext⟩

/-- Every supported successor of an available primitive-machine step completes
the graph node named by that primitive machine event. -/
theorem primitiveMachine_step_support_completeEventNode
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state next : ReachableConfig G}
    {event : (primitiveMachine spec).Event}
    (havailable :
      (primitiveMachine spec).EventAvailable state event)
    (hstep :
      next ∈ ((primitiveMachine spec).step event state).support) :
    ∃ written : TypedValue L,
      next.1 =
        state.1.completeNode
          (primitiveMachineEventNode spec event) written := by
  cases event with
  | play who action =>
      exact primitiveMachine_step_play_support_completeNode
        spec havailable hstep
  | internal event =>
      exact primitiveMachine_step_internal_support_completeNode
        spec havailable hstep

/-- Supported completions of two distinct available primitive-machine events
commute at the raw graph configuration level. -/
theorem primitiveMachine_supported_steps_complete_comm
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state leftNext rightNext : ReachableConfig G}
    {left right : (primitiveMachine spec).Event}
    (hleftAvailable :
      (primitiveMachine spec).EventAvailable state left)
    (hrightAvailable :
      (primitiveMachine spec).EventAvailable state right)
    (hne :
      primitiveMachineEventNode spec left ≠
        primitiveMachineEventNode spec right)
    (hleft :
      leftNext ∈ ((primitiveMachine spec).step left state).support)
    (hright :
      rightNext ∈ ((primitiveMachine spec).step right state).support) :
    ∃ leftWritten rightWritten : TypedValue L,
      leftNext.1 =
        state.1.completeNode
          (primitiveMachineEventNode spec left) leftWritten ∧
      rightNext.1 =
        state.1.completeNode
          (primitiveMachineEventNode spec right) rightWritten ∧
      leftNext.1.completeNode
          (primitiveMachineEventNode spec right) rightWritten =
        rightNext.1.completeNode
          (primitiveMachineEventNode spec left) leftWritten := by
  rcases primitiveMachine_step_support_completeEventNode
      spec hleftAvailable hleft with
    ⟨leftWritten, hleftNext⟩
  rcases primitiveMachine_step_support_completeEventNode
      spec hrightAvailable hright with
    ⟨rightWritten, hrightNext⟩
  refine ⟨leftWritten, rightWritten, hleftNext, hrightNext, ?_⟩
  rw [hleftNext, hrightNext]
  exact Config.completeNode_comm state.1 leftWritten rightWritten hne

/-- A distinct primitive-machine event that is available before an available
step remains available after that step. This is the machine-level
adjacent-swap availability lemma for schedule-independence proofs. -/
theorem primitiveMachine_available_persist_after_supported_step
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state next : ReachableConfig G}
    {first second : (primitiveMachine spec).Event}
    (hfirstAvailable :
      (primitiveMachine spec).EventAvailable state first)
    (hsecondAvailable :
      (primitiveMachine spec).EventAvailable state second)
    (hne :
      primitiveMachineEventNode spec second ≠
        primitiveMachineEventNode spec first)
    (hstep :
      next ∈ ((primitiveMachine spec).step first state).support) :
    (primitiveMachine spec).EventAvailable next second := by
  rcases primitiveMachine_step_support_completeEventNode
      spec hfirstAvailable hstep with
    ⟨written, hnext⟩
  have hfirstReady :
      ∃ row : EventNode P L,
        G.nodes[primitiveMachineEventNode spec first]? = some row ∧
          Ready G state.1 (primitiveMachineEventNode spec first) := by
    cases first with
    | play who action =>
        change CommitAvailable G state.1 who action at hfirstAvailable
        rcases hfirstAvailable with ⟨step⟩
        exact ⟨step.row, step.row_get, step.ready⟩
    | internal event =>
        change InternalAvailable G state.1 event at hfirstAvailable
        rcases hfirstAvailable.ready with ⟨row, hrow, hready⟩
        exact ⟨row, hrow, hready⟩
  rcases hfirstReady with ⟨firstRow, hfirstRow, hfirstReady⟩
  cases second with
  | play who action =>
      change CommitAvailable G next.1 who action
      rw [hnext]
      change CommitAvailable G state.1 who action at hsecondAvailable
      exact
        hsecondAvailable.persist_after_other_ready_write
          spec.graphWF hfirstRow hfirstReady written hne
  | internal event =>
      change InternalAvailable G next.1 event
      rw [hnext]
      change InternalAvailable G state.1 event at hsecondAvailable
      exact
        hsecondAvailable.persist_after_other_ready_write
          spec.graphWF hfirstRow hfirstReady written hne

theorem primitiveMachine_step_available_support
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state : ReachableConfig G}
    {event : (primitiveMachine spec).Event}
    (havailable :
      (primitiveMachine spec).EventAvailable state event) :
    ∃ next : ReachableConfig G,
      next ∈
        ((primitiveMachine spec).step event state).support := by
  classical
  cases event with
  | play who action =>
      rcases primitiveMachine_step_play_available_support
          spec havailable with
        ⟨_written, next, hnext, _hcfg⟩
      exact ⟨next, hnext⟩
  | internal event =>
      change InternalAvailable G state.1 event at havailable
      let step := Classical.choice havailable
      have hrawNonempty :
          (stepAvailableEvent G state.1
            (.internal event step)).support.Nonempty :=
        (stepAvailableEvent G state.1
          (.internal event step)).support_nonempty
      rcases hrawNonempty with ⟨raw, hraw⟩
      let next : ReachableConfig G :=
        ⟨raw, Reachable.step state.2 (.internal event step) hraw⟩
      refine ⟨next, ?_⟩
      change next ∈ (stepInternal G event state).support
      unfold stepInternal
      rw [dif_pos havailable]
      unfold stepAvailable
      rw [PMF.mem_support_bindOnSupport_iff]
      exact ⟨raw, hraw, by simp [next]⟩

/-- Every supported available primitive-machine step strictly advances the
completed-node downset. -/
theorem primitiveMachine_step_support_done_ssubset
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state next : ReachableConfig G}
    {event : (primitiveMachine spec).Event}
    (havailable :
      (primitiveMachine spec).EventAvailable state event)
    (hstep : next ∈ ((primitiveMachine spec).step event state).support) :
    state.1.done ⊂ next.1.done := by
  classical
  cases event with
  | play who action =>
      change CommitAvailable G state.1 who action at havailable
      let step := Classical.choice havailable
      have hstep' := hstep
      change next ∈ (stepPlay G who action state).support at hstep'
      unfold stepPlay at hstep'
      rw [dif_pos havailable] at hstep'
      unfold stepAvailable at hstep'
      rw [PMF.mem_support_bindOnSupport_iff] at hstep'
      rcases hstep' with ⟨rawNext, hrawNext, hnext⟩
      rw [PMF.support_pure, Set.mem_singleton_iff] at hnext
      subst next
      exact
        done_ssubset_of_stepAvailableEvent_support G
          (.commit who action step) hrawNext
  | internal internalEvent =>
      change InternalAvailable G state.1 internalEvent at havailable
      let step := Classical.choice havailable
      have hstep' := hstep
      change next ∈ (stepInternal G internalEvent state).support at hstep'
      unfold stepInternal at hstep'
      rw [dif_pos havailable] at hstep'
      unfold stepAvailable at hstep'
      rw [PMF.mem_support_bindOnSupport_iff] at hstep'
      rcases hstep' with ⟨rawNext, hrawNext, hnext⟩
      rw [PMF.support_pure, Set.mem_singleton_iff] at hnext
      subst next
      exact
        done_ssubset_of_stepAvailableEvent_support G
          (.internal internalEvent step) hrawNext

/-- Available primitive-machine runs never remove completed graph nodes. -/
theorem primitiveMachine_availableRunFrom_done_subset
    {G : Graph P L} (spec : GraphMachineSpec G)
    {source dst : ReachableConfig G}
    {events : List (primitiveMachine spec).Event} :
    (primitiveMachine spec).AvailableRunFrom source events dst →
      source.1.done ⊆ dst.1.done
  | .nil state => by
      intro node hnode
      exact hnode
  | .cons (source := source) (mid := mid) havailable hstep tail =>
      have hhead :
          source.1.done ⊆ mid.1.done :=
        (primitiveMachine_step_support_done_ssubset
          spec havailable hstep).1
      Finset.Subset.trans hhead
        (primitiveMachine_availableRunFrom_done_subset spec tail)

/-- Nonempty available primitive-machine runs strictly advance the completed
graph downset. -/
theorem primitiveMachine_availableRunFrom_done_ssubset_of_ne_nil
    {G : Graph P L} (spec : GraphMachineSpec G)
    {source dst : ReachableConfig G}
    {events : List (primitiveMachine spec).Event} :
    (hrun : (primitiveMachine spec).AvailableRunFrom source events dst) →
      events ≠ [] → source.1.done ⊂ dst.1.done
  | .nil state, hne => False.elim (hne rfl)
  | .cons havailable hstep tail, _hne =>
      Finset.ssubset_of_ssubset_of_subset
        (primitiveMachine_step_support_done_ssubset
          spec havailable hstep)
        (primitiveMachine_availableRunFrom_done_subset spec tail)

private theorem primitiveMachine_step_support_batchStep
    {G : Graph P L} (spec : GraphMachineSpec G)
    {source mid : ReachableConfig G}
    {event : (primitiveMachine spec).Event}
    (havailable : (primitiveMachine spec).EventAvailable source event)
    (hstep : mid ∈ ((primitiveMachine spec).step event source).support) :
    CheckpointStep G source mid := by
  classical
  cases event with
  | play who action =>
      change CommitAvailable G source.1 who action at havailable
      let step := Classical.choice havailable
      let graphEvent : AvailableEvent G source.1 :=
        .commit who action step
      have hstep' := hstep
      change mid ∈ (stepPlay G who action source).support at hstep'
      unfold stepPlay at hstep'
      rw [dif_pos havailable] at hstep'
      unfold stepAvailable at hstep'
      rw [PMF.mem_support_bindOnSupport_iff] at hstep'
      rcases hstep' with ⟨next, hnext, hmid⟩
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmid
      subst hmid
      exact ⟨BatchStep.singleton source graphEvent hnext⟩
  | internal event =>
      change InternalAvailable G source.1 event at havailable
      let step := Classical.choice havailable
      let graphEvent : AvailableEvent G source.1 :=
        .internal event step
      have hstep' := hstep
      change mid ∈ (stepInternal G event source).support at hstep'
      unfold stepInternal at hstep'
      rw [dif_pos havailable] at hstep'
      unfold stepAvailable at hstep'
      rw [PMF.mem_support_bindOnSupport_iff] at hstep'
      rcases hstep' with ⟨next, hnext, hmid⟩
      rw [PMF.support_pure, Set.mem_singleton_iff] at hmid
      subst hmid
      exact ⟨BatchStep.singleton source graphEvent hnext⟩

private theorem checkpointStepOfAvailableRunFrom
    {G : Graph P L} (spec : GraphMachineSpec G)
    {source dst : ReachableConfig G} :
    {events : List (primitiveMachine spec).Event} →
      (primitiveMachine spec).AvailableRunFrom source events dst →
        CheckpointStep G source dst
  | [], .nil state => ⟨BatchStep.nil state⟩
  | _event :: _events, .cons havailable hstep tail => by
      rcases primitiveMachine_step_support_batchStep
          spec havailable hstep with ⟨head⟩
      rcases checkpointStepOfAvailableRunFrom spec tail with ⟨tailStep⟩
      exact ⟨head.append tailStep⟩

/-- A machine-level available run of the EventGraph primitive machine induces
the corresponding graph-level checkpoint batch certificate. -/
theorem checkpointStep_of_availableRunFrom
    {G : Graph P L} (spec : GraphMachineSpec G)
    {source dst : ReachableConfig G}
    {events : List (primitiveMachine spec).Event}
    (hrun : (primitiveMachine spec).AvailableRunFrom source events dst) :
    CheckpointStep G source dst :=
  checkpointStepOfAvailableRunFrom spec hrun

/-- On terminal states, the primitive machine outcome is the compiled payoff
projection. -/
theorem primitiveMachine_outcome_terminal
    {G : Graph P L} (spec : GraphMachineSpec G)
    {state : ReachableConfig G}
    (hterminal : (primitiveMachine spec).terminal state) :
    (primitiveMachine spec).outcome state =
      evalPayoffs? spec.payoffs state.1.store := by
  classical
  change Terminal G state.1 at hterminal
  unfold primitiveMachine
  simp only [hterminal, ↓reduceDIte]
  exact
    (Classical.choose_spec
      (terminalPayoffTotal spec state hterminal)).symm

end ToMachine

end EventGraph

end Vegas
