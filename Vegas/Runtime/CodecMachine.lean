/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Runtime.Codec
import Vegas.Machine.Adapter.ToMachine
import Vegas.Machine.Refinement
import Vegas.Machine.RefinementKernelGame

/-!
# Wire-store codec machine

The first concrete rung below `PrimitiveMachine`.

A bare wire store cannot project to `PrimitiveMachine.State`, because primitive
states are reachable graph configurations, not just stores.  This machine uses
the config-shaped design: its state carries the primitive reachable config and a
wire-encoded copy of the config store. The refinement projection erases the
wire layer, while the state invariant records that the wire store encodes the
graph store.
-/

namespace Vegas

namespace Runtime

open EventGraph
open EventGraph.ToMachine

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ValueCodec

/-- Config-shaped runtime state with a wire-encoded copy of the graph store.

The reachable configuration supplies the structural/downset/reachability data
that a bare wire store cannot reconstruct. -/
structure CodecState (codec : ValueCodec L) (G : Graph P L) where
  config : ReachableConfig G
  wireStore : codec.WireStore
  wireStore_eq : wireStore = codec.encodeStore config.1.store

namespace CodecState

variable (codec : ValueCodec L) {G : Graph P L}

/-- Encode a primitive reachable config as a codec state. -/
def encode (config : ReachableConfig G) : CodecState codec G where
  config := config
  wireStore := codec.encodeStore config.1.store
  wireStore_eq := rfl

@[simp] theorem encode_config (config : ReachableConfig G) :
    (encode codec config).config = config := rfl

end CodecState

/-- Machine over codec states. Operationally it follows the primitive machine,
while maintaining a wire-encoded copy of every reached graph store. -/
noncomputable def codecMachine
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G) :
    Machine P where
  State := CodecState codec G
  Action := (primitiveMachine spec).Action
  Internal := (primitiveMachine spec).Internal
  Public := (primitiveMachine spec).Public
  Obs := (primitiveMachine spec).Obs
  Outcome := (primitiveMachine spec).Outcome
  init := CodecState.encode codec (primitiveMachine spec).init
  available := fun state player =>
    (primitiveMachine spec).available state.config player
  availableInternal := fun state =>
    (primitiveMachine spec).availableInternal state.config
  stepPlay := fun player action state =>
    PMF.map (CodecState.encode codec)
      ((primitiveMachine spec).stepPlay player action state.config)
  stepInternal := fun event state =>
    PMF.map (CodecState.encode codec)
      ((primitiveMachine spec).stepInternal event state.config)
  terminal := fun state => (primitiveMachine spec).terminal state.config
  publicView := fun state => (primitiveMachine spec).publicView state.config
  observe := fun player state => (primitiveMachine spec).observe player state.config
  outcome := fun state => (primitiveMachine spec).outcome state.config
  utility := (primitiveMachine spec).utility

/-- Project a codec-machine event to the primitive-machine event it realizes. -/
def projectEvent
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G) :
    (codec.codecMachine spec).Event → (primitiveMachine spec).Event
  | .play player action => .play player action
  | .internal event => .internal event

/-- Project a codec-machine event batch to primitive-machine events. -/
def projectEventBatch
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (events : List (codec.codecMachine spec).Event) :
    List (primitiveMachine spec).Event :=
  events.map (projectEvent codec spec)

/-- Lift a primitive-machine event to the codec machine. -/
def liftEvent
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G) :
    (primitiveMachine spec).Event → (codec.codecMachine spec).Event
  | .play player action => .play player action
  | .internal event => .internal event

/-- Lift a primitive-machine event batch to codec-machine events. -/
def liftEventBatch
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (events : List (primitiveMachine spec).Event) :
    List (codec.codecMachine spec).Event :=
  events.map (liftEvent codec spec)

@[simp] theorem projectEvent_liftEvent
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (event : (primitiveMachine spec).Event) :
    projectEvent codec spec (liftEvent codec spec event) = event := by
  cases event with
  | play player action => rfl
  | internal event => rfl

@[simp] theorem liftEvent_projectEvent
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (event : (codec.codecMachine spec).Event) :
    liftEvent codec spec (projectEvent codec spec event) = event := by
  cases event with
  | play player action => rfl
  | internal event => rfl

@[simp] theorem projectEventBatch_liftEventBatch
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (events : List (primitiveMachine spec).Event) :
    projectEventBatch codec spec (liftEventBatch codec spec events) =
      events := by
  simp [projectEventBatch, liftEventBatch, List.map_map,
    Function.comp_def]

@[simp] theorem liftEventBatch_projectEventBatch
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (events : List (codec.codecMachine spec).Event) :
    liftEventBatch codec spec (projectEventBatch codec spec events) =
      events := by
  simp [projectEventBatch, liftEventBatch, List.map_map,
    Function.comp_def]

/-- One codec-machine step projects to the corresponding primitive-machine
step. -/
theorem step_project
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (event : (codec.codecMachine spec).Event)
    (source : (codec.codecMachine spec).State) :
    PMF.map CodecState.config ((codec.codecMachine spec).step event source) =
      (primitiveMachine spec).step (projectEvent codec spec event)
        source.config := by
  cases event with
  | play player action =>
      change
        PMF.map CodecState.config
            (PMF.map (CodecState.encode codec)
              ((primitiveMachine spec).stepPlay player action source.config)) =
          (primitiveMachine spec).stepPlay player action source.config
      rw [PMF.map_comp]
      exact PMF.map_id _
  | internal event =>
      change
        PMF.map CodecState.config
            (PMF.map (CodecState.encode codec)
              ((primitiveMachine spec).stepInternal event source.config)) =
          (primitiveMachine spec).stepInternal event source.config
      rw [PMF.map_comp]
      exact PMF.map_id _

/-- A primitive event available at the projected state is available as the
corresponding codec-machine event. -/
theorem liftEvent_available
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (state : (codec.codecMachine spec).State)
    {event : (primitiveMachine spec).Event}
    (havailable :
      (primitiveMachine spec).EventAvailable state.config event) :
    (codec.codecMachine spec).EventAvailable state
      (liftEvent codec spec event) := by
  cases event with
  | play player action =>
      exact havailable
  | internal event =>
      exact havailable

/-- Any supported codec successor of a lifted primitive event projects to a
supported primitive successor. -/
theorem step_liftEvent_project_support
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    {state target : (codec.codecMachine spec).State}
    {event : (primitiveMachine spec).Event}
    (htarget :
      target ∈
        ((codec.codecMachine spec).step
          (liftEvent codec spec event) state).support) :
    target.config ∈
      ((primitiveMachine spec).step event state.config).support := by
  have hmap :
      target.config ∈
        (PMF.map CodecState.config
          ((codec.codecMachine spec).step
            (liftEvent codec spec event) state)).support := by
    exact
      (PMF.mem_support_map_iff _ _ _).mpr
        ⟨target, htarget, rfl⟩
  rw [ValueCodec.step_project codec spec
    (liftEvent codec spec event) state] at hmap
  simp only [projectEvent_liftEvent] at hmap
  exact hmap

/-- A primitive available batch lifts to a support-wide available codec batch. -/
theorem liftEventBatch_availableBatchFrom
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    {events : List (primitiveMachine spec).Event}
    {state : (codec.codecMachine spec).State}
    (hbatch :
      (primitiveMachine spec).AvailableBatchFrom state.config events) :
    (codec.codecMachine spec).AvailableBatchFrom state
      (liftEventBatch codec spec events) := by
  induction events generalizing state with
  | nil =>
      trivial
  | cons event events ih =>
      exact
        Machine.AvailableBatchFrom.cons
          (liftEvent_available codec spec state hbatch.1)
          (by
            intro mid hmid
            exact ih
              (hbatch.2 mid.config
                (step_liftEvent_project_support codec spec hmid)))

/-- Running a codec-machine event batch projects to running the corresponding
primitive-machine event batch. -/
theorem runEventsFrom_project
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (events : List (codec.codecMachine spec).Event)
    (source : (codec.codecMachine spec).State) :
    PMF.map CodecState.config
        ((codec.codecMachine spec).runEventsFrom events source) =
      (primitiveMachine spec).runEventsFrom
        (projectEventBatch codec spec events) source.config := by
  induction events generalizing source with
  | nil =>
      change PMF.map CodecState.config (PMF.pure source) =
        PMF.pure source.config
      rw [PMF.pure_map]
  | cons event events ih =>
      rw [Machine.runEventsFrom_cons_bind]
      change
        PMF.map CodecState.config
            (PMF.bind ((codec.codecMachine spec).step event source)
              (fun current =>
                (codec.codecMachine spec).runEventsFrom events current)) =
          (primitiveMachine spec).runEventsFrom
            (projectEventBatch codec spec (event :: events)) source.config
      rw [PMF.map_bind]
      simp_rw [ih]
      change
        ((codec.codecMachine spec).step event source).bind
            ((fun specState =>
                (primitiveMachine spec).runEventsFrom
                  (projectEventBatch codec spec events) specState) ∘
              CodecState.config) =
          (primitiveMachine spec).runEventsFrom
            (projectEventBatch codec spec (event :: events)) source.config
      calc
        ((codec.codecMachine spec).step event source).bind
            ((fun specState =>
                (primitiveMachine spec).runEventsFrom
                  (projectEventBatch codec spec events) specState) ∘
              CodecState.config)
            =
          (PMF.map CodecState.config
              ((codec.codecMachine spec).step event source)).bind
            (fun specState =>
              (primitiveMachine spec).runEventsFrom
                (projectEventBatch codec spec events) specState) := by
              exact
                (PMF.bind_map
                  ((codec.codecMachine spec).step event source)
                  CodecState.config
                  (fun specState =>
                    (primitiveMachine spec).runEventsFrom
                      (projectEventBatch codec spec events) specState)).symm
        _ =
          ((primitiveMachine spec).step
              (projectEvent codec spec event) source.config).bind
            (fun specState =>
              (primitiveMachine spec).runEventsFrom
                (projectEventBatch codec spec events) specState) := by
              exact
                congrArg
                  (fun law =>
                    law.bind fun specState =>
                      (primitiveMachine spec).runEventsFrom
                        (projectEventBatch codec spec events) specState)
                  (ValueCodec.step_project codec spec event source)
        _ =
          (primitiveMachine spec).runEventsFrom
            (projectEventBatch codec spec (event :: events)) source.config := by
              simp [projectEventBatch, projectEvent,
                Machine.runEventsFrom_cons_bind]

/-- The codec machine refines the primitive machine by erasing the wire-store
layer. -/
noncomputable def refinement
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G) :
    Machine.StochasticRefinement (codec.codecMachine spec)
      (primitiveMachine spec) where
  projectState := CodecState.config
  projectEvent? := fun event => some (projectEvent codec spec event)
  projectEventBatch := projectEventBatch codec spec
  projectPublic := id
  projectObs := fun _ => id
  projectOutcome := id
  init_project := rfl
  available_project := by
    intro state event specEvent havailable hproject
    cases event with
    | play player action =>
        injection hproject with heq
        cases heq
        exact havailable
    | internal event =>
        injection hproject with heq
        cases heq
        exact havailable
  step_project := by
    intro event source
    exact ValueCodec.step_project codec spec event source
  eventBatch_project := by
    intro events source
    exact runEventsFrom_project codec spec events source
  publicView_project := by
    intro state
    rfl
  observe_project := by
    intro player state
    rfl
  terminal_project := by
    intro state hterminal
    exact hterminal
  terminal_reflect := by
    intro state hterminal
    exact hterminal
  outcome_project := by
    intro state
    change Option.map id ((primitiveMachine spec).outcome state.config) =
      (primitiveMachine spec).outcome state.config
    simp
  utility_project := by
    intro outcome player
    rfl

/-- Lift a primitive event-batch law through the codec refinement. The law is
sampled on the projected primitive trace; sampled primitive batches are then
encoded as codec-machine batches. -/
noncomputable def liftEventBatchLaw
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (law : (primitiveMachine spec).EventBatchLaw) :
    (codec.codecMachine spec).EventBatchLaw :=
  fun trace =>
    PMF.map (liftEventBatch codec spec)
      (law ((refinement codec spec).projectEventBatchTrace trace))

/-- Lifted codec laws preserve support-wide batch legality. -/
theorem liftEventBatchLaw_legal
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    {law : (primitiveMachine spec).EventBatchLaw}
    (hlegal : (primitiveMachine spec).IsLegalEventBatchLaw law) :
    (codec.codecMachine spec).IsLegalEventBatchLaw
      (liftEventBatchLaw codec spec law) := by
  intro trace hnonterminal batch hbatch
  unfold liftEventBatchLaw at hbatch
  rcases (PMF.mem_support_map_iff _ _ _).mp hbatch with
    ⟨specBatch, hspecBatch, hbatchEq⟩
  subst batch
  have hspecNonterminal :
      ¬ (primitiveMachine spec).terminal
        ((refinement codec spec).projectEventBatchTrace trace).2 := by
    intro hterminal
    exact hnonterminal
      ((refinement codec spec).terminal_reflect hterminal)
  exact
    liftEventBatch_availableBatchFrom codec spec
      (hlegal ((refinement codec spec).projectEventBatchTrace trace)
        hspecNonterminal hspecBatch)

/-- The lifted codec law is compatible with the primitive law under the codec
refinement. -/
theorem liftEventBatchLaw_compatible
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    (law : (primitiveMachine spec).EventBatchLaw) :
    (refinement codec spec).EventBatchLawCompatible
      (liftEventBatchLaw codec spec law) law := by
  intro trace
  unfold liftEventBatchLaw
  rw [PMF.map_comp]
  change
    PMF.map
        (fun batch =>
          projectEventBatch codec spec (liftEventBatch codec spec batch))
        (law ((refinement codec spec).projectEventBatchTrace trace)) =
      law ((refinement codec spec).projectEventBatchTrace trace)
  simp only [projectEventBatch_liftEventBatch]
  change
    PMF.map id (law ((refinement codec spec).projectEventBatchTrace trace)) =
      law ((refinement codec spec).projectEventBatchTrace trace)
  rw [PMF.map_id]

/-- Lift a strategy-indexed primitive event-batch law family through the codec
refinement. -/
noncomputable def liftEventBatchLawFamily
    (codec : ValueCodec L) {G : Graph P L} (spec : GraphMachineSpec G)
    {Strategy : P → Type}
    (family : (primitiveMachine spec).EventBatchLawFamily Strategy) :
    (refinement codec spec).EventBatchLawFamilyLift Strategy family where
  impl :=
    { law := fun profile =>
        liftEventBatchLaw codec spec (family.law profile)
      legal := fun profile =>
        liftEventBatchLaw_legal codec spec (family.legal profile) }
  compatible := fun profile =>
    liftEventBatchLaw_compatible codec spec (family.law profile)

end ValueCodec

end Runtime

end Vegas
