import Vegas.Runtime.Codec
import Vegas.Machine.Adapter.ToMachine
import Vegas.Machine.Refinement

/-!
# Wire-store codec machine

The first concrete rung below `PrimitiveMachine`.

A bare wire store cannot project to `PrimitiveMachine.State`, because primitive
states are reachable graph configurations, not just stores.  This machine uses
the config-shaped design: its state carries the primitive reachable config and a
wire-encoded copy of the config store.  The refinement projection erases the
wire layer; the codec round-trip laws prove the wire store is the encoded form
of the graph store.
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

/-- Decoding the wire store stored in a codec state recovers the projected
primitive graph store. -/
theorem decode_wireStore (state : CodecState codec G) :
    codec.decodeStore state.wireStore = state.config.1.store := by
  rw [state.wireStore_eq]
  exact codec.decodeStore_encodeStore state.config.1.store

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
    simpa using ValueCodec.step_project codec spec event source
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

end ValueCodec

end Runtime

end Vegas
