import Vegas.Protocol.ActionGraph
import Vegas.Protocol.Machine
import Vegas.Protocol.FOSG
import Vegas.Protocol.Checked
import Vegas.Protocol.Backend
import Vegas.Protocol.Kuhn

/-!
# Protocol semantics

This entrypoint exposes the executable protocol construction path.

* `Vegas.Protocol.ActionGraph` is the finite dependency/visibility language for
  protocol transformations. It contains the Lean port of the useful
  action-DAG/frontier abstractions from `../vegas`: action metadata,
  reachability queries, redacted history, frontier configurations, play/quit
  labels, and structural label legality. Runtime configurations use bounded
  histories, so the graph machine state is finite when the action, field, and
  value carriers are finite. The Lean carrier is proof-carrying; the Kotlin
  prototype is design input, not an unproved specification.
* `Vegas.Protocol.Machine` is the single probabilistic, observation-aware
  execution carrier. Its primitive step is one enabled player move or one
  internal protocol event. `ActionGraph.Semantics.toMachine` is the direct
  source denotation: its state is exactly `ActionGraph.Configuration`, player
  steps merge one frontier packet, and the sole internal event finalizes the
  current frontier. Extra implementation state belongs in backend refinement,
  not in the source machine.
* `Vegas.Protocol.FOSG` derives sequential FOSG views directly from
  `Machine` through `Machine.FOSGView`, using `Machine.RunPrefix` event/state
  prefixes as worlds. `Machine.FOSGView.transition_map_lastState_eq_step`
  projects each derived FOSG transition back to the selected `Machine.step`.
* `Vegas.Protocol.Checked` elaborates checked syntax to
  `syntaxActionGraph`, interprets it with `graphSemantics`, and
  exposes `graphMachine` plus `graphMachineFOSG`. Available
  graph steps are proved to project to the corresponding checked cursor
  transition, so the cursor evaluator remains a proof tool rather than a second
  machine semantics.
* `Vegas.Protocol.Backend` states operational refinement obligations for
  reactive runtimes, including a probability-preserving
  `Machine.StochasticStepRefinement` for backend distribution-preservation
  proofs.
* `Vegas.Protocol.Kuhn` exposes `Machine.FOSGView.kuhn_mixed_to_behavioral`,
  a machine-native Kuhn realization theorem. The witness is a
  `Machine.FOSGView.BehavioralProfile`; the equality is between two
  `PMF M.Outcome` distributions. No external syntactic strategy space
  (e.g. `toStrategicKernelGame`) appears in the statement.

`Vegas.FOSG` exposes `FOSGBridge.toGraphFOSG` and
`FOSGBridge.toFiniteGraphMachineFOSG` as the graph-machine sequential views;
`FOSGBridge.toFOSG` is an alias for the same carrier.
`FOSGBridge.toObservedFOSG` is the finite cursor-world adapter used for
syntax-facing projection proofs, not a semantic owner.

Schedulers and linearizations are presentation data for traces, sequential
syntax, FOSG histories, or backend transaction orderings. They refine machine
events for a particular view; they are not part of
`ActionGraph.Semantics.toMachine`, and scheduled views must prove that
they collapse to the same machine-derived semantics.

The intended theorem is therefore not "machine and every sequential
presentation are definitionally the same"; it is a strategic correspondence
between machine-derived sequential games, the executable machine carrier, and
runtime implementations. The graph-machine FOSG carries the finite Kuhn target,
legal-observability proof, and product-mixed Vegas-pure collapse; the remaining
large step is the backend refinement/bisimulation theorem for a concrete
runtime.
-/
