import Vegas.Protocol.Graph
import Vegas.Protocol.Machine
import Vegas.Protocol.GraphMachine
import Vegas.Protocol.SyntaxGraph
import Vegas.Protocol.StateSufficiency
import Vegas.Protocol.Trace
import Vegas.Protocol.FOSG
import Vegas.Protocol.Strategic
import Vegas.Protocol.Backend
import Vegas.Protocol.Kuhn

/-!
# Protocol semantics

This entrypoint exposes the executable protocol construction path:

`WFProgram -> ProtocolGraph -> Machine -> FOSG view -> KernelGame`.

* `Vegas.Protocol.Graph` is the finite dependency/visibility language for
  protocol transformations. Graph nodes are protocol events; configurations
  are extensional partial result assignments with a proof that completed nodes
  are prefix-closed under dependencies. The frontier is computed from that
  assignment.
* `Vegas.Protocol.Machine` is the single probabilistic, observation-aware
  execution carrier. Its primitive step is one enabled player move or one
  internal protocol event. Extra implementation state belongs in backend
  refinement, not in the source machine.
* `Vegas.Protocol.GraphMachine` interprets a `ProtocolGraph.Configuration` as
  a `Machine` state. Player steps execute owned frontier nodes with legal write
  slices; internal steps execute non-player frontier nodes.
* `Vegas.Protocol.SyntaxGraph` compiles checked Vegas syntax to a
  `ProtocolGraph`, defines the canonical `syntaxGraphMachine`, and proves the
  finite and legal-observability facts needed by the FOSG/Kuhn layer.
* `Vegas.Protocol.Trace` defines the bounded event/state trace distribution
  `Machine.traceDist` and the terminal-outcome marginal
  `Machine.outcomeKernel`. These are the canonical machine-level trace
  semantics.
* `Vegas.Protocol.FOSG` derives checkpoint FOSG views directly from `Machine`
  through `Machine.FOSGView`. Worlds are machine states, bounded presentations
  add only a depth counter, and the view owns the player-facing round-action
  alphabet.
* `Vegas.Protocol.Strategic` packages the finite syntax-graph FOSG view as
  Vegas `KernelGame` constructors.
* `Vegas.Protocol.Backend` states operational refinement obligations for
  reactive runtimes, including a probability-preserving
  `Machine.StochasticStepRefinement` for backend distribution-preservation
  proofs.
* `Vegas.Protocol.Kuhn` exposes `Machine.FOSGView.kuhn_mixed_to_behavioral`,
  a machine-native Kuhn realization theorem. The witness is a
  `Machine.FOSGView.BehavioralProfile`; the equality is between two
  `PMF M.Outcome` distributions. No external syntactic strategy space
  (e.g. `pureKernelGame`) appears in the statement.

Schedulers and linearizations are presentation data for traces, source syntax,
FOSG histories, or backend transaction orderings. They refine machine events
for a particular view; they are not part of `syntaxGraphMachine`, and scheduled
views must prove that they collapse to the same machine-derived semantics.

The intended theorem is therefore not "machine and every sequential
presentation are definitionally the same"; it is a strategic correspondence
between machine-derived sequential games, the executable machine carrier, and
runtime implementations. The syntax-graph FOSG carries the finite Kuhn target,
legal-observability proof, and product-mixed Vegas-pure collapse.
-/
