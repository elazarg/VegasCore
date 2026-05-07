import Vegas.EventGraph.Basic
import Vegas.Machine.Basic
import Vegas.EventGraph.ToMachine
import Vegas.Core.ToEventGraph
import Vegas.GameBridge.FOSG.FromCore
import Vegas.Core.LinearRead
import Vegas.GameBridge.FOSG.StateSufficiency
import Vegas.GameBridge.FOSG.FrontierStability
import Vegas.Machine.Trace
import Vegas.GameBridge.FOSG.Basic
import Vegas.GameBridge.FOSG.FromEventGraph
import Vegas.Strategic.KernelGame
import Vegas.GameBridge.EFG.FromEventGraph
import Vegas.Backend.Refinement
import Vegas.Backend.KernelGame
import Vegas.GameBridge.FOSG.Kuhn

/-!
# Protocol compatibility entrypoint

This compatibility entrypoint re-exports the executable protocol construction
path under the historical `Vegas.Protocol` umbrella:

`WFProgram -> EventGraph -> Machine -> FOSG view -> KernelGame`.

The ownership modules are now named by semantic layer:

* `Vegas.EventGraph.Basic` is the finite dependency/visibility language for
  protocol transformations. Event nodes are protocol events; configurations
  are extensional partial result assignments with a proof that completed nodes
  are prefix-closed under dependencies. The frontier is computed from that
  assignment.
* `Vegas.Machine.Basic` is the single probabilistic, observation-aware
  execution carrier. Its primitive step is one enabled player move or one
  internal protocol event. Extra implementation state belongs in backend
  refinement, not in the source machine.
* `Vegas.EventGraph.ToMachine` interprets an `EventGraph.Configuration` as
  a `Machine` state. Player steps execute owned frontier nodes with legal write
  slices; internal steps execute non-player frontier nodes.
* `Vegas.Core.ToEventGraph` elaborates checked Vegas programs to an
  `EventGraph` and defines the canonical `eventGraphMachine`.
* `Vegas.GameBridge.FOSG.FromCore` packages the checked-program event graph as
  a FOSG view and proves the finite and legal-observability facts needed by the
  FOSG/Kuhn layer.
* `Vegas.Core.LinearRead` states the programmer-facing straight-line
  reading theorem: scanning source nodes by source rank never gets stuck before
  the event-graph semantics does; a rank-minimal unfinished source node is on the
  executable frontier.
* `Vegas.Machine.Trace` defines the bounded event/state trace distribution
  `Machine.traceDist` and the terminal-outcome marginal
  `Machine.outcomeKernel`. These are the canonical machine-level trace
  semantics.
* `Vegas.GameBridge.FOSG.Basic` derives checkpoint FOSG views directly from `Machine`
  through `Machine.FOSGView`. Worlds are machine states, bounded presentations
  add only a depth counter, and the view owns the player-facing round-action
  alphabet.
* `Vegas.Strategic.KernelGame` packages the finite event-graph FOSG view as
  Vegas `KernelGame` constructors.
* `Vegas.GameBridge.EFG.FromEventGraph` applies the GameTheory
  FOSG-to-augmented-EFG bridge to
  checked programs and proves that the resulting canonical EFG preserves the
  same generated behavioral public-outcome distribution.
* `Vegas.Backend.Refinement` states operational refinement obligations for
  reactive runtimes, including a probability-preserving
  `Machine.StochasticStepRefinement` for backend distribution-preservation
  proofs.
* `Vegas.Backend.KernelGame` packages a backend refinement plus a
  compatible block-law lift as a backend blocked-trace `KernelGame` and
  transports Nash equilibria from the canonical spec blocked-trace game.
* `Vegas.GameBridge.FOSG.Kuhn` exposes `Machine.FOSGView.kuhn_mixed_to_behavioral`,
  a machine-native Kuhn realization theorem. The witness is a
  `Machine.FOSGView.BehavioralProfile`; the equality is between two
  `PMF M.Outcome` distributions. No external syntactic strategy space
  (e.g. `pureKernelGame`) appears in the statement.

Schedulers and linearizations are presentation data for traces, source syntax,
FOSG histories, or backend transaction orderings. They refine machine events
for a particular view; they are not part of `eventGraphMachine`, and scheduled
views must prove that they collapse to the same machine-derived semantics.

The intended theorem is therefore not "machine and every sequential
presentation are definitionally the same"; it is a strategic correspondence
between machine-derived sequential games, the executable machine carrier, and
runtime implementations. The event-graph FOSG carries the finite Kuhn target,
legal-observability proof, and product-mixed Vegas-pure collapse.
-/
