import Vegas.Compile.Checkpoint

/-!
# EventGraph progress facts

Bare graph well-formedness is a safety condition.  Progress needs liveness of
commit guards: every live ready commit guard has at least one legal value.
Checked programs provide that guard liveness from source `Legal`.
-/

namespace Vegas

namespace EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- A well-formed graph with live commit guards has an executable primitive
event at every reachable nonterminal state. -/
theorem availableEvent_progress_of_guardLive
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G) :
    AvailableEventProgress G :=
  availableEventProgress_of_guardLive hwf hguards

/-- A well-formed graph with live commit guards has primitive downset
checkpoint progress. -/
theorem downset_progress_of_guardLive
    {G : Graph Player L} (hwf : G.WF) (hguards : GuardLive G) :
    DownsetProgress G :=
  primitiveDownsetProgress_of_availableEventProgress
    (availableEventProgress_of_guardLive hwf hguards)

end EventGraph

namespace WFProgram

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Checked source guard legality supplies the guard liveness needed for
compiled graph progress. -/
theorem compiledGraph_progress_guardLive
    (program : WFProgram P L) :
    EventGraph.GuardLive (ToEventGraph.compile program.core).graph :=
  ToEventGraph.compile_guardLive program

/-- The primitive downset checkpoint model of a checked program has at least
one allowed successor at every reachable nonterminal checkpoint. -/
theorem primitiveDownsetCheckpoint_progress
    (program : WFProgram P L)
    {state : (ToEventGraph.primitiveDownsetCheckpointModel program).State}
    (hterminal :
      ¬ (ToEventGraph.primitiveDownsetCheckpointModel program).terminal
        state) :
    ∃ dst,
      (ToEventGraph.primitiveDownsetCheckpointModel program).allowed
        state dst :=
  (ToEventGraph.primitiveDownsetCheckpointModel program)
    |>.nonterminal_exists_allowed hterminal

end WFProgram

end Vegas
