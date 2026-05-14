import Vegas.Core.ToEventGraph

/-!
# Checked-Program Visibility

Observation-locality facts that depend on the `VegasCore` visibility
discipline and generated commit guards.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

attribute [local instance] EventGraph.nodeDecEq
attribute [local instance] EventGraph.fieldDecEq

/-- Visible reads of a generated commit guard are fields visible to the
committing player. -/
theorem programEventGraph_commit_guard_visibleReads_visible
    (g : WFProgram P L)
    {node : ProgramNode g.prog}
    {owner : P} {target : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (fun field => field.ty) target}
    (hsem :
      ProgramNode.sem g.obligations node =
        EventGraph.NodeSem.commit owner target guard) :
    ∀ read, read ∈ guard.visibleReads → read.VisibleTo owner :=
  ProgramNode.guard_visibleReads_owner_of_sem_commit
    g.obligations node hsem

/-- Player action availability in a generated event graph is determined by the
public transcript and the acting player's private observation. -/
theorem programEventGraph_available_eq_of_observation_eq
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hpriv : eventGraphObserve g who left = eventGraphObserve g who right)
    (hpub : eventGraphPublicView g left = eventGraphPublicView g right) :
    EventGraph.available (programEventGraph g) left who =
      EventGraph.available (programEventGraph g) right who :=
  eventGraph_available_eq_of_observation_eq g who hpriv hpub

end Vegas
