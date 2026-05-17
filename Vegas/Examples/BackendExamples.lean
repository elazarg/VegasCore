import Vegas.Backend.Refinement
import Vegas.Examples.SyntaxConstructors

/-!
# Backend refinement examples

Tiny backend-facing examples. The identity backend is intentionally boring:
it checks that the refinement and trace-projection API is usable before a
real runtime supplies its own state/event representation.
-/

namespace Vegas
namespace Examples
namespace BackendExamples

namespace IdentityBackend

variable {P : Type} (M : Vegas.Machine P)

theorem refl_projectEventBatch (batch : List M.Event) :
    (((Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).projectEventBatch batch)) =
      batch := by
  exact Vegas.Machine.StochasticStepRefinement.refl_projectEventBatch M batch

theorem refl_projectEventBatchTrace (trace : M.EventBatchTrace) :
    (((Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).projectEventBatchTrace trace)) =
      trace := by
  exact Vegas.Machine.StochasticStepRefinement.refl_projectEventBatchTrace M trace

theorem refl_eventBatchLawCompatible (law : M.EventBatchLaw) :
    (Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).EventBatchLawCompatible law law := by
  exact Vegas.Machine.StochasticStepRefinement.refl_eventBatchLawCompatible M law

theorem refl_eventBatchTraceDist_project_eq
    (law : M.EventBatchLaw) (horizon : Nat) (trace : M.EventBatchTrace) :
    PMF.map
        (Vegas.Machine.StochasticStepRefinement.refl M :
          Vegas.Machine.StochasticStepRefinement M M).projectEventBatchTrace
        (M.eventBatchTraceDistFrom law horizon trace) =
      M.eventBatchTraceDistFrom law horizon trace := by
  let R : Vegas.Machine.StochasticStepRefinement M M :=
    Vegas.Machine.StochasticStepRefinement.refl M
  simpa [R] using
    Vegas.Machine.StochasticStepRefinement.eventBatchTraceDist_project_eq
      R law law
      (Vegas.Machine.StochasticStepRefinement.refl_eventBatchLawCompatible M law)
      horizon trace

end IdentityBackend

noncomputable abbrev syntaxConstructorIdentityBackend :
    Machine.StochasticStepRefinement
      (eventGraphMachine SyntaxConstructors.game)
      (eventGraphMachine SyntaxConstructors.game) :=
  Machine.StochasticStepRefinement.refl
    (eventGraphMachine SyntaxConstructors.game)

theorem syntaxConstructorIdentityBackend_traceProjection
    (law : (eventGraphMachine SyntaxConstructors.game).EventBatchLaw)
    (horizon : Nat)
    (trace : (eventGraphMachine SyntaxConstructors.game).EventBatchTrace) :
    PMF.map syntaxConstructorIdentityBackend.projectEventBatchTrace
        ((eventGraphMachine SyntaxConstructors.game).eventBatchTraceDistFrom
          law horizon trace) =
      (eventGraphMachine SyntaxConstructors.game).eventBatchTraceDistFrom
        law horizon trace :=
  IdentityBackend.refl_eventBatchTraceDist_project_eq
    (eventGraphMachine SyntaxConstructors.game) law horizon trace

end BackendExamples
end Examples
end Vegas
