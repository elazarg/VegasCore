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

theorem refl_projectEventBlock (block : List M.Event) :
    (((Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).projectEventBlock block)) =
      block := by
  exact Vegas.Machine.StochasticStepRefinement.refl_projectEventBlock M block

theorem refl_projectBlockTrace (trace : M.BlockTrace) :
    (((Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).projectBlockTrace trace)) =
      trace := by
  exact Vegas.Machine.StochasticStepRefinement.refl_projectBlockTrace M trace

theorem refl_blockLawCompatible (law : M.BlockLaw) :
    (Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).BlockLawCompatible law law := by
  exact Vegas.Machine.StochasticStepRefinement.refl_blockLawCompatible M law

theorem refl_blockTraceDist_project_eq
    (law : M.BlockLaw) (horizon : Nat) (trace : M.BlockTrace) :
    PMF.map
        (Vegas.Machine.StochasticStepRefinement.refl M :
          Vegas.Machine.StochasticStepRefinement M M).projectBlockTrace
        (M.blockTraceDistFrom law horizon trace) =
      M.blockTraceDistFrom law horizon trace := by
  let R : Vegas.Machine.StochasticStepRefinement M M :=
    Vegas.Machine.StochasticStepRefinement.refl M
  simpa [R] using
    Vegas.Machine.StochasticStepRefinement.blockTraceDist_project_eq
      R law law
      (Vegas.Machine.StochasticStepRefinement.refl_blockLawCompatible M law)
      horizon trace

end IdentityBackend

noncomputable abbrev syntaxConstructorIdentityBackend :
    Machine.StochasticStepRefinement
      (eventGraphMachine SyntaxConstructors.game)
      (eventGraphMachine SyntaxConstructors.game) :=
  Machine.StochasticStepRefinement.refl
    (eventGraphMachine SyntaxConstructors.game)

theorem syntaxConstructorIdentityBackend_traceProjection
    (law : (eventGraphMachine SyntaxConstructors.game).BlockLaw)
    (horizon : Nat)
    (trace : (eventGraphMachine SyntaxConstructors.game).BlockTrace) :
    PMF.map syntaxConstructorIdentityBackend.projectBlockTrace
        ((eventGraphMachine SyntaxConstructors.game).blockTraceDistFrom
          law horizon trace) =
      (eventGraphMachine SyntaxConstructors.game).blockTraceDistFrom
        law horizon trace :=
  IdentityBackend.refl_blockTraceDist_project_eq
    (eventGraphMachine SyntaxConstructors.game) law horizon trace

end BackendExamples
end Examples
end Vegas
