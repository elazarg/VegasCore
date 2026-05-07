import Vegas.Protocol.Backend
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
  simp [Vegas.Machine.StochasticStepRefinement.projectEventBlock,
    Vegas.Machine.StochasticStepRefinement.refl]

theorem refl_projectBlockTrace (trace : M.BlockTrace) :
    (((Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).projectBlockTrace trace)) =
      trace := by
  cases trace with
  | mk blocks state =>
      change
        (blocks.map
            (Vegas.Machine.StochasticStepRefinement.refl M :
              Vegas.Machine.StochasticStepRefinement M M).projectEventBlock,
          state) = (blocks, state)
      congr
      induction blocks with
      | nil => simp
      | cons block blocks ih =>
          simpa [ih] using refl_projectEventBlock M block

theorem refl_blockLawCompatible (law : M.BlockLaw) :
    (Vegas.Machine.StochasticStepRefinement.refl M :
      Vegas.Machine.StochasticStepRefinement M M).BlockLawCompatible law law := by
  intro trace
  rw [refl_projectBlockTrace]
  have hblock :
      (fun block : List M.Event =>
        (Vegas.Machine.StochasticStepRefinement.refl M :
          Vegas.Machine.StochasticStepRefinement M M).projectEventBlock block) = id := by
    funext block
    exact refl_projectEventBlock M block
  change PMF.map
      (fun block : List M.Event =>
        (Vegas.Machine.StochasticStepRefinement.refl M :
          Vegas.Machine.StochasticStepRefinement M M).projectEventBlock block)
      (law trace) = law trace
  rw [hblock]
  exact PMF.map_id (law trace)

theorem refl_blockTraceDist_project_eq
    (law : M.BlockLaw) (horizon : Nat) (trace : M.BlockTrace) :
    PMF.map
        (Vegas.Machine.StochasticStepRefinement.refl M :
          Vegas.Machine.StochasticStepRefinement M M).projectBlockTrace
        (M.blockTraceDistFrom law horizon trace) =
      M.blockTraceDistFrom law horizon trace := by
  let R : Vegas.Machine.StochasticStepRefinement M M :=
    Vegas.Machine.StochasticStepRefinement.refl M
  have hproject := Vegas.Machine.StochasticStepRefinement.blockTraceDist_project_eq
    R law law (refl_blockLawCompatible M law) horizon trace
  have htrace : R.projectBlockTrace = id := by
    funext trace
    exact refl_projectBlockTrace M trace
  simpa [R, htrace] using hproject

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
