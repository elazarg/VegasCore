/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Execution

/-! # Compiled source kernels in the graph executor

These laws apply at any ready event whose node is the corresponding compiled
source instruction. The graph may contain other events before or after it;
typed output equality is the only transport required by a suffix embedding.
-/

noncomputable section

namespace Vegas.SourceProgram.EventLowering

open GameTheory.Math.Probability
open Vegas.EventGraph

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- A compiled sample uses the exact source chance law in the shared executor. -/
theorem sample_step {Γ : SourceCtx Player L} {payload : L.Ty}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .publicData payload)
    (refs : ContextRefs graph.layout Γ)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .sample payload (compilePublicDist refs law))
    (state : State L Γ) (agrees : refs.Agrees state config.store) :
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) PUnit.unit) =
      (L.evalDist law (sourcePublicEnv state)).map fun value =>
        config.complete event ready
          (cast (congrArg EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventField.Value outputEq.symm) value) := by
  apply config.step_eq_map_of_code event ready outputEq _ codeEq
  change (compilePublicDist refs law).eval? config.store = _
  rw [PublicDist.eval?, compilePublicDist_evalLaw? refs state config.store agrees law]
  rfl

/-- A compiled commit stores the selected binding, including an unopenable one.
No guard is evaluated at this step. -/
theorem commit_step {owner : Player} {payload : L.Ty}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (binding : PublicationResult (L.Val payload)) :
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) binding) =
      FinDist.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) binding)
        (cast (congrArg EventField.Value outputEq.symm) binding)) := by
  rw [config.step_eq_map_of_code event ready outputEq _ codeEq _
    (FinDist.pure binding) rfl, FinDist.map_pure]

/-- A compiled reveal performs the checks of the obligations the reveal completes
and publishes the accepted result. The completion retains the original
disclosure decision, including a `true` decision whose publication is rejected. -/
theorem reveal_step
    {Γ : SourceCtx Player L} {published : VarId} {owner : Player} {payload : L.Ty}
    {name : VarId}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .publication payload)
    (refs : ContextRefs graph.layout Γ) (revelations : Revelations Γ) (registry : Registry Γ)
    (selected : HasVar Γ name (.commitment owner payload))
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload (refs.get selected)
        (compileChecks (published := published) refs registry revelations selected))
    (state : State L Γ) (refsAgree : refs.Agrees state config.store) (disclose : Bool) :
    let proposal : PublicationResult (L.Val payload) :=
      if disclose then state.get selected else .failure
    let accepted :=
      if (registry.completedBy (published := published) revelations selected).all
          (·.accepts (revelations.reveal (published := published) selected)
            (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
              proposal state))
        then proposal else PublicationResult.failure
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) disclose) =
      FinDist.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm) accepted)) := by
  classical
  dsimp only
  rw [config.step_eq_map_of_code event ready outputEq _ codeEq _ _
    (compileResolve_eval? refs registry revelations state config.store refsAgree selected
      disclose), FinDist.map_pure]

end Vegas.SourceProgram.EventLowering
