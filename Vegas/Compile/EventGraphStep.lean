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

/-- A compiled commit stores the selected bound value, including an unopenable
binding. No guard is evaluated at this step. -/
theorem commit_step {owner : Player} {payload : L.Ty}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (binding : BoundValue (L.Val payload)) :
    let choice := BoundValue.resultEquiv _ binding
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) choice) =
      FinDist.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) choice)
        (cast (congrArg EventField.Value outputEq.symm) choice)) := by
  dsimp only
  rw [config.step_eq_map_of_code event ready outputEq _ codeEq _
    (FinDist.pure (BoundValue.resultEquiv _ binding)) rfl, FinDist.map_pure]

/-- A compiled reveal executes the source's tentative validation and publishes
its accepted result. The completion retains the original disclosure decision,
including a `true` decision rejected by the retained guard registry. -/
theorem reveal_step
    {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty} {name : VarId}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .publication payload)
    (refs : ContextRefs graph.layout Γ) (publications : PublicationRefs graph.layout Γ)
    (unique : (Γ.map Prod.fst).Nodup) (registry : Registry Γ)
    (selected : HasVar Γ name (.privateData owner payload))
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload (refs.get selected)
        (registry.map (compileGuard refs (proposedOperands publications unique selected))))
    (state : State L Γ) (refsAgree : refs.Agrees state config.store)
    (publicationsAgree : publications.Agree state config.store) (disclose : Bool) :
    let proposed := boundResult state selected disclose
    let accepted := if registry.ok (updatePrivate state selected (resultPublication proposed))
      then proposed else PublicationResult.failure
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) disclose) =
      FinDist.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm) accepted)) := by
  classical
  dsimp only
  rw [config.step_eq_map_of_code event ready outputEq _ codeEq _ _
    (compileResolve_eval? refs publications unique registry state config.store
      refsAgree publicationsAgree selected disclose), FinDist.map_pure]

end Vegas.SourceProgram.EventLowering
