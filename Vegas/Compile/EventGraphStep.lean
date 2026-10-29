/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Compile.EventGraphEvaluation
import Vegas.EventGraph.Execution

/-! # Compiled source kernels in the graph executor

These laws apply at any ready event whose node is the corresponding compiled
source instruction. The graph may contain other events before or after it;
typed output equality is the only transport required by a suffix embedding.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability
open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]
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

/-- A compiled commit stores an admitted binding, including an unopenable one.
Omission and automatic completion store failure without evaluating a guard. -/
theorem commit_step {owner : Player} {payload : L.Ty}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (choice : Option (PublicationResult (L.Val payload))) :
    let effective := if owner ∈ config.defaulted then none else choice
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) choice) =
      PMF.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) choice)
        (cast (congrArg EventField.Value outputEq.symm) (effective.getD .failure))) := by
  dsimp only
  rw [config.step_eq_map_of_code event ready outputEq _ codeEq _
    (PMF.pure ((if owner ∈ config.defaulted then none else choice).getD .failure)) rfl,
    PMF.pure_map]

/-- A compiled reveal performs the checks of the obligations the reveal completes
and publishes the accepted result. Active completions retain the original
disclosure decision, including a `true` decision whose publication is rejected;
automatic completions retain no strategic decision. -/
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
    let effective := if owner ∈ config.defaulted then false else disclose
    let proposal : PublicationResult (L.Val payload) :=
      if effective then state.get selected else .failure
    let accepted :=
      if (registry.completedBy (published := published) revelations selected).all
          (·.accepts (revelations.reveal (published := published) selected)
            (Env.cons (Val := CellVal (Player := Player) L) (τ := .publication payload)
              proposal state))
        then proposal else PublicationResult.failure
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) disclose) =
      PMF.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm) accepted)) := by
  classical
  dsimp only
  rw [config.step_eq_map_of_code event ready outputEq _ codeEq _ _
    (compileResolve_eval? refs registry revelations state config.store refsAgree selected
      (if owner ∈ config.defaulted then false else disclose)), PMF.pure_map]

end Vegas
