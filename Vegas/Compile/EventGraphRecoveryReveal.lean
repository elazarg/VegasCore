/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphStep
import Vegas.Source.RegistryFailureExtension

/-! # Compiled reveal kernels after automatic excluded commitment slots -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Static guard obligations for automatically failed slots have no effect on
an actual compiled reveal. Its publication is exactly the source successor's. -/
theorem reveal_step_of_failureExtension
    {Γ : SourceCtx Player L} {published name : VarId} {owner : Player} {payload : L.Ty}
    (config : graph.Config) (event : graph.EventId) (ready : config.cut.Ready event)
    (outputEq : graph.outputLayout event = .publication payload)
    (refs : ContextRefs graph.layout Γ) (sourceConfig : SourceProgram.Config Player L Γ)
    (registry : Registry Γ) (source : HasVar Γ name (.commitment owner payload))
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload (refs.get source)
        (compileChecks (published := published) refs registry sourceConfig.revelations source))
    (agree : refs.Agrees sourceConfig.state config.store)
    (valid : Registry.FailureExtension sourceConfig.registry registry sourceConfig.state)
    (failures : Revelations.PreservesFailures sourceConfig.revelations sourceConfig.state)
    (unique : (Γ.map Prod.fst).Nodup) (disclose : Bool) :
    config.step event ready (cast (congrArg EventField.Action outputEq.symm) disclose) =
      PMF.pure (config.complete event ready
        (cast (congrArg EventField.Action outputEq.symm) disclose)
        (cast (congrArg EventField.Value outputEq.symm)
          ((revealSuccessor published source sourceConfig disclose).state.get .here))) := by
  have checks := valid.completedBy_all_eq sourceConfig.revelations failures unique source
    (published := published) disclose
  rw [reveal_step config event ready outputEq refs sourceConfig.revelations registry source
    codeEq sourceConfig.state agree disclose]
  dsimp only at checks
  dsimp only [revealSuccessor, Env.cons_get_here]
  rw [checks]

end Vegas
