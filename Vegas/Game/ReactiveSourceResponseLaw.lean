/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ReactiveSourceResponseRecall

/-! # Genuine source-recall coupling through prescribed responses -/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The actual behavioral response and its reconstructed source past have the
joint law obtained by retaining the original private posterior and sampling one
authentic response. No source history or traffic-factor equality is assumed. -/
theorem prescribedReactivePolicy_source_recall_response_law
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (whole : SourceProgram Player L Γ names)
    (runtime : EventGraphRuntime (toEventGraph whole))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (toEventGraph whole)))
    (who : Player) (policy : (toEventGraph whole).BehavioralPolicy who)
    (execution : (runtime.reactiveApplication leaks).Execution)
    (consistent : (runtime.prescribedReactivePolicy leaks who policy).Consistent
      (execution.recall who)) :
    (runtime.prescribedReactivePolicy leaks who policy (execution.recall who)
      (execution.observe (runtime.reactiveApplication leaks) who)).bind (fun action =>
        let next := execution.respond (runtime.reactiveApplication leaks) who action
        ((runtime.prescribedReactiveImplementation leaks who policy).posterior
          (next.recall who)).map fun intentions =>
            (next, originalReactiveSourceRecall whole runtime leaks who next intentions)) =
      ((runtime.prescribedReactiveImplementation leaks who policy).posterior
        (execution.recall who)).bind fun intentions =>
          (runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
            (execution.observe (runtime.reactiveApplication leaks) who)).map fun response =>
              (execution.respond (runtime.reactiveApplication leaks) who response.1,
                originalReactiveSourceRecall whole runtime leaks who execution intentions) := by
  have realized := (runtime.prescribedReactiveImplementation leaks who policy).response_disintegrate
    execution who (fun next intentions => PMF.pure
      (next, originalReactiveSourceRecall whole runtime leaks who next intentions))
  have actual :
      (runtime.prescribedReactivePolicy leaks who policy (execution.recall who)
        (execution.observe (runtime.reactiveApplication leaks) who)).bind (fun action =>
          let next := execution.respond (runtime.reactiveApplication leaks) who action
          ((runtime.prescribedReactiveImplementation leaks who policy).posterior
            (next.recall who)).map fun intentions =>
              (next, originalReactiveSourceRecall whole runtime leaks who next intentions)) =
        ((runtime.prescribedReactiveImplementation leaks who policy).posterior
          (execution.recall who)).bind fun intentions =>
            ((runtime.prescribedReactiveImplementation leaks who policy).respond intentions
              (execution.recall who, execution.observe (runtime.reactiveApplication leaks) who)).map
                fun response =>
                  (execution.respond (runtime.reactiveApplication leaks) who response.1,
                    originalReactiveSourceRecall whole runtime leaks who
                      (execution.respond (runtime.reactiveApplication leaks) who response.1)
                      response.2) := realized.symm
  rw [actual]
  apply bind_congr_on_support
  intro intentions memorySupported
  change ((runtime.prescribedReactiveResponse leaks who policy (execution.recall who) intentions
    (execution.observe (runtime.reactiveApplication leaks) who)).map
      (fun response => (response.1, intentions ++ [response.2]))).map _ = _
  rw [PMF.map_comp]
  apply map_congr_on_support
  intro response supported
  apply Prod.ext
  · rfl
  · have aligned := (runtime.prescribedReactivePosterior_length leaks who policy consistent
      intentions memorySupported).symm
    exact originalReactiveSourceRecall_respond whole runtime leaks who policy execution intentions
      aligned response.1 response.2 supported

end Vegas
