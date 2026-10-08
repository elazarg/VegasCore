/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommittedResolutionReadout
import Vegas.Source.Forfeit
import Vegas.Compile.EventGraphParameterReadout

/-! # Exact owner forfeits in the initialized reveal program -/

noncomputable section

namespace Vegas.Examples.CommittedResolutionForfeit

open SourceProgram EventGraph EventGraphRuntime Interaction
open CommittedResolutionService CommittedResolutionReadout

abbrev bobPublication : HasVar program.terminalCtx 4 (.publication .bool) := .here

/-- Only Bob's one reveal contributes to his source failure count. -/
theorem bob_failed_reveals (terminal : State simpleExpr program.terminalCtx) :
    failedReveals program bob (publicOutcome program terminal) =
      if (terminal.get bobPublication).isSuccess then 0 else 1 := by
  have viewed : (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool)
      ((sourcePublicEnv terminal).get (publicRef bobPublication)) =
        terminal.get bobPublication := by
    rw [sourcePublicEnv_get_publicRef]
    exact (IExpr.ResultTypes.valueEquiv (L := simpleExpr) .bool).apply_symm_apply _
  cases result : terminal.get bobPublication <;>
    simp [failedReveals, revealCells, program, RevealCell.failed, publicOutcome,
      SourceProgram.terminalRef, List.filter, viewed, PublicationResult.isSuccess,
      alice, bob, result]

/-- Decoding a successful physical Bob publication incurs no Bob source forfeit. -/
theorem bob_failed_reveals_of_success (physical : EventGraphRuntime.State nativeGraph)
    (terminal : State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) physical.config.store = some terminal)
    (published : physical.config.store (.inr bobEvent) = some (.success true)) :
    failedReveals program bob (publicOutcome program terminal) = 0 := by
  have aligned := decodeState?_agrees _ _ _ decoded bobPublication
  change physical.config.store (.inr bobEvent) =
    some (terminal.get bobPublication) at aligned
  rw [published] at aligned
  rw [bob_failed_reveals, Option.some.inj aligned.symm]
  rfl

/-- Decoding physical publication failure incurs exactly one Bob source forfeit. -/
theorem bob_failed_reveals_of_failure (physical : EventGraphRuntime.State nativeGraph)
    (terminal : State simpleExpr program.terminalCtx)
    (decoded : decodeState? (terminalRefs program) physical.config.store = some terminal)
    (published : physical.config.store (.inr bobEvent) = some .failure) :
    failedReveals program bob (publicOutcome program terminal) = 1 := by
  have aligned := decodeState?_agrees _ _ _ decoded bobPublication
  change physical.config.store (.inr bobEvent) =
    some (terminal.get bobPublication) at aligned
  rw [published] at aligned
  rw [bob_failed_reveals, Option.some.inj aligned.symm]
  rfl

/-- The initialized source forfeit subtracts exactly the declared amount
after Bob failure, independently of the secret parameter and Alice's result. -/
theorem bob_forfeit_utility_of_failure {Parameter : Type}
    (parameter : State simpleExpr initialCtx → Parameter)
    (utility : Parameter × PublicOutcome program → Player → ℝ) (forfeit : ℝ)
    (terminal : State simpleExpr program.terminalCtx)
    (failed : terminal.get bobPublication = .failure) :
    forfeitUtility program forfeit utility (setup.parameterOutcome parameter terminal) bob =
      utility (setup.parameterOutcome parameter terminal) bob - forfeit := by
  have count : failedReveals program bob (publicOutcome program terminal) = 1 := by
    rw [bob_failed_reveals, failed]
    rfl
  simp only [forfeitUtility, Setup.parameterOutcome]
  change utility _ bob - forfeit * failedReveals program bob (publicOutcome program terminal) = _
  rw [count, Nat.cast_one, mul_one]

/-- Bob success incurs no source forfeit, including when Alice failed. -/
theorem bob_forfeit_utility_of_success {Parameter : Type}
    (parameter : State simpleExpr initialCtx → Parameter)
    (utility : Parameter × PublicOutcome program → Player → ℝ) (forfeit : ℝ)
    (terminal : State simpleExpr program.terminalCtx)
    (published : terminal.get bobPublication = .success true) :
    forfeitUtility program forfeit utility (setup.parameterOutcome parameter terminal) bob =
      utility (setup.parameterOutcome parameter terminal) bob := by
  have count : failedReveals program bob (publicOutcome program terminal) = 0 := by
    rw [bob_failed_reveals, published]
    rfl
  simp only [forfeitUtility, Setup.parameterOutcome]
  change utility _ bob - forfeit * failedReveals program bob (publicOutcome program terminal) = _
  rw [count, Nat.cast_zero, mul_zero, sub_zero]

end Vegas.Examples.CommittedResolutionForfeit
