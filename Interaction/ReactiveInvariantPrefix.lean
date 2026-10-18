/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Interaction.ReactiveInvariant
import Interaction.ReactiveHistory
import Interaction.ReactiveResponseMenu
import GameTheoryExtensions.Protocol.TracePrefix

/-! # Application invariants along actual initialized history prefixes -/

noncomputable section

namespace Interaction.ReactiveApplication

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Principal : Type} [DecidableEq Principal] {app : ReactiveApplication Principal}
  {predicate : app.State → Prop}

/-- An invariant established at an initialized history persists along its
actual continuation. It need not hold at the initial application state. -/
theorem Invariant.reaches (invariant : app.Invariant predicate)
    (initial : PMF app.State) (horizon : Nat) (scheduler : app.Scheduler)
    {first last : (app.protocol initial horizon scheduler).History} {fuel : Nat}
    (path : (app.protocol initial horizon scheduler).ReachesWithin fuel first last)
    (before after : app.Control) (firstEq : first.state = some before)
    (lastEq : last.state = some after) (valid : predicate before.execution.application) :
    predicate after.execution.application := by
  let preservation : app.StepRelation (fun before after => predicate before → predicate after) :=
    { refl := fun _ valid => valid
      submit := invariant.submit
      handle := fun state message next handled valid =>
        invariant.handle state message next valid handled
      environment := fun state command next reached valid =>
        invariant.environment state command next valid reached }
  induction path generalizing before with
  | refl _ history =>
      cases Option.some.inj (firstEq.symm.trans lastEq)
      exact valid
  | @step steps history target joint legal reached supported suffix ih =>
      have moved := supported
      change reached ∈ (app.transition initial horizon scheduler history.state joint).support
        at moved
      rw [firstEq] at moved
      obtain ⟨middle, middleEq, _retained⟩ := app.transition_recall_prefix
        initial horizon scheduler before reached joint moved
      have preserved := preservation.transition initial horizon scheduler before middle joint
        (by rwa [middleEq] at moved)
      exact ih middle middleEq lastEq (preserved valid)

/-- Any response menu's genuine trace prefix transports an established
application invariant between its actual controls, with no policy assumption. -/
theorem Invariant.tracePrefix (invariant : app.Invariant predicate)
    (menu : app.ResponseMenu) (initial : PMF app.State) (horizon : Nat)
    (scheduler : app.Scheduler) (before after : app.Control)
    (prior : (menu.protocol initial horizon scheduler).Trace (some before))
    (final : (menu.protocol initial horizon scheduler).Trace (some after))
    (kept : TracePrefix prior final) (valid : predicate before.execution.application) :
    predicate after.execution.application := by
  exact invariant.reaches initial horizon scheduler
    (menu.reaches_raw initial horizon scheduler kept.reachesWithin) before after rfl rfl valid

end Interaction.ReactiveApplication
