/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCountedSeedTrace
import Vegas.Examples.CommitSeedBroadcastInitialQuiet

/-! # Actual initialized counted traces under each original service seed -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

theorem original_realize (players : Player → app.Policy) (count : Nat) (state : app.State) :
    (nativeSeedLaw.bind fun seed => app.runRounds (family seed) players count
      (ReactiveApplication.Execution.initial app state)) =
    app.runRounds scheduler players count (ReactiveApplication.Execution.initial app state) :=
  app.schedulerMixture_realize nativeSeedLaw family players count state

/-- The original counted policy supplies exactly the same responses to every
fixed scheduler seed; only the environment kernel is resolved. -/
theorem counted_profile_trace (profile : ∀ who, countedModel.BehavioralPolicy who)
    (seed : Seeds) (count : Nat) (bounded : count ≤ horizon) (execution : app.Execution)
    (reached : execution ∈ (app.runRounds (family seed)
      (countedMenu.decodeProfile initial horizon scheduler profile) count
        initialExecution).support) :
    Nonempty ((countedMenu.protocol initial horizon (family seed)).Trace
      (some ⟨horizon - count, none, execution⟩)) := by
  have covered (owner : Player) (past : List app.PlayerEntry) (view : app.PlayerView)
      (action : app.Action) (supported : action ∈
        (countedMenu.decodeProfile initial horizon scheduler profile owner past view).support) :
      action ∈ countedMenu.actions owner past view :=
    countedMenu.decode_embedPolicy_covered initial horizon scheduler owner (profile owner)
      past view action supported
  apply countedMenu.trace_roundsFrom initial horizon (family seed)
    (countedMenu.decodeProfile initial horizon scheduler profile) covered count bounded execution
  simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
    using reached

end Vegas.Examples.CommitSeedBroadcast
