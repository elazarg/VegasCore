/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCountedContinuation
import Interaction.ReactiveLocalContinuation

/-! # Exact native value after one forced current physical response -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

open Classical in
/-- The native one-shot deviation changes its current response only. Every
later assessed response and the original physical continuation remain literal. -/
theorem raw_committed_current_value_eq_finish
    (profile : ∀ owner, rawModel.BehavioralPolicy owner)
    (history : rawProtocol.History) (owner : Player) (remaining : Nat)
    (execution : app.Execution)
    (current : history.state = some ⟨remaining, some owner, execution⟩)
    (info : rawModel.InfoState owner) (observed : rawModel.infoOf owner history.trace = info)
    (choice : rawModel.Choice owner info) (response : app.Action)
    (selected : choice.1 = some response) :
    expect (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) profile owner
        ((profile owner).commit info choice)) history) (rawPayoff owner) =
      expect (app.finish initial horizon scheduler
        (rawMenu.decodeProfile initial horizon scheduler profile)
        (some ⟨remaining, none, execution.respond app owner response⟩))
          (fun state => netPayoff state owner) := by
  have raw := rawMenu.toRawTrace initial horizon scheduler history.trace
  have enough : app.rank horizon history.state ≤ 2 * horizon + 1 := by
    rw [current]
    exact (Nat.le_add_left _ _).trans (app.trace_bound initial horizon scheduler (current ▸ raw))
  have projection := rawMenu.run_local_law_finish_of_information initial horizon scheduler
    profile history owner remaining execution current info observed (PMF.pure choice)
      (2 * horizon) enough
  change (rawModel.runBehavioralFrom
    (Profile.update (sig := rawModel.behavioralSignature) profile owner
      ((profile owner).commit info choice)) (2 * horizon + 1) history).map History.state = _
        at projection
  rw [PMF.pure_map, selected, Option.getD_some, PMF.pure_bind] at projection
  have terminalProjection : (rawModel.runBehavioralTerminalFrom canonicalCertificate
      (Profile.update (sig := rawModel.behavioralSignature) profile owner
        ((profile owner).commit info choice)) history).map History.state =
      app.finish initial horizon scheduler (rawMenu.decodeProfile initial horizon scheduler profile)
        (some ⟨remaining, none, execution.respond app owner response⟩) := by
    rw [rawModel.runBehavioralTerminalFrom_eq_runBehavioralFrom_of_bounded canonicalCertificate
      (rawMenu.bounded initial horizon scheduler)]
    exact projection
  have expected := congrArg (fun law : PMF app.ProtocolState =>
    expect law (fun state => netPayoff state owner)) terminalProjection
  rw [expect_map] at expected
  change expect _ (rawPayoff owner) = _ at expected
  exact expected

end Vegas.Examples.CommitSeedBroadcast
