/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SourceSemantics
import Vegas.Graph.MessageApplication

/-! # Typed graph execution through the shared message transport -/

namespace VegasTests.GraphMessages

open GameTheory.Math.Probability Interaction Interaction.MessageApplication
open Vegas Vegas.GraphRuntime VegasTests.SourceSemantics

noncomputable section

private abbrev TestPlayer := VegasTests.SourceSemantics.Player

abbrev runtime : GraphRuntime TestPlayer simpleExpr
    (SourceProgram.graphCtx mixedProgram.terminalCtx) where
  deadline := fun _ => 2

abbrev app := runtime.application

private def initial : app.State :=
  MessageApplication.State.initial app
    (GraphRuntime.State.initial mixedInitial.graph mixedInitial.graphInputs)

private def choiceRaw (result : PublicationResult (Option Bool)) : Raw simpleExpr :=
  ⟨.result (.option .bool), result⟩

private def seedRaw (result : PublicationResult Bool) : Raw simpleExpr :=
  ⟨.result .bool, result⟩

private abbrev choiceHandle : GraphRuntime.Handle TestPlayer := (.alice, .prepared 0)
private abbrev seedHandle : GraphRuntime.Handle TestPlayer := (.alice, .initial 11)

private def pc (state : app.State) : Nat := state.application.publicView.pc

private def publicHas (name : VarId) (state : app.State) : Bool :=
  state.application.publicView.Γ.any fun binding =>
    match binding.2 with
    | ⟨_, .pub⟩ => binding.1 = name
    | ⟨_, .sealed _⟩ => false

private def payout? (state : app.State) : Option (List (TestPlayer × Int)) :=
  state.application.outcome?.map (Graph.evaluatePayoffs mixedInitial.graph)

private def successfulPrefix : List app.Action := [
  .privateCommand .alice (.prepare 0 (choiceRaw (.success none))),
  .submit .alice (.commitment 0 choiceHandle),
  .include (.alice, 0),
  .submit .alice (.opening 1 choiceHandle (choiceRaw (.success none)))]

/-- Delivery exposes a pending opening to its recipient, but does not install
the graph result or advance the canonical phase before public inclusion. -/
theorem delivered_opening_stays_pending :
    (app.run (successfulPrefix ++ [.deliver .alice (.alice, 1)]) initial).map
        (fun state => (pc state, publicHas 13 state,
          state.pool.inbox .alice)) =
      FinDist.pure (1, false,
        [⟨(.alice, 1), .opening 1 choiceHandle (choiceRaw (.success none))⟩]) := by
  simp [successfulPrefix, MessageApplication.run, MessageApplication.step,
    MessageApplication.includePending, MessagePool.includeApplication,
    MessagePool.submit, MessagePool.deliver, MessagePool.lookup, pc, publicHas,
    MessageApplication.State.initial, MessagePool.empty, GraphRuntime.State.initial,
    initial, mixedInitial, mixedProgram]
  congr 1

private def successfulActions : List app.Action := [
  .privateCommand .alice (.prepare 0 (choiceRaw (.success none))),
  .submit .alice (.commitment 0 choiceHandle),
  .include (.alice, 0),
  .submit .alice (.opening 1 choiceHandle (choiceRaw (.success none))),
  .deliver .alice (.alice, 1),
  .include (.alice, 1),
  .submit .alice (.opening 2 seedHandle (seedRaw (.success true))),
  .include (.alice, 2),
  .environment .tick]

/-- One complete run uses preparation, submission, recipient delivery, public
inclusion, initial-private disclosure, and the graph's dependent chance step. -/
theorem successful_transport_payout :
    (app.run successfulActions initial).map payout? =
      FinDist.pure (some [(.alice, 10)]) := by
  simp only [successfulActions, MessageApplication.run, MessageApplication.step,
    app, GraphRuntime.application, FinDist.pure_bind, FinDist.bind_pure]
  change FinDist.map _ (FinDist.map _ (FinDist.map (fun _value : Bool => _) _)) = _
  simp only [FinDist.map_comp]
  change (FinDist.map (fun _ : Bool =>
    some ([(Player.alice, 10)] : List (TestPlayer × Int))) _) = _
  exact FinDist.map_const _ _

private def rejectingActions : List app.Action := [
  .privateCommand .alice (.prepare 0 (choiceRaw (.success (some false)))),
  .submit .alice (.commitment 0 choiceHandle), .include (.alice, 0),
  .submit .alice (.opening 1 choiceHandle (choiceRaw (.success (some false)))),
  .include (.alice, 1),
  .submit .alice (.opening 2 seedHandle (seedRaw (.success true))),
  .include (.alice, 2), .environment .tick]

/-- The first opening succeeds while its guard waits. Publishing the initial
seed later closes the relation and rejects that current seed publication. -/
theorem later_guard_rejection_payout :
    (app.run rejectingActions initial).map payout? =
      FinDist.pure (some [(.alice, -5)]) := by
  simp only [rejectingActions, MessageApplication.run, MessageApplication.step,
    app, GraphRuntime.application, FinDist.pure_bind, FinDist.bind_pure]
  change FinDist.map _ (FinDist.map _ (FinDist.map (fun _value : Bool => _) _)) = _
  simp only [FinDist.map_comp]
  change (FinDist.map (fun _ : Bool =>
    some ([(Player.alice, -5)] : List (TestPlayer × Int))) _) = _
  exact FinDist.map_const _ _

private def unopenableActions : List app.Action := [
  .submit .alice (.commitment 0 choiceHandle), .include (.alice, 0),
  .submit .alice (.opening 1 choiceHandle (choiceRaw (.success none))),
  .include (.alice, 1), .environment .tick, .environment .tick,
  .submit .alice (.opening 2 seedHandle (seedRaw (.success true))),
  .include (.alice, 2), .environment .tick]

/-- Accepting an unprepared handle fixes an unopenable binding. Its rejected
opening leaves the phase pending until the ordinary relative deadline. -/
theorem unopenable_times_out_to_failure :
    (app.run unopenableActions initial).map payout? =
      FinDist.pure (some [(.alice, -10)]) := by
  simp only [unopenableActions, MessageApplication.run, MessageApplication.step,
    app, GraphRuntime.application, FinDist.pure_bind, FinDist.bind_pure]
  change FinDist.map _ ((FinDist.map _ (FinDist.pure _)).bind _) = _
  simp only [FinDist.map_pure, FinDist.pure_bind]
  change FinDist.map _ ((FinDist.map _ (FinDist.pure _)).bind _) = _
  simp only [FinDist.map_pure, FinDist.pure_bind]
  change FinDist.map _ (FinDist.map _ (FinDist.map (fun _value : Bool => _) _)) = _
  simp only [FinDist.map_comp]
  change (FinDist.map (fun _ : Bool =>
    some ([(Player.alice, -10)] : List (TestPlayer × Int))) _) = _
  exact FinDist.map_const _ _

private def withholdActions : List app.Action := [
  .privateCommand .alice (.prepare 0 (choiceRaw (.success none))),
  .submit .alice (.commitment 0 choiceHandle), .include (.alice, 0),
  .submit .alice (.withhold 1), .include (.alice, 1),
  .submit .alice (.opening 2 seedHandle (seedRaw (.success true))),
  .include (.alice, 2), .environment .tick]

theorem explicit_withhold_is_failure :
    (app.run withholdActions initial).map payout? =
      FinDist.pure (some [(.alice, -10)]) := by
  simp only [withholdActions, MessageApplication.run, MessageApplication.step,
    app, GraphRuntime.application, FinDist.pure_bind, FinDist.bind_pure]
  change FinDist.map _ (FinDist.map _ (FinDist.map (fun _value : Bool => _) _)) = _
  simp only [FinDist.map_comp]
  change (FinDist.map (fun _ : Bool =>
    some ([(Player.alice, -10)] : List (TestPlayer × Int))) _) = _
  exact FinDist.map_const _ _

/-- Initial private setup is not disclosed by a clock tick. Before its deadline
the resolve phase stutters and the private result remains absent publicly. -/
theorem initial_private_disclosure_is_not_automatic :
    (app.run (successfulPrefix ++ [.include (.alice, 1), .environment .tick]) initial).map
        (fun state => (pc state, publicHas 14 state)) =
      FinDist.pure (2, false) := by
  simp only [successfulPrefix, List.cons_append, List.nil_append,
    MessageApplication.run, MessageApplication.step, app, GraphRuntime.application,
    FinDist.pure_bind, FinDist.bind_pure]
  change FinDist.map _ (FinDist.map _ (FinDist.pure _)) = _
  simp only [FinDist.map_pure]
  rfl

/-- A wrong wire tag is publicly rejected and leaves the application state
unchanged; two later ticks resolve the same phase by failure. -/
theorem wrong_tag_rejects_then_times_out :
    let actions := successfulPrefix ++ [.include (.alice, 1)] ++ [
      .submit .alice (.opening 2 seedHandle (choiceRaw (.success none))),
      .include (.alice, 2), .environment .tick, .environment .tick]
    (app.run actions initial).map (fun state => (pc state, state.receipts.getLast?)) =
      FinDist.pure (3, some ((.alice, 2), false)) := by
  simp only [successfulPrefix, List.cons_append, List.nil_append,
    MessageApplication.run, MessageApplication.step, app, GraphRuntime.application,
    FinDist.pure_bind, FinDist.bind_pure]
  change FinDist.map _ ((FinDist.map _ (FinDist.pure _)).bind _) = _
  simp only [FinDist.map_pure, FinDist.pure_bind]
  change FinDist.map _ (FinDist.map _ (FinDist.pure _)) = _
  simp only [FinDist.map_pure]
  rfl

/-- Malformed, out-of-order, and replay traffic can change the native pool and
receipts but cannot advance the canonical graph phase. -/
theorem ineffective_traffic_does_not_advance :
    (app.run [
      .submit .alice (.malformed (seedRaw (.success true))), .include (.alice, 0),
      .submit .alice (.opening 2 seedHandle (seedRaw (.success true))),
      .include (.alice, 1), .replay .alice (.alice, 0), .include (.alice, 2)] initial).map pc =
      FinDist.pure 0 := by
  simp [MessageApplication.run, MessageApplication.step, MessageApplication.includePending,
    MessagePool.includeApplication, MessagePool.submit, MessagePool.replay,
    pc, initial, mixedInitial, mixedProgram]
  congr 1

/-- Couple each completed run to its own later clock ticks. The entire decoded
typed environment, including the sampled coin, is retained pointwise. -/
theorem terminal_ticks_do_not_reroll :
    ((app.run successfulActions initial).bind fun before =>
      (app.run [.environment .tick, .environment .tick] before).map fun after =>
      (before.application.outcome?, after.application.outcome?)) =
    (app.run successfulActions initial).map fun state =>
      (state.application.outcome?, state.application.outcome?) := by
  rw [FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro before hbefore
  have hmapped : payout? before ∈
      ((app.run successfulActions initial).map payout?).support := by
    rw [FinDist.support_map]
    exact ⟨before, hbefore, rfl⟩
  rw [successful_transport_payout, FinDist.mem_support_pure] at hmapped
  have hterminal : before.application.outcome? ≠ none := by
    intro hnone
    simp [payout?, hnone] at hmapped
  obtain ⟨application, pool, receipts⟩ := before
  cases application with
  | running graph ideal values bindings candidates pc clock enteredAt =>
      cases graph with
      | ret payoffs =>
          simp [MessageApplication.run, MessageApplication.step, app,
            GraphRuntime.application, GraphRuntime.environmentStep, GraphRuntime.tick,
            GraphRuntime.State.outcome?]
      | sample name fresh law next => exact False.elim (hterminal rfl)
      | bind name owner fresh next => exact False.elim (hterminal rfl)
      | resolve outputName owner bindingName fresh source checks next =>
          exact False.elim (hterminal rfl)

end

end VegasTests.GraphMessages
