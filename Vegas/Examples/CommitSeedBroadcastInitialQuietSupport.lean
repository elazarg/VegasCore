/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastInitialQuietDensity

/-! # Positive reference likelihood forces the actual initial quiet subevent -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem after_initial_records (first second third : app.Action) :
    ∃ aliceEntry bobEntry carolEntry : app.PlayerEntry,
      (afterInitialResponses first second third).recall alice = [aliceEntry] ∧
      (afterInitialResponses first second third).recall bob = [bobEntry] ∧
      (afterInitialResponses first second third).recall carol = [carolEntry] ∧
      aliceEntry.action = first ∧ bobEntry.action = second ∧ carolEntry.action = third := by
  obtain ⟨aliceEmitted, aliceRecord⟩ := app.respond_recall_entry initialAliceCallback alice first
  obtain ⟨bobEmitted, bobRecord⟩ :=
    app.respond_recall_entry (initialBobCallback first) bob second
  obtain ⟨carolEmitted, carolRecord⟩ :=
    app.respond_recall_entry (initialCarolCallback first second) carol third
  have aliceEmpty : initialAliceCallback.recall alice = [] := rfl
  have bobEmpty : (initialBobCallback first).recall bob = [] := by
    change (initialAliceCallback.respond app alice first).recall bob = []
    rw [app.respond_recall_other _ alice bob (by decide)]
    rfl
  have carolEmpty : (initialCarolCallback first second).recall carol = [] := by
    change ((initialBobCallback first).respond app bob second).recall carol = []
    rw [app.respond_recall_other _ bob carol (by decide)]
    change (initialAliceCallback.respond app alice first).recall carol = []
    rw [app.respond_recall_other _ alice carol (by decide)]
    rfl
  rw [aliceEmpty, List.nil_append] at aliceRecord
  rw [bobEmpty, List.nil_append] at bobRecord
  rw [carolEmpty, List.nil_append] at carolRecord
  refine ⟨⟨initialAliceCallback.observe app alice, first, aliceEmitted⟩,
    ⟨(initialBobCallback first).observe app bob, second, bobEmitted⟩,
    ⟨(initialCarolCallback first second).observe app carol, third, carolEmitted⟩,
    ?_, ?_, carolRecord, rfl, rfl, rfl⟩
  · change ((initialCarolCallback first second).respond app carol third).recall alice = _
    rw [app.respond_recall_other _ carol alice (by decide)]
    change ((initialBobCallback first).respond app bob second).recall alice = _
    rw [app.respond_recall_other _ bob alice (by decide)]
    exact aliceRecord
  · change ((initialCarolCallback first second).respond app carol third).recall bob = _
    rw [app.respond_recall_other _ carol bob (by decide)]
    exact bobRecord

private theorem positive_reference_first_action
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (control : app.Control) (trace : rawProtocol.Trace (some control))
    (positive : 0 <
      (rawModel.historyReachWeight (initialQuietProfile profile) ⟨_, trace⟩).toReal)
    (owner : Player) (entry : app.PlayerEntry) (later : List app.PlayerEntry)
    (recorded : control.execution.recall owner = entry :: later) : entry.action = ⟨none⟩ := by
  have member : (some ([], entry.beforeView), entry.action) ∈
      app.recallOwnPlay (control.execution.recall owner) := by
    rw [recorded]
    have actual := app.recallOwnPlay_entry_mem (entry :: later) 0
      (by simp only [List.length_cons]; omega)
    change (some ([], entry.beforeView), entry.action) ∈
      app.recallOwnPlay (entry :: later) at actual
    exact actual
  have own : rawModel.ownPlay owner trace =
      app.recallOwnPlay (control.execution.recall owner) := by
    change (rawMenu.signals initial horizon scheduler).ownPlay owner trace = _
    rw [← rawMenu.ownPlay_toRawTrace initial horizon scheduler owner trace, app.trace_ownPlay]
    rfl
  rw [← own] at member
  have supported := rawModel.ownPlay_supported_of_historyReach_pos
    (initialQuietProfile profile) owner trace positive member
  rw [initialQuietProfile_first] at supported
  exact Option.some.inj ((PMF.mem_support_pure_iff _ _).mp supported)

/-- Positive reference reach forces all three actual initialized responses to
be WAIT. In particular the reference has zero weight outside the quiet subevent. -/
theorem positive_initialQuietProfile_snapshot
    (profile : ∀ observer, rawModel.BehavioralPolicy observer)
    (seed : Seeds) (remaining : Nat) (execution : app.Execution) (owner : Player)
    (trace : rawProtocol.Trace (some ⟨remaining, some owner, execution⟩))
    (fixed : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some owner, execution⟩))
    (late : 5 ≤ execution.environmentRecall.length)
    (positive : 0 <
      (rawModel.historyReachWeight (initialQuietProfile profile) ⟨_, trace⟩).toReal) :
    EmptyEarlySnapshot execution := by
  obtain ⟨first, second, third, snapshot, selected, inputs, records⟩ :=
    original_initial_response_prefix seed remaining execution owner fixed late
  obtain ⟨aliceEntry, bobEntry, carolEntry, aliceRecord, bobRecord, carolRecord,
    firstEq, secondEq, thirdEq⟩ := after_initial_records first second third
  have initialWait (observer : Player) (entry : app.PlayerEntry)
      (initialRecord : (afterInitialResponses first second third).recall observer = [entry]) :
      entry.action = ⟨none⟩ := by
    obtain ⟨later, recalled⟩ := records observer
    rw [initialRecord, List.singleton_append] at recalled
    exact positive_reference_first_action profile ⟨remaining, some owner, execution⟩ trace
      positive observer entry later recalled.symm
  have firstWait := firstEq.symm.trans (initialWait alice aliceEntry aliceRecord)
  have secondWait := secondEq.symm.trans (initialWait bob bobEntry bobRecord)
  have thirdWait := thirdEq.symm.trans (initialWait carol carolEntry carolRecord)
  have empty : (afterInitialResponses first second third).network.inputs = [] :=
    (afterInitialResponses_inputs_empty first second third).mpr
      ⟨firstWait, secondWait, thirdWait⟩
  intro actual member
  have equal := Option.some.inj ((Option.mem_def.mp member).symm.trans selected)
  subst actual
  exact inputs.trans empty

end Vegas.Examples.CommitSeedBroadcast
