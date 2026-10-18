/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingHelperInformation
import Vegas.Examples.CommitSeedSignallingHelperInitialRecall

/-! # Literal silent own words before the known useful binding callback -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

private theorem past_clock_length (past : List Nat) (now : Nat)
    (eligible : now = 2 ∨ now = 3) (clockPrefix : past ++ [now] <+: [0, 2, 3]) :
    past.length = if now = 2 then 1 else 2 := by
  cases past with
  | nil =>
      have zero : now = 0 := (List.cons_prefix_cons.mp clockPrefix).1
      omega
  | cons first rest =>
      cases rest with
      | nil =>
          have next : now = 2 :=
            (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp clockPrefix).2).1
          subst now
          rfl
      | cons second rest =>
          cases rest with
          | nil =>
              have next : now = 3 := (List.cons_prefix_cons.mp
                (List.cons_prefix_cons.mp (List.cons_prefix_cons.mp clockPrefix).2).2).1
              subst now
              rfl
          | cons third rest =>
              have bound := clockPrefix.length_le
              simp only [List.length_append, List.length_cons, List.length_nil] at bound
              omega

/-- Before an unresolved original binding, every earlier own callback was a
request for that same binding. The actual fixed calendar therefore counts the
entire own recall, rather than a selected subsequence of convenient records. -/
theorem alice_helper_recall_length (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (eligible : execution.application.current.native.clock = 2 ∨
      execution.application.current.native.clock = 3) :
    (execution.recall alice).length =
      if execution.application.current.native.clock = 2 then 1 else 2 := by
  classical
  have requested (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice) :
      PhaseRuntimeState.requests entry.beforeView.application.2 alice
        (originalCoordinate alice) := by
    obtain ⟨before, prior, kept, _active, observed, _allowed, _later⟩ :=
      rawMenu.recorded_response_prefix initial horizon (family seed)
        ⟨remaining, some alice, execution⟩ trace alice entry recorded
    have earlier := original_binding_request_of_prefix rawMenu seed before
      ⟨remaining, some alice, execution⟩ prior trace kept alice request
    have valid := raw_native_valid (family seed) before
      (rawMenu.toRawTrace initial horizon (family seed) prior)
    have publicRequest : PhaseRuntimeState.requests before.execution.application.publicView alice
        (originalCoordinate alice) :=
      (before.execution.application.requests_publicView valid alice
        (originalCoordinate alice)).mpr earlier
    rw [observed]
    exact publicRequest
  have filtered : (execution.recall alice).filter (fun entry =>
      PhaseRuntimeState.requests entry.beforeView.application.2 alice
        (originalCoordinate alice)) = execution.recall alice := by
    apply List.filter_eq_self.mpr
    intro entry recorded
    exact decide_eq_true (requested entry recorded)
  have calendar := original_service_clocks_prefix rawMenu seed
    ⟨remaining, some alice, execution⟩ trace alice rfl request
  have timer := original_timer (family seed) ⟨remaining, some alice, execution⟩
    (rawMenu.toRawTrace initial horizon (family seed) trace) request.1.symm aliceBinding
      (Or.inl rfl) request.2.2.1.1
  change ((PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate alice) alice
    (execution.recall alice)).map Prod.fst ++
      [execution.application.current.native.clock -
        (execution.application.current.native.activatedAt aliceBinding).getD
          execution.application.current.native.clock]) <+: [0, 2, 3] at calendar
  rw [timer, Option.getD_some, Nat.sub_zero] at calendar
  have counted := past_clock_length _ execution.application.current.native.clock eligible calendar
  simpa only [PhaseSeedScheduler.ownerWord, List.length_map, filtered] using counted

/-- Initial WAIT is the whole literal own history before Alice's clock-two
response, including at actual raw histories of zero assessed probability. -/
theorem alice_clock_two_initial_wait_recall (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice) :
    execution.recall alice = [originalResponseEntry aliceFirst alice ⟨none⟩] := by
  have length := alice_helper_recall_length seed remaining execution trace request (Or.inl clock)
  norm_num [clock] at length
  obtain ⟨entry, recalled⟩ := List.length_eq_one_iff.mp length
  rw [recalled, List.mem_singleton] at quiet
  rw [recalled, quiet]

private theorem alice_outputs_empty_of_silent_records (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (silent : ∀ entry ∈ execution.recall alice, entry.action.transmission = none) :
    app.outputs (execution.recall alice) = [] := by
  have raw := rawMenu.toRawTrace initial horizon (family seed) trace
  have inputs := app.history_inputRecall initial horizon (family seed) raw
  have provenance := app.history_provenance initial horizon (family seed) raw
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro message emitted
  have present : message ∈ execution.network.inputs.filter (fun item => item.sender = alice) := by
    rw [inputs alice]
    exact emitted
  obtain ⟨member, authored⟩ := List.mem_filter.mp present
  have sender : message.sender = alice := of_decide_eq_true authored
  obtain ⟨entry, recorded, material, transmitted, _emitted, _packet⟩ :=
    provenance.inputs message member
  rw [sender] at recorded
  rw [silent entry recorded] at transmitted
  cases transmitted

/-- The real clock-two source has not emitted any own packet when its literal
initial record is WAIT. No clean-foreign-history premise is needed. -/
theorem alice_clock_two_initial_wait_outputs_empty (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (trace : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 2)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice) :
    app.outputs (execution.recall alice) = [] := by
  have recalled := alice_clock_two_initial_wait_recall seed remaining execution trace request clock
    quiet
  apply alice_outputs_empty_of_silent_records seed remaining execution trace
  intro entry recorded
  rw [recalled, List.mem_singleton] at recorded
  subst entry
  rfl

/-- The actual source after WAIT at clocks zero and two remains unsent at
clock three. The two distinct silent records exhaust the actual fixed-calendar
word; their order need not be reconstructed from an integrated scheduler. -/
theorem alice_clock_three_after_wait_outputs_empty (seed : Seeds) (remaining : Nat)
    (execution : app.Execution)
    (fixed : (rawMenu.protocol initial horizon (family seed)).Trace
      (some ⟨remaining, some alice, execution⟩))
    (request : execution.application.SeedRequest alice (originalCoordinate alice))
    (clock : execution.application.current.native.clock = 3)
    (quiet : originalResponseEntry aliceFirst alice ⟨none⟩ ∈ execution.recall alice)
    (helper : app.PlayerEntry) (remembered : helper ∈ execution.recall alice)
    (helperClock : helper.beforeView.application.2.native.clock = 2)
    (waited : helper.action.transmission = none) :
    app.outputs (execution.recall alice) = [] := by
  have length := alice_helper_recall_length seed remaining execution fixed request (Or.inr clock)
  norm_num [clock] at length
  obtain ⟨first, second, recalled⟩ := List.length_eq_two.mp length
  have different : helper ≠ originalResponseEntry aliceFirst alice ⟨none⟩ := by
    intro same
    rw [same] at helperClock
    have zero :
        (originalResponseEntry aliceFirst alice ⟨none⟩).beforeView.application.2.native.clock =
        0 := by
      change aliceFirst.application.current.native.clock = 0
      rw [aliceFirst_application]
      exact initialState_clock
    rw [zero] at helperClock
    omega
  rw [recalled, List.mem_cons, List.mem_singleton] at quiet remembered
  have covered (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall alice) :
      entry = originalResponseEntry aliceFirst alice ⟨none⟩ ∨ entry = helper := by
    rw [recalled, List.mem_cons, List.mem_singleton] at recorded
    rcases quiet with firstQuiet | secondQuiet <;>
      rcases remembered with firstHelper | secondHelper <;>
      rcases recorded with firstEntry | secondEntry
    all_goals first
      | exact Or.inl (firstEntry.trans firstQuiet.symm)
      | exact Or.inl (secondEntry.trans secondQuiet.symm)
      | exact Or.inr (firstEntry.trans firstHelper.symm)
      | exact Or.inr (secondEntry.trans secondHelper.symm)
      | exact (different (firstHelper.trans firstQuiet.symm)).elim
      | exact (different (secondHelper.trans secondQuiet.symm)).elim
  apply alice_outputs_empty_of_silent_records seed remaining execution fixed
  intro entry recorded
  rcases covered entry recorded with first | last
  · subst entry
    rfl
  · subst entry
    exact waited
end Vegas.Examples.CommitSeedSignalling
