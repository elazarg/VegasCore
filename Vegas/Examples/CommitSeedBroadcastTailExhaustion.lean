/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingExhaustion
import Vegas.Examples.CommitSeedBroadcastOpportunity
import Vegas.Examples.CommitSeedBroadcastCalendarClocks

/-! # Exhaustion of an unsent continuation episode -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

private theorem tail_selected_age_zero (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate)
    (selected : choose seeds current.execution.environmentRecall
      (current.execution.observeEnvironment app) = .activate owner) :
    PhaseSeedScheduler.elapsed runtime leaks coordinate
      (current.execution.observeEnvironment app) = 0 := by
  have elapsed := tail_request_elapsed seeds current trace coordinate owner retired request
  have turn := tail_activation_turn seeds current trace coordinate owner retired request selected
  rw [turn, tailTurn] at elapsed
  have bounded := owner.isLt
  have zero : 2 * owner.val - 6 = 0 := by omega
  simpa only [zero, Nat.zero_min] using elapsed

private theorem recorded_tail_clock_zero (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (earlier later : List app.EnvironmentEntry) (entry : app.EnvironmentEntry)
    (recalled : execution.environmentRecall = earlier ++ entry :: later)
    (callback : PhaseSeedScheduler.callback runtime leaks coordinate owner entry) :
    PhaseSeedScheduler.elapsed runtime leaks coordinate entry.beforeView = 0 := by
  obtain ⟨used, before, _within, ⟨beforeTrace⟩, _supported, past, viewed⟩ :=
    menu.recorded_environment_prefix initial horizon (family seeds) remaining execution trace
      earlier entry later recalled
  have raw := menu.toRawTrace initial horizon (family seeds) beforeTrace
  have valid := raw_native_valid (family seeds) _ raw
  have publicRequest := callback.2
  rw [viewed] at publicRequest
  have request := (before.application.requests_publicView valid owner coordinate).mp publicRequest
  have commands := family_commands seeds _ (menu.toRawTrace initial horizon (family seeds) trace)
  rw [recalled] at commands
  have chosen := ((app.commandConsistentFrom_append choose seeds [] earlier
    (entry :: later)).mp commands).2.1
  have activated := callback.1
  rw [activated] at chosen
  have selected : choose seeds before.environmentRecall (before.observeEnvironment app) =
      .activate owner := by
    simpa only [List.nil_append, ← past, viewed] using chosen
  rw [viewed]
  exact tail_selected_age_zero seeds _ raw coordinate owner retired request selected

private theorem environment_exclusions_bound (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current)) :
    ∀ entry ∈ current.execution.environmentRecall,
      entry.beforeView.application.excluded ⊆ current.execution.application.current.excluded := by
  let predicate : app.Execution → Prop := fun execution =>
    ∀ entry ∈ execution.environmentRecall,
      entry.beforeView.application.excluded ⊆ execution.application.current.excluded
  have monotone := phaseApplication_exclusion_monotone runtime leaks
  have invariant : app.ServiceInvariant (family seeds) predicate := {
    respond := by
      intro execution actor response prior entry recorded
      rw [app.respond_environmentRecall] at recorded
      exact (prior entry recorded).trans (monotone.respond execution actor response)
    environment := by
      intro execution next command prior _selected moved entry recorded
      rw [app.environmentStep_environmentRecall execution next command moved] at recorded
      rcases List.mem_append.mp recorded with old | latest
      · exact (prior entry old).trans (monotone.environmentStep execution next command moved)
      · cases List.mem_singleton.mp latest
        exact monotone.environmentStep execution next command moved }
  exact invariant.history initial horizon
    (fun _ _ entry member => False.elim (List.not_mem_nil member)) trace

theorem positive_age_callback (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (request : execution.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app)) :
    ∃ entry ∈ execution.environmentRecall,
      PhaseSeedScheduler.callback runtime leaks coordinate owner entry := by
  classical
  have raw := menu.toRawTrace initial horizon (family seeds) trace
  have valid := raw_native_valid (family seeds) _ raw
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  have older : entered < execution.application.current.native.clock := by
    change 0 < execution.application.current.native.clock -
      (execution.application.current.native.activatedAt coordinate.event).getD
        execution.application.current.native.clock at positive
    rw [stamp, Option.getD_some] at positive
    omega
  obtain witnessed | unserved := raw_pending_opportunity seeds raw coordinate owner entered
    request stamp
  · obtain ⟨entry, member, activated, tag, ready, _stamp⟩ := witnessed
    obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp member
    obtain ⟨used, before, _within, ⟨beforeTrace⟩, _supported, _past, viewed⟩ :=
      menu.recorded_environment_prefix initial horizon (family seeds) remaining execution trace
        earlier entry later recalled
    have beforeRaw := menu.toRawTrace initial horizon (family seeds) beforeTrace
    have beforeValid := raw_native_valid (family seeds) _ beforeRaw
    have sameTag : before.application.attempt = coordinate.attempt := by
      change (before.observeEnvironment app).application.attempt = _
      rw [← viewed]
      exact tag
    have samePhases := raw_same_attempt_phases (family seeds) _ _ beforeRaw raw
      (sameTag.trans request.1)
    have beforeReady : before.application.current.native.config.cut.Ready coordinate.event := by
      apply (State.publicView_eventReady _ _).mp
      change (before.observeEnvironment app).application.native.EventReady coordinate.event
      rw [← viewed]
      exact ready
    have beforeUnexcluded : owner ∉ before.application.current.excluded := by
      intro excluded
      apply request.2.2.2.2
      apply environment_exclusions_bound seeds _ raw entry member
      rw [viewed]
      exact excluded
    have beforeRequest : before.application.SeedRequest owner coordinate := by
      refine ⟨sameTag.symm, ?_, beforeReady, request.2.2.2.1, beforeUnexcluded⟩
      obtain ⟨phase, installed, inside⟩ := request.2.1
      refine ⟨phase, ?_, inside⟩
      rwa [samePhases]
    refine ⟨entry, member, activated, ?_⟩
    rw [viewed]
    exact (before.application.requests_publicView beforeValid owner coordinate).mpr beforeRequest
  · exact (Nat.not_lt_of_ge unserved.2 older).elim

private theorem filter_length_le_one_of_unique_indices {α : Type} (predicate : α → Bool)
    (entries : List α) :
    (∀ first second (firstBound : first < entries.length) (secondBound : second < entries.length),
      predicate entries[first] = true → predicate entries[second] = true → first = second) →
        (entries.filter predicate).length ≤ 1 := by
  induction entries with
  | nil => intro _unique; simp
  | cons entry rest ih =>
      intro unique
      by_cases selected : predicate entry = true
      · have restEmpty : rest.filter predicate = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro later member laterSelected
          obtain ⟨earlier, after, restEq⟩ := List.mem_iff_append.mp member
          have firstBound : 0 < (entry :: rest).length := by simp only [List.length_cons]; omega
          have laterBound : earlier.length + 1 < (entry :: rest).length := by
            rw [restEq]
            simp only [List.length_cons, List.length_append]
            omega
          have atLater : predicate (entry :: rest)[earlier.length + 1] = true := by
            have foundLater : (entry :: rest)[earlier.length + 1]? = some later := by
              rw [restEq]
              change (earlier ++ later :: after)[earlier.length]? = some later
              rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]
              rfl
            have exactLater := Option.some.inj
              ((List.getElem?_eq_getElem laterBound).symm.trans foundLater)
            rw [exactLater]
            exact laterSelected
          have same := unique 0 (earlier.length + 1) firstBound laterBound selected atLater
          omega
        simp only [List.filter_cons, selected, ite_true, restEmpty, List.length_cons,
          List.length_nil, Nat.le_refl]
      · have restUnique : ∀ first second (firstBound : first < rest.length)
            (secondBound : second < rest.length), predicate rest[first] = true →
              predicate rest[second] = true → first = second := by
          intro first second firstBound secondBound firstSelected secondSelected
          have same := unique (first + 1) (second + 1)
            (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using firstBound)
            (by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using secondBound)
            firstSelected secondSelected
          omega
        simpa only [List.filter_cons, ite_eq_right selected] using ih restUnique

private theorem tail_clock_word_length (menu : app.ResponseMenu)
    (silence : ∀ owner past view,
      (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt) :
    (clockWord coordinate owner current.execution.environmentRecall).length ≤ 1 := by
  classical
  simp only [clockWord, List.length_map]
  apply filter_length_le_one_of_unique_indices
  intro first second firstBound secondBound firstSelected secondSelected
  exact tail_callback_index_unique menu silence seeds current trace coordinate owner retired
    first second firstBound secondBound (of_decide_eq_true firstSelected)
      (of_decide_eq_true secondSelected)

private theorem positive_tail_clock_word (menu : app.ResponseMenu)
    (silence : ∀ owner past view,
      (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (seeds : Seeds) (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate)
    (positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app)) :
    clockWord coordinate owner execution.environmentRecall = [0] := by
  classical
  obtain ⟨entry, member, callback⟩ := positive_age_callback menu seeds remaining execution trace
    coordinate owner request positive
  obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp member
  have zero := recorded_tail_clock_zero menu seeds remaining execution trace coordinate owner
    retired earlier later entry recalled callback
  have zeroMember : 0 ∈ clockWord coordinate owner execution.environmentRecall := by
    apply List.mem_map.mpr
    exact ⟨entry, List.mem_filter.mpr ⟨member, decide_eq_true callback⟩, zero⟩
  have bounded := tail_clock_word_length menu silence seeds _ trace coordinate owner retired
  cases wordEq : clockWord coordinate owner execution.environmentRecall with
  | nil => rw [wordEq] at zeroMember; exact (List.not_mem_nil zeroMember).elim
  | cons first rest =>
      rw [wordEq, List.length_cons] at bounded
      have emptyRest : rest = [] := List.length_eq_zero_iff.mp (by omega)
      rw [wordEq, emptyRest] at zeroMember
      rw [emptyRest]
      exact congrArg (fun entry : Nat => [entry]) (List.mem_singleton.mp zeroMember).symm

private theorem tail_request_loss_clock_word (seeds : Seeds) (remaining : Nat)
    (execution next : app.Execution)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : execution.application.SeedRequest owner coordinate)
    (unsent : ∀ message ∈ app.outputs (execution.recall owner),
      PhaseCount.event? message.payload ≠ some coordinate)
    (command : app.Command) (moved : next ∈ (execution.environmentStep app command).support)
    (lost : ¬ next.application.SeedRequest owner coordinate) :
    coordinate.Resolved next.application ∧
      clockWord coordinate owner next.environmentRecall = [0] := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have valid := raw_native_valid (family seeds) _ raw
  have ordered := (raw_phase_geometry (family seeds) _ raw).1.adjacent
  obtain retained | expiry := unsent_request_retained_or_expiry seeds remaining execution next raw
    coordinate owner request unsent command moved
  · exact (lost retained).elim
  have expiryMoved := moved
  rw [expiry] at expiryMoved
  have nativeMoved : next.application ∈
      (execution.application.environment runtime (.expire coordinate.event)).support := by
    simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at expiryMoved
    obtain ⟨state, supported, rfl⟩ := PMF.support_map .. ▸ expiryMoved
    exact supported
  obtain ⟨entered, stamp⟩ := Option.isSome_iff_exists.mp
    ((valid.active.activated_iff coordinate.event).mpr
      ⟨request.2.2.1, by rw [request.2.2.2.1]; rfl⟩)
  have due : runtime.deadline coordinate.event ≤
      execution.application.current.native.clock - entered := by
    by_contra early
    have timely : execution.application.current.native.WithinDeadline runtime coordinate.event := by
      rw [State.WithinDeadline, stamp]
      omega
    exact lost (PhaseRuntimeState.expiry_request_before_deadline runtime execution.application
      next.application owner coordinate request timely nativeMoved)
  have positive : 0 < PhaseSeedScheduler.elapsed runtime leaks coordinate
      (execution.observeEnvironment app) := by
    change 0 < execution.application.current.native.clock -
      (execution.application.current.native.activatedAt coordinate.event).getD
        execution.application.current.native.clock
    rw [stamp, Option.getD_some]
    change 6 ≤ execution.application.current.native.clock - entered at due
    omega
  have clocks := positive_tail_clock_word countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seeds remaining execution trace coordinate
      owner retired request positive
  have closed := execution.application.expire_resolves_of_request runtime next.application valid
    ordered request (by rw [stamp, Option.getD_some]; exact due) nativeMoved
  have resolved := CommitAttemptEvent.Resolved.of_step coordinate execution.application
    next.application request.1
    ((phaseApplication_namespace_progress runtime leaks).environmentStep execution next command
      moved ordered) closed
  have notCallback : ¬ PhaseSeedScheduler.callback runtime leaks coordinate owner
      ⟨execution.observeEnvironment app, command⟩ := by
    intro callback
    rw [expiry] at callback
    cases callback.1
  refine ⟨resolved, ?_⟩
  rw [app.environmentStep_environmentRecall execution next command moved, clockWord_snoc,
    ite_eq_right notCallback, List.append_nil]
  exact clocks

private theorem closed_clock_word_transition (seeds : Seeds) (before after : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some before))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (resolved : coordinate.Resolved before.execution.application)
    (joint : Player → Option app.Action)
    (moved : some after ∈
      (app.transition initial horizon (family seeds) (some before) joint).support) :
    coordinate.Resolved after.execution.application ∧
      clockWord coordinate owner after.execution.environmentRecall =
        clockWord coordinate owner before.execution.environmentRecall := by
  classical
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  have valid := raw_native_valid (family seeds) before raw
  have ordered := (raw_phase_geometry (family seeds) before raw).1.adjacent
  refine ⟨(phaseApplication_resolution runtime leaks coordinate).transition initial horizon
    (family seeds) before after joint moved (encodeInputs (Env.empty (CellVal simpleExpr))) valid
      ordered resolved, ?_⟩
  rcases before with ⟨remaining, active, execution⟩
  cases active with
  | some actor =>
      cases (PMF.mem_support_pure_iff _ _).mp moved
      rw [app.respond_environmentRecall]
  | none =>
      cases remaining with
      | zero => cases (PMF.mem_support_pure_iff _ _).mp moved; rfl
      | succ remaining =>
          obtain ⟨command, _selected, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
          obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ reached
          cases Option.some.inj same
          have absent : ¬ PhaseRuntimeState.requests execution.application.publicView owner
              coordinate := by
            intro requested
            exact CommitAttemptEvent.Resolved.not_request coordinate execution.application resolved
              owner ((execution.application.requests_publicView valid owner coordinate).mp
                requested)
          have notCallback : ¬ PhaseSeedScheduler.callback runtime leaks coordinate owner
              ⟨execution.observeEnvironment app, command⟩ := fun callback => absent callback.2
          rw [app.environmentStep_environmentRecall execution next command supported,
            clockWord_snoc, ite_eq_right notCallback, List.append_nil]

private theorem tail_silent_prefix_progress (seeds : Seeds) (before : app.Control)
    (beforeTrace : (countedMenu.protocol initial horizon (family seeds)).Trace (some before))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : before.execution.application.SeedRequest owner coordinate) :
    ∀ {state} {trace : (countedMenu.protocol initial horizon (family seeds)).Trace state},
      TracePrefix beforeTrace trace → ∃ after : app.Control, state = some after ∧
        ((∀ message ∈ app.outputs (after.execution.recall owner),
          PhaseCount.event? message.payload ≠ some coordinate) →
          after.execution.application.SeedRequest owner coordinate ∨
            (coordinate.Resolved after.execution.application ∧
              clockWord coordinate owner after.execution.environmentRecall = [0])) := by
  classical
  intro state trace kept
  induction kept with
  | refl => exact ⟨before, rfl, fun _unsent => Or.inl request⟩
  | @extend source target prior kept joint legal moved ih =>
      obtain ⟨middle, rfl, previous⟩ := ih
      change target ∈ (app.transition initial horizon (family seeds) (some middle) joint).support
        at moved
      obtain ⟨after, rfl, recalledPrefix⟩ := app.transition_recall_prefix initial horizon
        (family seeds) middle target joint moved
      refine ⟨after, rfl, ?_⟩
      intro unsent
      have beforeUnsent : ∀ message ∈ app.outputs (middle.execution.recall owner),
          PhaseCount.event? message.payload ≠ some coordinate := by
        intro message output
        obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
        exact unsent message (List.mem_filterMap.mpr
          ⟨entry, (recalledPrefix owner).subset member, emitted⟩)
      rcases previous beforeUnsent with asked | ⟨closed, clocks⟩
      · by_cases retained : after.execution.application.SeedRequest owner coordinate
        · exact Or.inl retained
        · right
          rcases middle with ⟨remaining, active, execution⟩
          cases active with
          | some actor =>
              cases (PMF.mem_support_pure_iff _ _).mp moved
              exact (retained (respond_request runtime leaks execution actor _ owner coordinate
                asked)).elim
          | none =>
              cases remaining with
              | zero => exact (legal.1 ⟨rfl, rfl⟩).elim
              | succ remaining =>
                  obtain ⟨command, _selected, reached⟩ := Set.mem_iUnion₂.mp
                    (PMF.support_bind .. ▸ moved)
                  obtain ⟨next, supported, same⟩ := PMF.support_map .. ▸ reached
                  cases Option.some.inj same
                  exact tail_request_loss_clock_word seeds (remaining + 1) execution next prior
                    coordinate owner retired asked beforeUnsent command supported retained
      · have afterClosed := closed_clock_word_transition seeds middle after prior coordinate owner
          closed joint moved
        exact Or.inr ⟨afterClosed.1, afterClosed.2.trans clocks⟩

/-- A genuinely requested continuation coordinate that resolves without a
service emission exhausts its singleton calendar, retaining the actual prefix,
all foreign counted choices, and every subsequent retired namespace. -/
theorem tail_episode_exhausted_clocks (seeds : Seeds) (before current : app.Control)
    (beforeTrace : (countedMenu.protocol initial horizon (family seeds)).Trace (some before))
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some current))
    (kept : TracePrefix beforeTrace trace) (coordinate : CommitAttemptEvent graph) (owner : Player)
    (retired : coordinate.attempt ≠ originalAttempt)
    (request : before.execution.application.SeedRequest owner coordinate)
    (resolved : coordinate.Resolved current.execution.application)
    (empty : PhaseService.bindingEmissionClocks runtime leaks coordinate owner
      current.execution = []) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
      (current.execution.recall owner)).map Prod.fst = [0] := by
  classical
  have progress := tail_silent_prefix_progress seeds before beforeTrace coordinate owner retired
    request kept
  obtain ⟨after, same, result⟩ := progress
  cases Option.some.inj same
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none =>
      have unsent := unsent_of_empty_emissions seeds remaining execution trace coordinate owner
        empty
      obtain retained | ⟨_closed, clocks⟩ := result unsent
      · exact (CommitAttemptEvent.Resolved.not_request coordinate execution.application resolved
          owner retained).elim
      · have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
          horizon (family seeds) remaining execution trace owner coordinate
        rw [← words, word_clock_projection]
        exact clocks
  | some actor =>
      obtain ⟨responded⟩ := countedMenu.trace_respond initial horizon (family seeds) remaining
        execution actor ⟨none⟩ trace (PhaseCount.silence_onePacket runtime leaks bounds actor _ _)
      have afterEmpty : PhaseService.bindingEmissionClocks runtime leaks coordinate owner
          (execution.respond app actor ⟨none⟩) = [] := empty
      have afterUnsent := unsent_of_empty_emissions seeds remaining
        (execution.respond app actor ⟨none⟩) responded coordinate owner afterEmpty
      have unsent : ∀ message ∈ app.outputs (execution.recall owner),
          PhaseCount.event? message.payload ≠ some coordinate := by
        intro message output
        obtain ⟨entry, member, emitted⟩ := List.mem_filterMap.mp output
        exact afterUnsent message (List.mem_filterMap.mpr ⟨entry,
          (app.respond_recall_prefix execution actor owner ⟨none⟩).subset member, emitted⟩)
      obtain retained | ⟨_closed, clocks⟩ := result unsent
      · exact (CommitAttemptEvent.Resolved.not_request coordinate execution.application resolved
          owner retained).elim
      · have valid := raw_native_valid (family seeds) _
          (countedMenu.toRawTrace initial horizon (family seeds) trace)
        have absent : ¬ PhaseRuntimeState.requests (execution.observe app owner).application.2
            owner coordinate := by
          intro requested
          exact CommitAttemptEvent.Resolved.not_request coordinate execution.application resolved
            owner ((execution.application.requests_publicView valid owner coordinate).mp requested)
        have afterWord : PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
            ((execution.respond app actor ⟨none⟩).recall owner) =
              PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
                (execution.recall owner) := by
          by_cases sameOwner : owner = actor
          · subst actor
            simp only [ReactiveApplication.Execution.respond, ite_true,
              PhaseSeedScheduler.ownerWord, List.filter_append, List.filter_cons, List.filter_nil,
              absent, decide_false, Bool.false_eq_true, ite_false, List.append_nil]
          · rw [app.respond_recall_other execution actor owner sameOwner ⟨none⟩]
        have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks countedMenu initial
          horizon (family seeds) remaining (execution.respond app actor ⟨none⟩) responded owner
            coordinate
        rw [afterWord] at words
        rw [← words, word_clock_projection, app.respond_environmentRecall]
        exact clocks

end Vegas.Examples.CommitSeedBroadcast
