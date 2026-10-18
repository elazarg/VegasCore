/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastOriginalBindingWord
import Interaction.ReactiveRecallInvariant
import Mathlib.Data.List.Nodup

/-! # A remembered original omission cannot be replaced at the same clock -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- Every retained original response has a distinct relative clock, including
when the current phase is retired, exhausted or no longer requests its owner. -/
theorem original_recalled_clocks_nodup (menu : app.ResponseMenu) (seeds : Seeds)
    (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) :
    ((PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
      (current.execution.recall owner)).map Prod.fst).Nodup := by
  classical
  have prefixes : ∀ past : List app.PlayerEntry, past <+: current.execution.recall owner →
      ((PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner past).map
        Prod.fst).Nodup := by
    intro past
    induction past using List.reverseRecOn with
    | nil => intro _kept; simp [PhaseSeedScheduler.ownerWord]
    | append_singleton earlier entry ih =>
        intro kept
        by_cases requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
            (originalCoordinate owner)
        · obtain ⟨later, equation⟩ := kept
          have recalled : current.execution.recall owner = earlier ++ entry :: later := by
            rw [← equation]
            simp only [List.append_assoc, List.singleton_append]
          obtain ⟨before, prior, _retained, active, ownPast, viewed, _allowed⟩ :=
            menu.recorded_response_at initial horizon (family seeds) current trace owner
              earlier entry later recalled
          have publicRequest := requested
          rw [viewed] at publicRequest
          change PhaseRuntimeState.requests before.execution.application.publicView owner
            (originalCoordinate owner) at publicRequest
          have valid := raw_native_valid (family seeds) before
            (menu.toRawTrace initial horizon (family seeds) prior)
          have request := (before.execution.application.requests_publicView valid owner
            (originalCoordinate owner)).mp publicRequest
          have clocks := original_service_clocks_prefix menu seeds before prior owner active request
          have unique : (PhaseSeedScheduler.serviceClocks runtime leaks
              (originalCoordinate owner) owner (before.execution.recall owner)
                (before.execution.observe app owner)).Nodup :=
            (by decide : ([0, 2, 3] : List Nat).Nodup).sublist clocks.sublist
          rw [ownPast, ← viewed] at unique
          simpa [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput,
            PhaseSeedScheduler.ownerWord, requested] using unique
        · have previous : earlier <+: current.execution.recall owner :=
            (List.prefix_append earlier [entry]).trans kept
          simpa [PhaseSeedScheduler.ownerWord, requested] using ih previous
  exact prefixes _ (List.prefix_refl _)

private theorem recalled_silent_emission (menu : app.ResponseMenu) (seeds : Seeds)
    (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (silent : entry.action.transmission = none) : entry.emitted = none := by
  let faithful : app.ServiceInvariant (family seeds) (fun execution =>
      ∀ entry ∈ execution.recall owner,
        entry.action.transmission = none → entry.emitted = none) := {
    respond := fun execution actor action valid =>
      (app.silentEmission_invariant (fun _ _ _ => PMF.pure action) owner).respond
        execution actor action valid (by simp)
    environment := fun execution next command valid _selected moved =>
      (app.silentEmission_invariant (fun _ _ _ => PMF.pure ⟨none⟩) owner).environment
        execution next command valid moved }
  exact faithful.history initial horizon
    (fun _ _ _ member => (List.not_mem_nil member).elim)
      (menu.toRawTrace initial horizon (family seeds) trace) entry recorded silent

private theorem idle_recorded_wait_no_emission (menu : app.ResponseMenu) (seeds : Seeds)
    (remaining : Nat) (execution : app.Execution)
    (trace : (menu.protocol initial horizon (family seeds)).Trace
      (some ⟨remaining, none, execution⟩)) (owner : Player)
    (entry : app.PlayerEntry) (recorded : entry ∈ execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : entry.action.transmission = none) (clock : Nat)
    (physical : entry.beforeView.application.2.native.clock = clock) :
    clock ∉ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
      execution := by
  classical
  have omitted := recalled_silent_emission menu seeds _ trace owner entry recorded silent
  obtain ⟨before, prior, _kept, _active, viewed, _allowed, _later, _past⟩ :=
    menu.recorded_response_prefix initial horizon (family seeds) _ trace owner entry recorded
  have raw := menu.toRawTrace initial horizon (family seeds) prior
  have valid := raw_native_valid (family seeds) before raw
  have publicRequest := requested
  rw [viewed] at publicRequest
  change PhaseRuntimeState.requests before.execution.application.publicView owner
    (originalCoordinate owner) at publicRequest
  have request := (before.execution.application.requests_publicView valid owner
    (originalCoordinate owner)).mp publicRequest
  have stamp := original_timer (family seeds) before raw request.1.symm owner request.2.2.1.1
  have age : entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock = clock := by
    rw [viewed]
    change before.execution.application.current.native.clock -
      (before.execution.application.current.native.activatedAt (bindingEvent owner)).getD
        before.execution.application.current.native.clock = clock
    rw [stamp, Option.getD_some, Nat.sub_zero]
    rw [viewed] at physical
    exact physical
  let word := PhaseSeedScheduler.ownerWord runtime leaks (originalCoordinate owner) owner
    (execution.recall owner)
  have remembered : (clock, []) ∈ word := by
    apply List.mem_map.mpr
    refine ⟨entry, List.mem_filter.mpr ⟨recorded, decide_eq_true requested⟩, ?_⟩
    simp only [omitted, Option.toList_none, List.filter_nil]
    change (entry.beforeView.application.2.native.clock -
      (entry.beforeView.application.2.native.activatedAt (bindingEvent owner)).getD
        entry.beforeView.application.2.native.clock, []) = (clock, [])
    exact Prod.ext age rfl
  intro member
  obtain ⟨pair, emitted, sameClock⟩ := List.mem_map.mp member
  have words := PhaseSeedScheduler.idle_wordRecall_of_trace runtime leaks menu initial horizon
    (family seeds) remaining execution trace
  rw [PhaseSeedScheduler.localInput_word, words owner (originalCoordinate owner)] at emitted
  obtain ⟨record, retained, packet⟩ := List.mem_flatMap.mp emitted
  obtain ⟨message, input, same⟩ := List.mem_map.mp packet
  have atClock : record.1 = clock := (congrArg Prod.fst same).trans sameClock
  have unique := original_recalled_clocks_nodup menu seeds _ trace owner
  have equal : record = (clock, []) := List.inj_on_of_nodup_map unique retained remembered atClock
  rw [equal] at input
  exact List.not_mem_nil input

/-- A literal original WAIT at a physical clock rules out every emission at
that clock in the same entire later history. No later policy restriction or
already-present receipt is assumed. -/
theorem original_recorded_wait_no_emission (menu : app.ResponseMenu)
    (silence : ∀ owner past view, (⟨none⟩ : app.Action) ∈ menu.actions owner past view)
    (seeds : Seeds) (current : app.Control)
    (trace : (menu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (entry : app.PlayerEntry) (recorded : entry ∈ current.execution.recall owner)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner
      (originalCoordinate owner))
    (silent : entry.action.transmission = none) (clock : Nat)
    (physical : entry.beforeView.application.2.native.clock = clock) :
    clock ∉ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner) owner
      current.execution := by
  rcases current with ⟨remaining, active, execution⟩
  cases active with
  | none =>
      exact idle_recorded_wait_no_emission menu seeds remaining execution trace owner entry
        recorded requested silent clock physical
  | some actor =>
      obtain ⟨responded⟩ := menu.trace_respond initial horizon (family seeds) remaining execution
        actor ⟨none⟩ trace (silence actor _ _)
      exact idle_recorded_wait_no_emission menu seeds remaining (execution.respond app actor ⟨none⟩)
        responded owner entry (app.respond_recall_mono execution actor owner ⟨none⟩ recorded)
          requested silent clock physical

/-- With a good original service bit, omitting both clock zero and clock two
precludes original binding acceptance under every actual counted continuation. -/
theorem original_good_binding_waits_unaccepted (seeds : Seeds) (current : app.Control)
    (trace : (countedMenu.protocol initial horizon (family seeds)).Trace (some current))
    (owner : Player) (good : seeds.2 owner = true)
    (first last : app.PlayerEntry)
    (firstMember : first ∈ current.execution.recall owner)
    (lastMember : last ∈ current.execution.recall owner)
    (firstRequest : PhaseRuntimeState.requests first.beforeView.application.2 owner
      (originalCoordinate owner))
    (lastRequest : PhaseRuntimeState.requests last.beforeView.application.2 owner
      (originalCoordinate owner))
    (firstSilent : first.action.transmission = none)
    (lastSilent : last.action.transmission = none)
    (firstClock : first.beforeView.application.2.native.clock = 0)
    (lastClock : last.beforeView.application.2.native.clock = 2) :
    ¬ PhaseService.BindingAccepted runtime leaks (originalCoordinate owner) owner
      current.execution := by
  have missingZero := original_recorded_wait_no_emission countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seeds current trace owner first firstMember
      firstRequest firstSilent 0 firstClock
  have missingTwo := original_recorded_wait_no_emission countedMenu
    (PhaseCount.silence_onePacket runtime leaks bounds) seeds current trace owner last lastMember
      lastRequest lastSilent 2 lastClock
  intro accepted
  have raw := countedMenu.toRawTrace initial horizon (family seeds) trace
  rw [initial_eq_compiled] at raw
  have resolved := PhaseService.bindingAccepted_resolved runtime leaks plan
    (setup.initialLaw.map encodeInputs) horizon (family seeds) raw
      (originalCoordinate owner) owner accepted
  have either : 0 ∈ PhaseService.bindingEmissionClocks runtime leaks (originalCoordinate owner)
      owner current.execution ∨ 2 ∈ PhaseService.bindingEmissionClocks runtime leaks
        (originalCoordinate owner) owner current.execution := by
    simpa only [good, lateClock, ite_true] using
      (original_binding_accepted_iff_clocks seeds current trace owner resolved).mp accepted
  exact either.elim missingZero missingTwo

end Vegas.Examples.CommitSeedBroadcast
