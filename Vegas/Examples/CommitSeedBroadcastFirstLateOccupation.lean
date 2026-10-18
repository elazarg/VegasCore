/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastCallbackReplay
import Vegas.Examples.CommitSeedBroadcastAudit
import Interaction.ReactiveRecordedResponse
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveRoundOccupation

/-! # The retained first-late input is a genuine unique native decision -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

/-- The literal first response, retaining the actual complete activation view. -/
def initialWaitEntry (owner : Player) : app.PlayerEntry :=
  ⟨(initialCallback owner).observe app owner, ⟨none⟩, none⟩

theorem quietStart_recall (owner : Player) :
    quietStart.recall owner = [initialWaitEntry owner] := by
  fin_cases owner <;> rfl

theorem initialWaitEntry_clock (owner : Player) :
    (initialWaitEntry owner).beforeView.application.2.native.clock = 0 := by
  fin_cases owner <;> exact initialState_clock

private theorem physicalCallbacks_cons (players : Player → app.Policy) (owner : Player)
    (owners : List Player) (execution : app.Execution) :
    physicalCallbacks players (owner :: owners) execution =
      (app.dispatch players (.activate owner) (physicalExecution execution)).bind
        (physicalCallbacks players owners) := by
  change ((app.dispatch players (.activate owner) (physicalExecution execution)).bind
    (commandComposition players (owners.map ReactiveApplication.Command.activate))).map
      physicalExecution = _
  rw [PMF.map_bind]
  apply bind_congr_on_support
  intro next _
  exact commandComposition_physical players _ next

private theorem physicalCallbacks_cons_support (players : Player → app.Policy) (owner : Player)
    (owners : List Player) (execution final : app.Execution)
    (reached : final ∈ (physicalCallbacks players (owner :: owners) execution).support) :
    ∃ action, action ∈ (players owner ((completeActivation (physicalExecution execution)
      owner).recall owner) ((completeActivation (physicalExecution execution) owner).observe
        app owner)).support ∧ final ∈ (physicalCallbacks players owners
          ((completeActivation (physicalExecution execution) owner).respond app owner
            action)).support := by
  rw [physicalCallbacks_cons, ReactiveApplication.dispatch, completeActivation_law,
    PMF.pure_bind] at reached
  change final ∈ (((players owner ((completeActivation (physicalExecution execution)
    owner).recall owner) ((completeActivation (physicalExecution execution) owner).observe
      app owner)).map ((completeActivation (physicalExecution execution) owner).respond
        app owner)).bind (physicalCallbacks players owners)).support at reached
  rw [PMF.bind_map, PMF.support_bind] at reached
  obtain ⟨action, chosen, future⟩ := Set.mem_iUnion₂.mp reached
  exact ⟨action, chosen, future⟩

private theorem response_publicView (execution : app.Execution) (owner : Player)
    (action : app.Action) :
    (execution.respond app owner action).application.publicView =
      execution.application.publicView := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some material => exact PhaseCount.submit_publicView execution.application owner material

private theorem physicalCallbacks_publicView (players : Player → app.Policy)
    (owners : List Player) (execution final : app.Execution)
    (reached : final ∈ (physicalCallbacks players owners execution).support) :
    final.application.publicView = execution.application.publicView := by
  induction owners generalizing execution with
  | nil =>
      simp only [physicalCallbacks, commandComposition, List.map_nil, List.foldr_nil,
        PMF.pure_map, physicalExecution_idempotent] at reached
      have same : final = physicalExecution execution := by
        exact (PMF.mem_support_pure_iff _ _).mp reached
      subst final
      rfl
  | cons owner owners ih =>
      obtain ⟨action, _chosen, future⟩ := physicalCallbacks_cons_support players owner owners
        execution final reached
      exact (ih _ future).trans (response_publicView _ owner action)

private theorem physicalCallbacks_no_own_response (players : Player → app.Policy)
    (owners : List Player) (owner : Player) (absent : owner ∉ owners)
    (execution final : app.Execution)
    (reached : final ∈ (physicalCallbacks players owners execution).support) :
    final.recall owner = execution.recall owner := by
  induction owners generalizing execution with
  | nil =>
      simp only [physicalCallbacks, commandComposition, List.map_nil, List.foldr_nil,
        PMF.pure_map, physicalExecution_idempotent] at reached
      have same : final = physicalExecution execution :=
        (PMF.mem_support_pure_iff _ _).mp reached
      subst final
      rfl
  | cons actor owners ih =>
      have different : owner ≠ actor := fun same => absent (List.mem_cons.mpr (Or.inl same))
      have tail : owner ∉ owners := fun member => absent (List.mem_cons_of_mem actor member)
      obtain ⟨action, _chosen, future⟩ := physicalCallbacks_cons_support players actor owners
        execution final reached
      rw [ih tail _ future, app.respond_recall_other _ actor owner different action]
      rfl

/-- Each owner in the callback permutation adds exactly one real response
record, whatever its raw action or hidden preparation happens to be. -/
theorem physicalCallbacks_unique_record (players : Player → app.Policy)
    (owners : List Player) (distinct : owners.Nodup) (owner : Player) (member : owner ∈ owners)
    (execution final : app.Execution)
    (reached : final ∈ (physicalCallbacks players owners execution).support) :
    ∃ entry, final.recall owner = execution.recall owner ++ [entry] ∧
      entry.beforeView.application.2 = execution.application.publicView := by
  induction owners generalizing execution with
  | nil => cases member
  | cons actor owners ih =>
      obtain ⟨action, _chosen, future⟩ := physicalCallbacks_cons_support players actor owners
        execution final reached
      have noRepeat := List.nodup_cons.mp distinct
      rcases List.mem_cons.mp member with same | later
      · subst owner
        let active := completeActivation (physicalExecution execution) actor
        obtain ⟨emitted, word⟩ := app.respond_recall_entry active actor action
        have after := physicalCallbacks_no_own_response players owners actor noRepeat.1
          (active.respond app actor action) final future
        refine ⟨⟨active.observe app actor, action, emitted⟩, after.trans word, ?_⟩
        rfl
      · by_cases same : owner = actor
        · exact (noRepeat.1 (same ▸ later)).elim
        · obtain ⟨entry, word, viewed⟩ := ih noRepeat.2 later _ future
          refine ⟨entry, ?_, viewed.trans (response_publicView _ actor action)⟩
          rw [app.respond_recall_other _ actor owner same action] at word
          exact word

theorem nativePartitionedOrder_nodup (seed : Seeds) :
    (nativePartitionedOrder seed).Nodup := by
  change ([seed.1 0, seed.1 1, seed.1 2].filter seed.2 ++
    [seed.1 0, seed.1 1, seed.1 2].filter fun owner => !(seed.2 owner)).Nodup
  have ne01 : seed.1 0 ≠ seed.1 1 := fun same => (by decide : (0 : Player) ≠ 1)
    (seed.1.injective same)
  have ne02 : seed.1 0 ≠ seed.1 2 := fun same => (by decide : (0 : Player) ≠ 2)
    (seed.1.injective same)
  have ne12 : seed.1 1 ≠ seed.1 2 := fun same => (by decide : (1 : Player) ≠ 2)
    (seed.1.injective same)
  cases first : seed.2 (seed.1 0) <;> cases second : seed.2 (seed.1 1) <;>
    cases third : seed.2 (seed.1 2) <;>
      simp [first, second, third, ne01, ne02, ne12, Ne.symm ne01, Ne.symm ne02, Ne.symm ne12]

theorem nativePartitionedOrder_mem (seed : Seeds) (owner : Player) :
    owner ∈ nativePartitionedOrder seed := by
  have member : owner ∈ List.ofFn seed.1 := List.mem_ofFn.mpr
    ⟨seed.1.symm owner, seed.1.apply_symm_apply owner⟩
  change owner ∈ (List.ofFn seed.1).filter seed.2 ++
    (List.ofFn seed.1).filter fun who => !(seed.2 who)
  cases bit : seed.2 owner
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨member, by simp only [bit, Bool.not_false]⟩)
  · exact List.mem_append_left _ (List.mem_filter.mpr ⟨member, bit⟩)

/-- The actual initialized quiet experiment contains precisely the initial
WAIT and one clock-two response record for each owner. -/
theorem initialized_firstLate_own_word (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players 14 initialExecution).support)
    (owner : Player) :
    ∃ entry, final.recall owner = [initialWaitEntry owner, entry] ∧
      entry.beforeView.application.2 = quietStart.application.publicView ∧
      firstLateInput owner final = some ([initialWaitEntry owner], entry.beforeView) := by
  have projected : physicalExecution final ∈
      ((app.runRounds (family seed) players 14 initialExecution).map physicalExecution).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨final, reached, rfl⟩
  rw [show 14 = 5 + 9 by decide, app.runRounds_add, quietStart_law seed players waited,
    PMF.pure_bind, nohelper_first_late_physical_kernel] at projected
  obtain ⟨entry, word, observed⟩ := physicalCallbacks_unique_record players _
    (nativePartitionedOrder_nodup seed) owner (nativePartitionedOrder_mem seed owner)
      quietStart (physicalExecution final) projected
  change final.recall owner = quietStart.recall owner ++ [entry] at word
  rw [quietStart_recall] at word
  change final.recall owner = [initialWaitEntry owner, entry] at word
  refine ⟨entry, word, observed, ?_⟩
  rw [firstLateInput, word]
  rfl

/-- On the whole actual support the retained selector is a unique real
clock-two response, with the literal old own word retained rather than replaced. -/
theorem initialized_firstLate_unique_clock_two (seed : Seeds) (players : Player → app.Policy)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players 14 initialExecution).support)
    (owner : Player) :
    ∃ entry ∈ final.recall owner,
      entry.beforeView.application.2.native.clock = 2 ∧
      (∀ other ∈ final.recall owner,
        other.beforeView.application.2.native.clock = 2 → other = entry) ∧
      firstLateInput owner final = some ([initialWaitEntry owner], entry.beforeView) := by
  obtain ⟨entry, word, publicView, selected⟩ :=
    initialized_firstLate_own_word seed players waited final reached owner
  have clock : entry.beforeView.application.2.native.clock = 2 :=
    (congrArg (fun view : PhasePublicView graph => view.native.clock) publicView).trans
      quietStart_clock
  refine ⟨entry, by rw [word]; exact List.mem_cons_of_mem _ (List.mem_singleton_self _), clock,
    ?_, selected⟩
  intro other recorded time
  rw [word] at recorded
  rcases List.mem_cons.mp recorded with same | later
  · rw [same, initialWaitEntry_clock] at time
    omega
  · exact (List.mem_singleton.mp later)

/-- A positive original seed realizes the same initialized raw physical prefix
under the installed scheduler mixture. The seed is never redrawn at the callback. -/
theorem initialized_firstLate_mixed_support (seed : Seeds)
    (supported : seed ∈ nativeSeedLaw.support)
    (players : Player → app.Policy) (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players 14 initialExecution).support) :
    final ∈ (app.runRounds scheduler players 14 initialExecution).support := by
  have law := app.schedulerMixture_realize nativeSeedLaw family players 14 initialState
  change (nativeSeedLaw.bind fun memory => app.runRounds (family memory) players 14
    initialExecution) = app.runRounds scheduler players 14 initialExecution at law
  rw [← law, PMF.support_bind]
  exact Set.mem_iUnion₂.mpr ⟨seed, supported, reached⟩

/-- The selector is exactly the information of a genuine actor history in the
original mixed raw model, including zero-equilibrium-reach forced quiet prefixes. -/
theorem initialized_firstLate_raw_information (seed : Seeds)
    (supported : seed ∈ nativeSeedLaw.support) (players : Player → app.Policy)
    (covered : ∀ owner past view response, response ∈ (players owner past view).support →
      response ∈ rawMenu.actions owner past view)
    (waited : ∀ owner, players owner ((initialCallback owner).recall owner)
      ((initialCallback owner).observe app owner) = PMF.pure ⟨none⟩)
    (final : app.Execution)
    (reached : final ∈ (app.runRounds (family seed) players 14 initialExecution).support)
    (owner : Player) :
    ∃ history : rawProtocol.History,
      rawProtocol.active history.state owner ∧
      rawModel.infoOf owner history.trace = firstLateInput owner final ∧
      ∃ remaining execution, history.state = some ⟨remaining, some owner, execution⟩ ∧
        execution.application.current.native.clock = 2 ∧
        execution.recall owner = [initialWaitEntry owner] := by
  obtain ⟨entry, word, publicView, selected⟩ :=
    initialized_firstLate_own_word seed players waited final reached owner
  have actual := initialized_firstLate_mixed_support seed supported players final reached
  have rounds : final ∈ (app.roundsFrom initial scheduler players 14).support := by
    simpa only [ReactiveApplication.roundsFrom, initial, PMF.pure_bind, initialExecution]
      using actual
  obtain ⟨finalTrace⟩ := rawMenu.trace_roundsFrom initial horizon scheduler players covered 14
    (by decide) final rounds
  have recorded : final.recall owner = [initialWaitEntry owner] ++ entry :: [] := word
  obtain ⟨before, prior, _kept, active, oldWord, viewed, _allowed⟩ :=
    rawMenu.recorded_response_at initial horizon scheduler ⟨horizon - 14, none, final⟩ finalTrace
      owner [initialWaitEntry owner] entry [] recorded
  let history : rawProtocol.History := ⟨some before, prior⟩
  refine ⟨history, ?_, ?_, before.remaining, before.execution, ?_, ?_, oldWord⟩
  · change before.actor = some owner
    exact active
  · rw [selected]
    change (rawMenu.signals initial horizon scheduler).infoOf owner prior = _
    rw [rawMenu.info]
    simp only [ReactiveApplication.observe, active, ite_true]
    rw [oldWord, ← viewed]
  · cases before
    simp only at active
    cases active
    rfl
  · have clock := (congrArg (fun view : PhasePublicView graph => view.native.clock)
      publicView).trans quietStart_clock
    rw [viewed] at clock
    exact clock

end Vegas.Examples.CommitSeedBroadcast
