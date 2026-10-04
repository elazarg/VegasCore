/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServicePrefix
import Vegas.Pending.ReactiveStateInvariant
import Interaction.ReactiveHistory

/-! # Reading a completed source ancestor from a later native configuration

The rank fixes the typed source position. Its decoder reads the existing store
and only existing completions below that rank. Later completions retain those
fields and contribute no actions to the filtered history. No snapshot is stored
in the runtime, and no later action is treated as part of the earlier source view.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem decodeState?_eq_of_reads_eq {Field : Type}
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    (refs : ContextRefs layout Γ) (left right : EventGraph.Store layout)
    (same : ∀ {name cell} (source : HasVar Γ name cell),
      (refs.get source).get? left = (refs.get source).get? right) :
    decodeState? refs left = decodeState? refs right := by
  induction Γ with
  | nil => rfl
  | cons entry Γ ih =>
      obtain ⟨name, cell⟩ := entry
      have head := same (HasVar.here : HasVar ((name, cell) :: Γ) name cell)
      have tail := ih refs.tail (fun source => same (.there source))
      cases cell <;> simp only [decodeState?, head, tail]

/-- A prefix decoder reads only its starting context and outputs below its
instruction count. Future output fields are irrelevant, even when available. -/
theorem decodeSourcePrefix?_eq_of_prefix_reads_eq
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {names : Finset VarId}
    (program : SourceProgram Player L Γ names) (refs : ContextRefs layout Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (count : Nat) (left right : EventGraph.Store layout) (history : History Player L)
    (context : ∀ {name cell} (source : HasVar Γ name cell),
      (refs.get source).get? left = (refs.get source).get? right)
    (completed : ∀ event, event.val < count →
      (outputs event).get? left = (outputs event).get? right) :
    decodeSourcePrefix? program refs registry revelations outputs count left history =
      decodeSourcePrefix? program refs registry revelations outputs count right history := by
  induction count generalizing Γ names with
  | zero =>
      simp only [decodeSourcePrefix?, decodeState?_eq_of_reads_eq refs left right context]
  | succ count ih =>
      cases program with
      | ret payoffs => rfl
      | sample name fresh law next =>
          rw [decodeSourcePrefix?_sample, decodeSourcePrefix?_sample]
          congr 1
          apply ih
          · intro readName cell source
            cases source with
            | here => exact completed ⟨0, by simp [eventCount]⟩ (Nat.zero_lt_succ count)
            | there prior => exact context prior
          · intro event before
            exact completed event.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ before)
      | commit name owner fresh guard next =>
          rw [decodeSourcePrefix?_commit, decodeSourcePrefix?_commit]
          congr 1
          apply ih
          · intro readName cell source
            cases source with
            | here => exact completed ⟨0, by simp [eventCount]⟩ (Nat.zero_lt_succ count)
            | there prior => exact context prior
          · intro event before
            exact completed event.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ before)
      | reveal published owner name fresh binding unresolved next =>
          rw [decodeSourcePrefix?_reveal, decodeSourcePrefix?_reveal]
          congr 1
          apply ih
          · intro readName cell source
            cases source with
            | here => exact completed ⟨0, by simp [eventCount]⟩ (Nat.zero_lt_succ count)
            | there prior => exact context prior
          · intro event before
            exact completed event.succ (by simpa only [Fin.val_succ] using Nat.succ_lt_succ before)

/-- Reconstruct the source position before this rank using persistent fields
and the chronological actions of lower-ranked events already in the config. -/
def sourceServicePastPrefix? (setup : Setup (Player := Player) (L := L))
    (rank : Nat) (config : (graph setup).Config) : setup.ProtocolState :=
  decodeSourcePrefix? setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) []
    (Revelations.initial setup.context) (outputRef setup.program) rank config.store
    (decodeHistory setup.program ((config.history.filter
      (fun completion => completion.event.val < rank)).map
        (setup.eventGraph.fromModeCompletion .sequential)))

/-- At the actual completed prefix, the retrospective readout is the ordinary
source prefix decoder; it neither drops prior actions nor introduces new ones. -/
theorem sourceServicePastPrefix?_eq_at_prefix
    (setup : Setup (Player := Player) (L := L)) (rank : Nat)
    (config : (graph setup).Config) (ordered : config.cut.IsPrefix rank) :
    sourceServicePastPrefix? setup rank config = sourceServicePrefix? setup rank config := by
  have filtered : config.history.filter (fun completion => completion.event.val < rank) =
      config.history := by
    apply List.filter_eq_self.mpr
    intro completion member
    apply decide_eq_true_eq.mpr
    exact (ordered.2 completion.event).mp
      ((config.history_exact completion.event).mp (List.mem_map.mpr ⟨completion, member, rfl⟩))
  unfold sourceServicePastPrefix? sourceServicePrefix?
  rw [filtered]

/-- Initial fields, lower-ranked outputs and lower-ranked completions are the
entire retrospective decoder input. No future private output is consulted. -/
theorem sourceServicePastPrefix?_congr
    (setup : Setup (Player := Player) (L := L)) (rank : Nat)
    (left right : (graph setup).Config)
    (inputs : left.inputs = right.inputs)
    (outputs : ∀ event, event.val < rank → left.outputs event = right.outputs event)
    (history : left.history.filter (fun completion => completion.event.val < rank) =
      right.history.filter (fun completion => completion.event.val < rank)) :
    sourceServicePastPrefix? setup rank left = sourceServicePastPrefix? setup rank right := by
  unfold sourceServicePastPrefix?
  rw [history]
  apply decodeSourcePrefix?_eq_of_prefix_reads_eq
  · intro name cell source
    apply ((ContextRefs.initial setup.context (outputLayout setup.program)).get source).get?_congr
    change some (left.inputs (inputId source)) = some (right.inputs (inputId source))
    rw [inputs]
  · intro event before
    exact outputs event before

/-- Completing a ready event after all lower ranks have completed cannot
change the retrospective source position, even if its action contains evidence. -/
theorem sourceServicePastPrefix?_complete
    (setup : Setup (Player := Player) (L := L)) (rank : Nat)
    (config : (graph setup).Config)
    (completed : ∀ event, event.val < rank → event ∈ config.cut.completed)
    (event : (graph setup).EventId) (ready : config.cut.Ready event)
    (action : (graph setup).Action event) (value : ((graph setup).outputLayout event).Value) :
    sourceServicePastPrefix? setup rank (config.complete event ready action value) =
      sourceServicePastPrefix? setup rank config := by
  have later : ¬ event.val < rank := fun before => ready.1 (completed event before)
  apply sourceServicePastPrefix?_congr
  · rfl
  · intro query before
    apply config.complete_output_of_ne event query ready action value
    intro same
    exact later (same ▸ before)
  · simp only [EventGraph.Config.complete_history, List.filter_append, List.filter_cons,
      List.filter_nil, decide_eq_false_iff_not.mpr later, Bool.false_eq_true, ↓reduceIte,
      List.append_nil]

/-- This applies to the actual chance law and strategic graph step, with no
restriction on the selected value or any later source policy. -/
theorem sourceServicePastPrefix?_step
    (setup : Setup (Player := Player) (L := L)) (rank : Nat)
    (config next : (graph setup).Config)
    (completed : ∀ event, event.val < rank → event ∈ config.cut.completed)
    (event : (graph setup).EventId) (ready : config.cut.Ready event)
    (action : (graph setup).Action event)
    (supported : next ∈ (config.step event ready action).support) :
    sourceServicePastPrefix? setup rank next = sourceServicePastPrefix? setup rank config := by
  rw [EventGraph.Config.step, PMF.support_map] at supported
  obtain ⟨value, _, rfl⟩ := supported
  exact sourceServicePastPrefix?_complete setup rank config completed event ready action value

/-- Arbitrary native responses and environment commands preserve the earlier
source position once its lower ranks have completed. -/
theorem sourceServicePastPrefix_invariant
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rank : Nat) (seed : (graph setup).Config) :
    (application setup leaks).Invariant (fun state =>
      (∀ event, event.val < rank → event ∈ state.config.cut.completed) ∧
        sourceServicePastPrefix? setup rank state.config =
          sourceServicePastPrefix? setup rank seed) := by
  have graphStep (config next : (graph setup).Config)
      (valid : (∀ event, event.val < rank → event ∈ config.cut.completed) ∧
        sourceServicePastPrefix? setup rank config = sourceServicePastPrefix? setup rank seed)
      (event : (graph setup).EventId) (ready : config.cut.Ready event)
      (action : (graph setup).Action event)
      (supported : next ∈ (config.step event ready action).support) :
      (∀ event, event.val < rank → event ∈ next.cut.completed) ∧
        sourceServicePastPrefix? setup rank next = sourceServicePastPrefix? setup rank seed := by
    refine ⟨?_, (sourceServicePastPrefix?_step setup rank config next valid.1 event ready action
      supported).trans valid.2⟩
    intro query before
    rw [config.step_cut event ready action next supported, EventOrder.Cut.mem_complete]
    exact Or.inr (valid.1 query before)
  refine ⟨?_, ?_, ?_⟩
  · intro state who material valid
    change (∀ event, event.val < rank → event ∈ (submitStep
      (material.call.register state who) who material.call.packet).config.cut.completed) ∧
        sourceServicePastPrefix? setup rank
          (submitStep (material.call.register state who) who material.call.packet).config = _
    rw [submitStep_config, (material.call.register_facts who state).1]
    exact valid
  · intro state message next valid accepted
    obtain ⟨event, _, ready, action, supported⟩ := handle_config_mem_step (runtime setup) state next
      ⟨message.id, message.payload.call⟩ (reactiveHandle_call accepted)
    exact graphStep state.config next.config valid event ready action supported
  · intro state command next valid supported
    cases command with
    | advanceClock =>
        change next ∈ (environmentStep (runtime setup) state .advanceClock).support at supported
        simp only [environmentStep, PMF.mem_support_pure_iff _ _] at supported
        subst next
        exact valid
    | executeSample event =>
        obtain ⟨_, same | moved⟩ := environmentStep_executeSample_config_activated
          (runtime setup) state next event supported
        · rw [same.1]
          exact valid
        · obtain ⟨ready, action, reached, _⟩ := moved
          exact graphStep state.config next.config valid event ready action reached
    | expire event =>
        obtain ⟨_, same | moved⟩ := environmentStep_expire_config_activated
          (runtime setup) state next event supported
        · rw [same.1]
          exact valid
        · obtain ⟨ready, action, reached, _⟩ := moved
          exact graphStep state.config next.config valid event ready action reached

/-- Later policies and scheduler choices retain the same before-rank source
state and own histories, including after terminal completion. -/
theorem sourceServicePastPrefix?_runRounds
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rank : Nat) (before after : (application setup leaks).Execution)
    (ordered : before.application.config.cut.IsPrefix rank)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy) (rounds : Nat)
    (supported : after ∈ ((application setup leaks).runRounds scheduler players rounds
      before).support) :
    sourceServicePastPrefix? setup rank after.application.config =
      sourceServicePrefix? setup rank before.application.config := by
  have valid := (ReactiveApplication.Invariant.policyInvariant (application setup leaks)
      (sourceServicePastPrefix_invariant setup leaks rank before.application.config)
        players).runRounds scheduler rounds before after
    ⟨fun event preceding => (ordered.2 event).mpr preceding, rfl⟩ supported
  exact valid.2.trans (sourceServicePastPrefix?_eq_at_prefix setup rank _ ordered)

/-- Every legal native continuation path preserves this same earlier source
position. Its lower-rank completion premise is propagated by real transitions,
including scheduler boundaries, rather than assumed again at the endpoint. -/
theorem sourceServicePastPrefix_reaches
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (rank : Nat)
    {first last : ((application setup leaks).protocol initial horizon scheduler).History}
    {fuel : Nat}
    (path : ((application setup leaks).protocol initial horizon scheduler).ReachesWithin fuel
      first last)
    (before after : (application setup leaks).Control)
    (firstEq : first.state = some before) (lastEq : last.state = some after)
    (completed : ∀ event, event.val < rank →
      event ∈ before.execution.application.config.cut.completed) :
    (∀ event, event.val < rank → event ∈ after.execution.application.config.cut.completed) ∧
      sourceServicePastPrefix? setup rank after.execution.application.config =
        sourceServicePastPrefix? setup rank before.execution.application.config := by
  let app := application setup leaks
  induction path generalizing before with
  | refl _ history =>
      cases Option.some.inj (firstEq.symm.trans lastEq)
      exact ⟨completed, rfl⟩
  | @step steps history target joint legal reached supported suffix ih =>
      have moved := supported
      change reached ∈ (app.transition initial horizon scheduler history.state joint).support
        at moved
      rw [firstEq] at moved
      obtain ⟨middle, middleEq, _⟩ := app.transition_recall_prefix initial horizon scheduler before
        reached joint moved
      have invariant := sourceServicePastPrefix_invariant setup leaks rank
        before.execution.application.config
      have good := invariant.transition (PMF.pure before.execution.application) horizon scheduler
        (by
          intro state member
          cases (PMF.mem_support_pure_iff _ _).mp member
          exact ⟨completed, rfl⟩)
        (some before) reached joint ⟨completed, rfl⟩ moved
      rw [middleEq] at good
      obtain ⟨finished, same⟩ := ih middle middleEq lastEq good.1
      exact ⟨finished, same.trans good.2⟩

end Vegas
