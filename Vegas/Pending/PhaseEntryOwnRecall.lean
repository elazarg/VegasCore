/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseSeedFreshness
import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseEntryExclusion
import Interaction.ReactiveRecordedResponse

/-! # Actual full recall at the first installation of an attempt -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Every remembered own callback belongs to a componentwise earlier attempt.
This covers silent callbacks and preserves the complete permanent recall. -/
theorem phase_ownRecall_namespace_le_history (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((app).protocol initial horizon scheduler).Trace (some control)) :
    ∀ who, ∀ entry ∈ control.execution.recall who,
      entry.beforeView.application.2.attempt.generation ≤
          control.execution.application.attempt.generation ∧
        entry.beforeView.application.2.attempt.phase ≤
          control.execution.application.attempt.phase := by
  let property := fun execution : (app).Execution => execution.application.Ordered ∧
    ∀ who, ∀ entry ∈ execution.recall who,
      entry.beforeView.application.2.attempt.generation ≤ execution.application.attempt.generation ∧
        entry.beforeView.application.2.attempt.phase ≤ execution.application.attempt.phase
  have invariant : (app).ServiceInvariant scheduler property := {
    respond := by
      intro execution who action valid
      have ordered := (phaseApplication_seedOrder runtime leaks).respond execution who action
        valid.1
      have progress := (phaseApplication_namespace_progress runtime leaks).respond execution who
        action valid.1
      refine ⟨ordered, ?_⟩
      intro owner entry member
      by_cases same : owner = who
      · subst owner
        obtain ⟨emitted, recalled⟩ := (app).respond_recall_entry execution who action
        rw [recalled, List.mem_append, List.mem_singleton] at member
        rcases member with old | rfl
        · have earlier := valid.2 who entry old
          exact ⟨earlier.1.trans progress.1, earlier.2.trans progress.2⟩
        · exact progress
      · rw [(app).respond_recall_other execution who owner same action] at member
        have earlier := valid.2 owner entry member
        exact ⟨earlier.1.trans progress.1, earlier.2.trans progress.2⟩
    environment := by
      intro execution next command valid _ reached
      have ordered := (phaseApplication_seedOrder runtime leaks).environmentStep execution next
        command valid.1 reached
      have progress := (phaseApplication_namespace_progress runtime leaks).environmentStep
        execution next command reached valid.1
      refine ⟨ordered, ?_⟩
      intro owner entry member
      rw [(app).environmentStep_recall execution next command reached] at member
      have earlier := valid.2 owner entry member
      exact ⟨earlier.1.trans progress.1, earlier.2.trans progress.2⟩ }
  exact ((invariant.history initial horizon (by
    intro state supported
    exact ⟨initialized state supported, by intro owner entry impossible; cases impossible⟩)
      trace).2)

/-- Installing a different namespace leaves no earlier own callback at that
new address, even when the callback itself was silent. -/
theorem phase_ownRecall_fresh_after_environment (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) (before : (app).Control)
    (trace : ((app).protocol initial horizon scheduler).Trace (some before))
    (next : (app).Execution) (command : (app).Command)
    (reached : next ∈ (before.execution.environmentStep (app) command).support)
    (different : before.execution.application.attempt ≠ next.application.attempt) :
    ∀ who, ∀ entry ∈ next.recall who,
      entry.beforeView.application.2.attempt ≠ next.application.attempt := by
  have ordered := (phaseApplication_seedOrder runtime leaks).history initial horizon scheduler
    initialized trace
  have strict := PhaseSeedFreshness.changed_namespace_strict runtime leaks before.execution next
    command ordered reached different
  intro who entry member equal
  rw [(app).environmentStep_recall before.execution next command reached] at member
  have earlier := phase_ownRecall_namespace_le_history runtime leaks initial initialized horizon
    scheduler trace who entry member
  have generation := congrArg CommitAttemptId.generation equal
  have phase := congrArg CommitAttemptId.phase equal
  rcases strict with strict | strict <;> omega

/-- Every genuine history has an actual prefix at which its present attempt
was installed and no callback in the permanent own recall used that address.
The prefix is idle and retains its original network and recalled past. Its
application is an actual initial draw or saves the current exclusion. -/
theorem phase_attempt_entry_prefix (menu : (app).ResponseMenu) (initial : PMF (app).State)
    (initialized : ∀ state ∈ initial.support, state.Ordered) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : (menu.protocol initial horizon scheduler).Trace (some control)) :
    ∃ (entry : (app).Control)
      (entryTrace : (menu.protocol initial horizon scheduler).Trace (some entry)),
      TracePrefix entryTrace trace ∧ entry.execution.application.attempt =
        control.execution.application.attempt ∧ entry.actor = none ∧
      ((∃ input ∈ initial.support, entry.execution.application = input) ∨
        entry.execution.application.entry.excluded =
          entry.execution.application.current.excluded) ∧
      ∀ who, ∀ record ∈ entry.execution.recall who,
        record.beforeView.application.2.attempt ≠ entry.execution.application.attempt := by
  have along : ∀ {state} (current : (menu.protocol initial horizon scheduler).Trace state),
      ∀ target : (app).Control, state = some target →
      ∃ (entry : (app).Control)
        (entryTrace : (menu.protocol initial horizon scheduler).Trace (some entry)),
        TracePrefix entryTrace current ∧ entry.execution.application.attempt =
          target.execution.application.attempt ∧ entry.actor = none ∧
        ((∃ input ∈ initial.support, entry.execution.application = input) ∨
          entry.execution.application.entry.excluded =
            entry.execution.application.current.excluded) ∧
        ∀ who, ∀ record ∈ entry.execution.recall who,
          record.beforeView.application.2.attempt ≠ entry.execution.application.attempt := by
    intro state current
    induction current with
    | start => intro target impossible; cases impossible
    | @extend source state prior joint legal reached ih =>
        intro target equal
        subst state
        have realized : some target ∈
            ((app).transition initial horizon scheduler source joint).support := reached
        cases source with
        | none =>
            obtain ⟨input, _supported, equation⟩ := PMF.support_map .. ▸ realized
            cases Option.some.inj equation
            exact ⟨_, .extend prior joint legal reached, .refl, rfl, rfl,
              Or.inl ⟨input, _supported, rfl⟩,
              by intro who record impossible; cases impossible⟩
        | some before =>
            by_cases same : before.execution.application.attempt =
                target.execution.application.attempt
            · obtain ⟨entry, entryTrace, retained, address, idle, origin, fresh⟩ := ih before rfl
              exact ⟨entry, entryTrace, .extend retained joint legal reached,
                address.trans same, idle, origin, fresh⟩
            · have previous := (menu).toRawTrace initial horizon scheduler prior
              cases active : before.actor with
              | some who =>
                  simp only [ReactiveApplication.transition, active] at realized
                  cases (PMF.mem_support_pure_iff ..).mp realized
                  apply False.elim
                  apply same
                  generalize ((joint who).getD ⟨none⟩) = action
                  rcases action with ⟨_ | material⟩ <;> rfl
              | none =>
                  cases remaining : before.remaining with
                  | zero =>
                      simp only [ReactiveApplication.transition, active, remaining] at realized
                      cases (PMF.mem_support_pure_iff ..).mp realized
                      exact False.elim (same rfl)
                  | succ remaining =>
                      simp only [ReactiveApplication.transition, active, remaining,
                        PMF.support_bind, Set.mem_iUnion, PMF.support_map] at realized
                      obtain ⟨command, _selected, next, supported, equation⟩ := realized
                      cases Option.some.inj equation
                      have idle : command.actor? (app) = none := by
                        cases command with
                        | activate owner =>
                            simp only [ReactiveApplication.Execution.environmentStep,
                              PMF.support_map] at supported
                            obtain ⟨learned, ⟨selected, _chosen, rfl⟩, rfl⟩ := supported
                            exact False.elim (same rfl)
                        | «include» id => rfl
                        | application operation => rfl
                        | wait => rfl
                      have installation := phaseApplication_namespaceInstallation runtime leaks
                      have saved := installation.environmentStep before.execution next command
                        supported same
                      refine ⟨_, .extend prior joint legal reached, .refl, rfl, idle,
                        Or.inr saved, ?_⟩
                      exact phase_ownRecall_fresh_after_environment runtime leaks initial
                        initialized horizon scheduler before previous next command supported same
  exact along trace control rfl

/-- For the actual initialized application the SAME first-installation prefix
is idle, has fresh complete recall, and saves its actual permanent exclusion.
Inherited excluded owners and automatic phase skips remain permitted. -/
theorem phase_attempt_installed_prefix (menu : (app).ResponseMenu)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (control : (app).Control)
    (trace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
      (some control)) :
    ∃ (entry : (app).Control)
      (entryTrace : (menu.protocol (inputs.map (PhaseRuntimeState.initial plan)) horizon
        scheduler).Trace (some entry)),
      TracePrefix entryTrace trace ∧
      entry.execution.application.attempt = control.execution.application.attempt ∧
      entry.actor = none ∧
      entry.execution.application.entry.excluded = entry.execution.application.current.excluded ∧
      ∀ who, ∀ record ∈ entry.execution.recall who,
        record.beforeView.application.2.attempt ≠ entry.execution.application.attempt := by
  have initialized : ∀ state ∈ (inputs.map (PhaseRuntimeState.initial plan)).support,
      state.Ordered := by
    intro state supported
    obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    exact PhaseRuntimeState.initial_ordered plan draw
  obtain ⟨entry, entryTrace, retained, same, idle, origin, fresh⟩ :=
    phase_attempt_entry_prefix runtime leaks menu (inputs.map (PhaseRuntimeState.initial plan))
      initialized horizon scheduler control trace
  refine ⟨entry, entryTrace, retained, same, idle, ?_, fresh⟩
  rcases origin with ⟨input, supported, equation⟩ | saved
  · obtain ⟨draw, _supported, rfl⟩ := PMF.support_map .. ▸ supported
    rw [equation]
    exact PhaseRuntimeState.initial_entry_excluded plan draw
  · exact saved

end Vegas.EventGraphRuntime
