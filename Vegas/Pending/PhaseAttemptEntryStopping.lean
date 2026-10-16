/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseEntryOwnRecall
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # Full recall at the first actual visit to an attempt namespace -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Stop at the first exact phase and generation or first public exclusion.
The preinitialization state is allowed to draw its original initial input. -/
def phaseAttemptEntryStop (target : CommitAttemptId) : (app).ProtocolState → Prop
  | none => False
  | some control => control.execution.application.current.excluded ≠ ∅ ∨
      control.execution.application.attempt = target

/-- First visiting the exact phase and generation leaves every earlier own
callback outside that namespace. The original full execution is retained. -/
theorem phase_attempt_first_visit_fresh (menu : (app).ResponseMenu)
    (initial : PMF (app).State) (initialized : ∀ state ∈ initial.support, state.Ordered)
    (horizon : Nat) (scheduler : (app).Scheduler)
    (certificate : (menu.protocol initial horizon scheduler).WellFoundedHistories)
    (profile : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (target : CommitAttemptId) :
    let E := menu.protocol initial horizon scheduler
    let model := menu.information initial horizon scheduler
    let stopped := fun history : E.History =>
      phaseAttemptEntryStop runtime leaks target history.state
    ∀ final ∈ (model.runBehavioralUntil certificate profile stopped E.initHistory).support,
      ∀ control, final.state = some control → control.execution.application.attempt = target →
        control.actor = none ∧ ∀ who, ∀ record ∈ control.execution.recall who,
          record.beforeView.application.2.attempt ≠ target := by
  classical
  intro E model stopped
  let property := fun history : E.History =>
    ∀ control, history.state = some control → control.execution.application.attempt = target →
      control.actor = none ∧ ∀ who, ∀ record ∈ control.execution.recall who,
        record.beforeView.application.2.attempt ≠ target
  apply model.runBehavioralUntil_support_history_closed certificate profile stopped property
  · intro before going running _holds after supported control equal address
    obtain ⟨joint, legal, reached⟩ :=
      (model.mem_support_runBehavioralFrom_one profile running supported).1
    have realized : some control ∈
        ((app).transition initial horizon scheduler before.state joint).support := equal ▸ reached
    cases state : before.state with
    | none =>
        simp only [ReactiveApplication.transition, state, PMF.support_map] at realized
        obtain ⟨input, _member, equation⟩ := realized
        cases Option.some.inj equation
        refine ⟨rfl, ?_⟩
        intro who record impossible
        cases impossible
    | some previous =>
        have notTarget : previous.execution.application.attempt ≠ target := by
          intro same
          exact going (by simp only [stopped, phaseAttemptEntryStop, state]; exact Or.inr same)
        have raw : ((app).protocol initial horizon scheduler).Trace (some previous) :=
          state ▸ menu.toRawTrace initial horizon scheduler before.trace
        rw [state] at realized
        cases active : previous.actor with
        | some who =>
            simp only [ReactiveApplication.transition, active] at realized
            cases (PMF.mem_support_pure_iff ..).mp realized
            apply False.elim
            apply notTarget
            generalize ((joint who).getD ⟨none⟩) = action at address
            rcases action with ⟨_ | material⟩ <;> exact address
        | none =>
            cases remaining : previous.remaining with
            | zero =>
                simp only [ReactiveApplication.transition, active, remaining] at realized
                cases (PMF.mem_support_pure_iff ..).mp realized
                exact False.elim (notTarget address)
            | succ remaining =>
                simp only [ReactiveApplication.transition, active, remaining,
                  PMF.support_bind, Set.mem_iUnion, PMF.support_map] at realized
                obtain ⟨command, _selected, next, reached, equation⟩ := realized
                cases Option.some.inj equation
                have different : previous.execution.application.attempt ≠
                    next.application.attempt := fun same => notTarget (same.trans address)
                have idle : command.actor? (app) = none := by
                  cases command with
                  | activate owner =>
                      simp only [ReactiveApplication.Execution.environmentStep,
                        PMF.support_map] at reached
                      obtain ⟨learned, ⟨selected, _supported, rfl⟩, rfl⟩ := reached
                      exact False.elim (different rfl)
                  | «include» id => rfl
                  | application operation => rfl
                  | wait => rfl
                have fresh := phase_ownRecall_fresh_after_environment runtime leaks initial
                  initialized horizon scheduler previous raw next command reached different
                exact ⟨idle, by simpa only [address] using fresh⟩
  · intro control impossible
    cases impossible

end Vegas.EventGraphRuntime
