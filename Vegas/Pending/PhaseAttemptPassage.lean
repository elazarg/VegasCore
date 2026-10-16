/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseAttemptCheckpoint
import Vegas.Pending.PhaseClearTraceProgress
import GameTheoryExtensions.Analysis.Protocol.PassageBayes
import GameTheoryExtensions.Analysis.Protocol.StoppedHistoryInvariant

/-! # Clear information passage cannot return after an attempt exit -/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

omit [DecidableEq Player] in
private theorem reached_prefix {E : ExecutionProtocol Player} {fuel : Nat}
    {first last : E.History} (reached : E.ReachesWithin fuel first last) :
    TracePrefix first.trace last.trace := by
  induction reached with
  | refl => exact .refl
  | step joint legal realized rest ih =>
      exact (TracePrefix.extend .refl joint legal realized).trans ih

omit [DecidableEq Player] in
private theorem ancestor_stable {E : ExecutionProtocol Player} (M : InformationModel E)
    {who : Player} (site : M.InformationSite who) (antichain : site.IsHistoryAntichain)
    (ending final : E.History) (reached : E.HistoryReaches ending final)
    (noLater : ∀ prior : M.InformationHistory who site.1,
      E.HistoryReaches ending prior.1 → prior.1 = ending) :
    site.ancestor? M final = site.ancestor? M ending := by
  classical
  apply Option.ext
  intro prior
  rw [site.ancestor?_eq_some_iff M antichain,
    site.ancestor?_eq_some_iff M antichain]
  constructor
  · rintro ⟨fuel, path⟩
    obtain ⟨remaining, tail⟩ := reached
    by_cases length : prior.1.trace.length ≤ ending.trace.length
    · exact ⟨fuel, path.ancestor_comparable tail length⟩
    · have after := tail.ancestor_comparable path (by omega)
      rw [noLater prior ⟨remaining, after⟩]
      exact HistoryReaches.refl E ending
  · intro before
    obtain ⟨firstFuel, before⟩ := before
    obtain ⟨lastFuel, reached⟩ := reached
    exact ⟨firstFuel + lastFuel, before.trans reached⟩

variable (menu : (phaseApplication runtime leaks).ResponseMenu)
  (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "E" => menu.protocol initial horizon scheduler
local notation "N" => menu.information initial horizon scheduler

/-- A full actual information view identifies its genuine physical control's
public exclusion set and complete attempt namespace. -/
theorem phase_information_control_of_view {who : Player} (site : (N).InformationSite who)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (prior : (N).InformationHistory who site.1) :
    ∃ control : (app).Control, prior.1.state = some control ∧
      control.execution.application.current.excluded = view.application.2.excluded ∧
      control.execution.application.attempt = view.application.2.attempt := by
  have info := prior.2
  change (menu.signals initial horizon scheduler).infoOf who prior.1.trace = site.1 at info
  rw [menu.info] at info
  have info := info.trans observed
  cases state : prior.1.state with
  | none => simp [state, ReactiveApplication.observe] at info
  | some control =>
      rw [state] at info
      change (if control.actor = some who then
        some (control.execution.recall who, control.execution.observe (app) who) else none) =
          some (past, view) at info
      by_cases acting : control.actor = some who
      · rw [ite_eq_left acting] at info
        have current := congrArg (fun input : List (app).PlayerEntry × (app).PlayerView =>
          input.2.application.2) (Option.some.inj info)
        exact ⟨control, rfl, congrArg (fun state => state.excluded) current,
          congrArg (fun state => state.attempt) current⟩
      · rw [ite_eq_right acting] at info
        cases info

/-- Once a clear information site's attempt has been left, every later terminal
continuation has exactly the same encountered ancestor as the stopped history.
Exclusion and attempt exit are established from the actual full history. -/
theorem phase_attempt_ancestor_of_exit
    (initialized : ∀ state ∈ initial.support, state.Ordered)
    {who : Player} (site : (N).InformationSite who) (antichain : site.IsHistoryAntichain)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (before ending : (app).Control) (prior : (E).Trace (some before))
    (trace : (E).Trace (some ending)) (retained : TracePrefix prior trace)
    (ordered : before.execution.application.Ordered)
    (entered : before.execution.application.current.excluded ≠ ∅ ∨
      before.execution.application.attempt = view.application.2.attempt)
    (stopped : ending.execution.application.current.excluded ≠ ∅ ∨
      ending.execution.application.attempt ≠ view.application.2.attempt ∨
      (N).infoOf who trace = site.1)
    (final : (E).History) (reached : (E).HistoryReaches ⟨some ending, trace⟩ final) :
    site.ancestor? (N) final = site.ancestor? (N) ⟨some ending, trace⟩ := by
  apply ancestor_stable (N) site antichain _ final reached
  intro atSite later
  obtain ⟨current, currentState, currentClear, currentAttempt⟩ :=
    phase_information_control_of_view runtime leaks menu initial horizon scheduler site past view
      observed atSite
  cases atSite with
  | mk history info =>
    cases history with
    | mk state historyTrace =>
      dsimp at currentState
      subst state
      obtain ⟨fuel, later⟩ := later
      have lastPrefix := reached_prefix later
      have endingClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial horizon
        scheduler ending current trace historyTrace lastPrefix (currentClear.trans clear)).1
      have progress := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon scheduler before ending prior trace retained ordered
      have endingOrdered := (phaseApplication_seedOrder runtime leaks).history initial horizon
        scheduler initialized (menu.toRawTrace initial horizon scheduler trace)
      have next := phase_attempt_progress_of_prefix runtime leaks menu initial initialized
        horizon scheduler ending current trace historyTrace lastPrefix endingOrdered
      rcases stopped with excluded | exited | hit
      · exact False.elim (excluded endingClear)
      · rcases entered with excluded | same
        · have firstClear := (phase_clear_nativeProgress_of_prefix runtime leaks menu initial
            horizon scheduler before ending prior trace retained endingClear).1
          exact False.elim (excluded firstClear)
        · exfalso
          apply exited
          have gen := congrArg CommitAttemptId.generation same
          have phase := congrArg CommitAttemptId.phase same
          have finalGen := congrArg CommitAttemptId.generation currentAttempt
          have finalPhase := congrArg CommitAttemptId.phase currentAttempt
          cases first : before.execution.application.attempt with
          | mk firstPhase firstGeneration =>
            cases middle : ending.execution.application.attempt with
            | mk middlePhase middleGeneration =>
              cases last : current.execution.application.attempt with
              | mk lastPhase lastGeneration =>
                simp only [first, middle, last] at progress next gen phase finalGen finalPhase
                cases targetId : view.application.2.attempt with
                | mk targetPhase targetGeneration =>
                  simp only [targetId] at gen phase finalGen finalPhase ⊢
                  congr 1 <;> omega
      · exact congrArg Subtype.val (site.eq_of_common_descendant (N) antichain
          ⟨⟨some ending, trace⟩, hit⟩ ⟨⟨some current, historyTrace⟩, info⟩
            ⟨some current, historyTrace⟩ later (.refl 0 _)) |>.symm


variable [Fintype Player]

/-- Stopping at the first exclusion, attempt exit, or visit to the specified
clear information site already determines its complete passage readout.
Terminal and excluded entry branches remain in the actual stopped law. -/
theorem phase_attempt_stopped_ancestor
    (initialized : ∀ state ∈ initial.support, state.Ordered)
    (certificate : (E).WellFoundedHistories)
    (profile continuation : ∀ owner, (N).BehavioralPolicy owner)
    {who : Player} (site : (N).InformationSite who) (antichain : site.IsHistoryAntichain)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (before : (app).Control) (prior : (E).Trace (some before))
    (ordered : before.execution.application.Ordered)
    (entered : before.execution.application.current.excluded ≠ ∅ ∨
      before.execution.application.attempt = view.application.2.attempt) :
    let stopped := fun history : (E).History => match history.state with
      | none => False
      | some current => current.execution.application.current.excluded ≠ ∅ ∨
          current.execution.application.attempt ≠ view.application.2.attempt ∨
          (N).infoOf who history.trace = site.1
    ((N).runBehavioralUntil certificate profile stopped ⟨some before, prior⟩).bind
      (fun ending => ((N).runBehavioralTerminalFrom certificate continuation ending).map
        (site.ancestor? (N))) =
      ((N).runBehavioralUntil certificate profile stopped ⟨some before, prior⟩).map
        (site.ancestor? (N)) := by
  classical
  intro stopped
  let start : (E).History := ⟨some before, prior⟩
  let law := (N).runBehavioralUntil certificate profile stopped start
  have reaches : ∀ ending ∈ law.support, (E).HistoryReaches start ending := by
    apply (N).runBehavioralUntil_support_history_closed certificate profile stopped
      (fun ending => (E).HistoryReaches start ending) _ start (HistoryReaches.refl (E) start)
    intro history _going running earlier next supported
    have step := ((N).mem_support_runBehavioralFrom_one profile running supported).2 next
      (HistoryReaches.refl (E) next)
    obtain ⟨firstFuel, first⟩ := earlier
    obtain ⟨lastFuel, last⟩ := step
    exact ⟨firstFuel + lastFuel, first.trans last⟩
  have live : ∀ ending ∈ law.support, ∃ current : (app).Control,
      ending.state = some current := by
    apply (N).runBehavioralUntil_support_closed certificate profile stopped
      (fun state => ∃ current : (app).Control, state = some current) _ start ⟨before, rfl⟩
    rintro state joint _legal target ⟨current, rfl⟩ supported
    exact ⟨_, ((app).transition_recall_prefix initial horizon scheduler current target joint
      supported).choose_spec.1⟩
  conv_rhs => rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support law
  intro ending supported
  have status := (N).mem_support_runBehavioralUntil certificate profile stopped start
    ending supported
  by_cases terminal : (E).terminal ending.state
  · change (((E).randomizedBackwardLaw certificate ((N).randomizedChooser continuation)
      ending).map _) = _
    rw [(E).randomizedBackwardLaw_of_terminal terminal, PMF.pure_map]
    rfl
  obtain ⟨current, currentState⟩ := live ending supported
  obtain ⟨fuel, path⟩ := reaches ending supported
  cases ending with
  | mk state historyTrace =>
    dsimp at currentState
    subst state
    have exit := status.resolve_right terminal
    have retained : TracePrefix prior historyTrace := reached_prefix path
    apply pmf_eq_pure_of_support_subset_singleton
    intro selected selectedSupport
    obtain ⟨final, finalSupport, rfl⟩ := PMF.support_map .. ▸ selectedSupport
    have reached := (E).randomizedBackwardLaw_support_reaches
      ⟨some current, historyTrace⟩ final finalSupport
    exact phase_attempt_ancestor_of_exit runtime leaks menu initial horizon scheduler initialized
      site antichain past view observed clear before current prior historyTrace retained ordered
        entered exit final reached

end Vegas.EventGraphRuntime
