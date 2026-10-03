/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceImmediateRecall
import Vegas.Game.SourceServiceFirstTurnSafe
import Vegas.Pending.ReactiveBindingLikelihood
import Interaction.ReactiveOwnPlay
import Interaction.ReactiveObservation

/-! # The actual input at the first ready owner activation

Stopping after the first ready owner response retains its before-response input
in actual own recall. The asynchronous contract and exact first-turn policy
ensure this stop is reached within the horizon. No response lottery, source
prefix probability, or information posterior is assumed.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Recover the most recent actual input at an own turn for this event.
At the first-ready-turn stop there is exactly one such recalled input. -/
def sourceServiceTurnInput? (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry) : (application setup leaks).Info :=
  ((application setup leaks).recallOwnPlay past).find? (fun played =>
    match played.1 with
    | none => false
    | some (_, view) => decide (view.application.publicView.ownTurn? who = some event)) |>.bind
      Prod.fst

variable {setup leaks}

theorem sourceServiceTurnInput?_append (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) :
    sourceServiceTurnInput? setup leaks who event (past ++ [entry]) =
      if entry.beforeView.application.publicView.ownTurn? who = some event then
        some (past, entry.beforeView) else sourceServiceTurnInput? setup leaks who event past := by
  unfold sourceServiceTurnInput?
  rw [ReactiveApplication.recallOwnPlay_append]
  split
  · rename_i turn
    rw [List.find?_cons_of_pos (by simpa only [decide_eq_true_eq] using turn)]
    rfl
  · rename_i turn
    rw [List.find?_cons_of_neg (by simpa only [decide_eq_true_eq] using turn)]

theorem sourceServiceTurnInput?_eq_none_iff (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry) :
    sourceServiceTurnInput? setup leaks who event past = none ↔
      ∀ entry ∈ past, entry.beforeView.application.publicView.ownTurn? who ≠ some event := by
  induction past using List.reverseRecOn with
  | nil => simp [sourceServiceTurnInput?, ReactiveApplication.recallOwnPlay,
      ReactiveApplication.ownPlayFrom]
  | append_singleton past entry ih =>
      rw [sourceServiceTurnInput?_append]
      by_cases turn : entry.beforeView.application.publicView.ownTurn? who = some event
      · simp only [turn, ↓reduceIte, Option.some_ne_none, false_iff]
        intro all
        exact all entry (List.mem_append_right _ (List.mem_singleton_self _)) turn
      · simp only [turn, ↓reduceIte, ih, List.mem_append, List.mem_singleton]
        constructor
        · intro all other member
          rcases member with member | rfl
          · exact all other member
          · exact turn
        · intro all other member
          exact all other (Or.inl member)

/-- The recalled input does not depend on the response sampled after it. -/
theorem sourceServiceTurnInput?_respond_eq (who : Player) (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (response : (application setup leaks).Action) :
    sourceServiceTurnInput? setup leaks who event
      ((execution.respond (application setup leaks) who response).recall who) =
      if execution.application.publicView.ownTurn? who = some event then
        some (execution.recall who, execution.observe (application setup leaks) who)
      else sourceServiceTurnInput? setup leaks who event (execution.recall who) := by
  have own := (application setup leaks).respond_ownPlay execution who response
  unfold sourceServiceTurnInput?
  rw [own]
  split
  · rename_i turn
    have observed :
        (execution.observe (application setup leaks) who).application.publicView.ownTurn? who =
          some event := turn
    rw [List.find?_cons_of_pos (by simpa only [decide_eq_true_eq] using observed)]
    rfl
  · rename_i turn
    have observed :
        (execution.observe (application setup leaks) who).application.publicView.ownTurn? who ≠
          some event := turn
    rw [List.find?_cons_of_neg (by simpa only [decide_eq_true_eq] using observed)]

/-- The recalled input does not depend on the response sampled after it. -/
theorem sourceServiceTurnInput?_respond (who : Player) (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (response : (application setup leaks).Action) :
    sourceServiceTurnInput? setup leaks who event
      ((execution.respond (application setup leaks) who response).recall who) =
        some (execution.recall who, execution.observe (application setup leaks) who) := by
  rw [sourceServiceTurnInput?_respond_eq, ite_eq_left turn]

/-- Integrating the actual response lottery recovers the same pre-response
input, including its actual partial network sample. -/
theorem sourceServiceTurnInput?_invoke (players : Player → (application setup leaks).Policy)
    (who : Player) (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (turn : execution.application.publicView.ownTurn? who = some event) :
    ((application setup leaks).invoke players who execution).map
      (fun next => sourceServiceTurnInput? setup leaks who event (next.recall who)) =
        PMF.pure (some (execution.recall who,
          execution.observe (application setup leaks) who)) := by
  simp only [ReactiveApplication.invoke, PMF.map_comp, Function.comp_def]
  rw [map_congr_on_support _ (g := fun _ =>
    some (execution.recall who, execution.observe (application setup leaks) who))
      (fun response _ => sourceServiceTurnInput?_respond who event execution turn response)]
  exact PMF.map_const _ _

/-- The actual activation-and-response round has the same recovered input law
as its passive activation. Both sides use the same actual network sample. -/
theorem sourceServiceTurnInput?_dispatch_activation
    (players : Player → (application setup leaks).Policy)
    (who : Player) (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (turn : execution.application.publicView.ownTurn? who = some event) :
    ((application setup leaks).dispatch players (.activate who) execution).map
      (fun next => sourceServiceTurnInput? setup leaks who event (next.recall who)) =
        (execution.environmentStep (application setup leaks) (.activate who)).map
          (fun middle => some (middle.recall who,
            middle.observe (application setup leaks) who)) := by
  let app := application setup leaks
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, PMF.map_bind]
  rw [← PMF.bind_pure_comp]
  apply bind_congr_on_support _
  intro middle observed
  apply sourceServiceTurnInput?_invoke players who event middle
  rw [activation_application setup leaks execution middle who observed]
  exact turn

/-- Equal complete owner traffic gives the same recovered actual input after
passive activation and any subsequent response lottery. -/
theorem sourceServiceTurnInput?_dispatch_activation_congr
    (players : Player → (application setup leaks).Policy)
    (who : Player) (event : (graph setup).EventId)
    (left right : (application setup leaks).Execution)
    (same : (runtime setup).bindingTraffic leaks who left =
      (runtime setup).bindingTraffic leaks who right)
    (turn : left.application.publicView.ownTurn? who = some event) :
    ((application setup leaks).dispatch players (.activate who) left).map
        (fun next => sourceServiceTurnInput? setup leaks who event (next.recall who)) =
      ((application setup leaks).dispatch players (.activate who) right).map
        (fun next => sourceServiceTurnInput? setup leaks who event (next.recall who)) := by
  let app := application setup leaks
  have networks := congrArg Prod.fst same
  have receipts := congrArg (fun traffic => traffic.2.1) same
  have recalls := congrArg (fun traffic => traffic.2.2.2.1) same
  have views := congrArg (fun traffic => traffic.2.2.2.2.1) same
  have publics := congrArg (fun traffic => traffic.2.2.2.2.2) same
  dsimp only [bindingTraffic] at networks receipts recalls views publics
  have rightTurn : right.application.publicView.ownTurn? who = some event := by
    rw [← publics]
    exact turn
  rw [sourceServiceTurnInput?_dispatch_activation players who event left turn,
    sourceServiceTurnInput?_dispatch_activation players who event right rightTurn]
  have localView : app.observePlayer left.application who =
      app.observePlayer right.application who := by
    exact congrArg (fun view : EventGraphRuntime.PlayerView (graph setup) =>
      (⟨view.who, view.publicView, view.observation, view.candidates⟩ :
        ReactivePlayerView (graph setup))) views
  have law := app.activation_info_congr left right who networks receipts localView recalls
  have tagged := congrArg (PMF.map some) law
  simpa only [PMF.map_comp, Function.comp_def] using tagged

private theorem completed_turn_input {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (count : Nat) (within : count ≤ horizon)
    (execution : (application setup leaks).Execution)
    (reached : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players count).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (completed : event ∈ execution.application.config.cut.completed) :
    sourceServiceTurnInput? setup leaks who event (execution.recall who) ≠ none := by
  obtain ⟨trace⟩ := (application setup leaks).raw_trace_roundsFrom (initialLaw setup) horizon
    scheduler players count within execution reached
  have clear := sourceServiceFirstTurn_no_public_miss contract timely players who turns profile
    follows count within execution reached
  have recorded := completed_owned_decision_recorded trace who event completed clear owned
  obtain ⟨entry, member, named⟩ := List.any_eq_true.mp recorded
  have atTurn := (canonicalSlots_roundsFrom scheduler players who (firstTurnTiming setup turns)
    profile follows count execution reached).1
  have turn := atTurn entry member event (of_decide_eq_true named)
  intro absent
  exact (sourceServiceTurnInput?_eq_none_iff who event _).mp absent entry member turn

/-- The actual first-ready-turn stop is reached before the contract's horizon.
Only the focal owner's first-turn policy is fixed; foreign policies are raw. -/
theorem sourceServiceFirstActivation_stopped {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (execution : (application setup leaks).Execution)
    (within : execution.environmentRecall.length ≤ horizon)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players execution.environmentRecall.length).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution).support) :
    stopped.environmentRecall.length ≤ horizon ∧
      sourceServiceTurnInput? setup leaks who event (stopped.recall who) ≠ none := by
  classical
  let app := application setup leaks
  let stop := fun final : app.Execution =>
    sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none
  obtain ⟨used, budget, _rounds, length⟩ := app.runUntil_runRounds scheduler players stop
    (horizon - execution.environmentRecall.length) execution stopped reached
  have bounded : stopped.environmentRecall.length ≤ horizon := by omega
  have actual := app.roundsFrom_runUntil scheduler players (initialLaw setup) stop
    (horizon - execution.environmentRecall.length) execution stopped initialized reached
  refine ⟨bounded, ?_⟩
  rcases app.runUntilHorizon_stopped scheduler players stop horizon
      (horizon - execution.environmentRecall.length) execution stopped (by omega) reached with
    hit | spent
  · exact hit
  · obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
      stopped.environmentRecall.length bounded stopped actual
    rw [spent, Nat.sub_self] at trace
    have terminal : (app.protocol (initialLaw setup) horizon scheduler).terminal
        (some ⟨0, none, stopped⟩) := by trivial
    have completed := contract.completes ⟨0, none, stopped⟩ trace terminal
    exact completed_turn_input contract timely players who turns profile follows _ bounded
      stopped actual event owned (by rw [completed]; exact Finset.mem_univ _)

/-- The actual stopped input has total mass on genuine owner inputs. -/
theorem sourceServiceFirstActivation_input_isSome_law {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (execution : (application setup leaks).Execution)
    (within : execution.environmentRecall.length ≤ horizon)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players execution.environmentRecall.length).support)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who) :
    (((application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution).map fun stopped =>
        (sourceServiceTurnInput? setup leaks who event (stopped.recall who)).isSome) =
      PMF.pure true := by
  classical
  rw [map_congr_on_support _ (g := fun _ => true) ?_]
  · exact PMF.map_const _ _
  · intro stopped reached
    have hit := (sourceServiceFirstActivation_stopped contract timely players who turns profile
      follows execution within initialized event owned stopped reached).2
    cases input : sourceServiceTurnInput? setup leaks who event (stopped.recall who) with
    | none => exact (hit input).elim
    | some pair => rfl

private theorem firstActivation_origin {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (count : Nat) (execution : (application setup leaks).Execution)
    (budget : execution.environmentRecall.length + count ≤ horizon)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      players execution.environmentRecall.length).support)
    (ready : execution.application.config.cut.Ready event)
    (absent : sourceServiceTurnInput? setup leaks who event (execution.recall who) = none)
    (stopped : (application setup leaks).Execution)
    (hit : sourceServiceTurnInput? setup leaks who event (stopped.recall who) ≠ none)
    (reached : stopped ∈ ((application setup leaks).runUntil scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      count execution).support) :
    ∃ (before middle : (application setup leaks).Execution)
      (response : (application setup leaks).Action),
      before ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler players
        before.environmentRecall.length).support ∧
      before.environmentRecall.length < horizon ∧
      before.application.config = execution.application.config ∧
      sourceServiceTurnInput? setup leaks who event (before.recall who) = none ∧
      .activate who ∈ (scheduler before.environmentRecall
        (before.observeEnvironment (application setup leaks))).support ∧
      middle ∈ (before.environmentStep (application setup leaks) (.activate who)).support ∧
      middle.application.publicView.ownTurn? who = some event ∧
      response ∈ (players who (middle.recall who)
        (middle.observe (application setup leaks) who)).support ∧
      stopped = middle.respond (application setup leaks) who response := by
  classical
  let app := application setup leaks
  let stop := fun final : app.Execution =>
    sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (hit absent).elim
  | succ count ih =>
      change stopped ∈ (app.runUntil scheduler players stop (count + 1) execution).support
        at reached
      have running : ¬ stop execution := by simp only [stop, absent, ne_eq, not_true_eq_false,
        not_false_eq_true]
      simp only [ReactiveApplication.runUntil, running, ↓reduceIte] at reached
      obtain ⟨next, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have length := app.round_environmentRecall_length scheduler players execution next moved
      have nextActual : next ∈ (app.roundsFrom (initialLaw setup) scheduler players
          next.environmentRecall.length).support := by
        rw [length, app.roundsFrom_succ, PMF.support_bind]
        exact Set.mem_iUnion₂.mpr ⟨execution, initialized, moved⟩
      by_cases seen : stop next
      · rw [app.runUntil_of_stop scheduler players stop count next seen,
          PMF.mem_support_pure_iff] at rest
        subst stopped
        obtain ⟨command, selected, middle, observed, cases⟩ := round_cases setup leaks moved
        have recalls := app.environmentStep_recall execution middle command observed
        have notYet : sourceServiceTurnInput? setup leaks who event (middle.recall who) = none :=
          by rw [recalls]; exact absent
        rcases cases with ⟨_inactive, rfl⟩ | ⟨actor, active, response, chosen, rfl⟩
        · exact (seen notYet).elim
        · by_cases same : actor = who
          · subst actor
            have turn : middle.application.publicView.ownTurn? who = some event := by
              by_contra different
              apply seen
              rw [sourceServiceTurnInput?_respond_eq, ite_eq_right different]
              exact notYet
            have commandEq : command = .activate who := by
              cases command with
              | activate actor =>
                  exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
              | wait | «include» _ | application _ => cases active
            subst commandEq
            exact ⟨execution, middle, response, initialized, by omega, rfl, absent,
              selected, observed, turn, chosen, rfl⟩
          · apply (seen ?_).elim
            rw [app.respond_recall_other middle actor who (Ne.symm same) response]
            exact notYet
      · have nextAbsent : sourceServiceTurnInput? setup leaks who event (next.recall who) = none :=
          by simpa only [stop, ne_eq, not_not] using seen
        have same : next.application.config = execution.application.config := by
          rcases round_configStep setup leaks scheduler players execution next moved with same |
              ⟨target, targetReady, action, stepped⟩
          · exact same
          · have targetEq := setup.eventGraph.sequentialize_ready_unique
              execution.application.config.cut targetReady ready
            subst target
            have completed : event ∈ next.application.config.cut.completed := by
              rw [execution.application.config.step_cut event ready action next.application.config
                stepped, EventOrder.Cut.mem_complete]
              exact Or.inl rfl
            exact (completed_turn_input contract timely players who turns profile follows
              next.environmentRecall.length (by omega) next nextActual event owned completed
                nextAbsent).elim
        obtain ⟨before, middle, response, actual, bounded, configEq, noInput, selected,
          observed, turn, chosen, result⟩ := ih next (by omega) nextActual (same ▸ ready)
            nextAbsent rest
        exact ⟨before, middle, response, actual, bounded, configEq.trans same, noInput, selected,
          observed, turn, chosen, result⟩

/-- From an untouched actual completion boundary, the first ready owner
activation has the unchanged typed configuration and a protected inclusion
window. Its exact passive before-response input is recovered from actual
recall; the current response is supported by the initialized physical policy. -/
theorem sourceServiceFirstActivation_input {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (within : execution.environmentRecall.length ≤ horizon)
    (stopped : (application setup leaks).Execution)
    (reached : stopped ∈ ((application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution).support) :
    ∃ (middle : (application setup leaks).Execution)
      (response : (application setup leaks).Action),
      (application setup leaks).RoundSupported (initialLaw setup) horizon scheduler players
        (some ⟨horizon - middle.environmentRecall.length, some who, middle⟩) ∧
      middle.application.config = execution.application.config ∧
      sourceServiceTurn setup leaks who event (middle.recall who)
        (middle.observe (application setup leaks) who) = some 0 ∧
      middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event ∧
      response ∈ (players who (middle.recall who)
        (middle.observe (application setup leaks) who)).support ∧
      stopped = middle.respond (application setup leaks) who response ∧
      sourceServiceTurnInput? setup leaks who event (stopped.recall who) =
        some (middle.recall who, middle.observe (application setup leaks) who) := by
  classical
  let app := application setup leaks
  have ready : execution.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
  have absent : sourceServiceTurnInput? setup leaks who event (execution.recall who) = none := by
    apply (sourceServiceTurnInput?_eq_none_iff who event _).mpr
    intro entry member turn
    exact boundary.untouched event rfl who entry member (PublicView.ownTurn?_spec _ who event
      turn).1
  have hit := (sourceServiceFirstActivation_stopped contract timely players who turns profile
    follows execution within boundary.supported event owned stopped reached).2
  obtain ⟨before, middle, response, actual, bounded, configEq, noInput, selected, observed,
    turn, chosen, result⟩ := firstActivation_origin contract timely players who turns profile
      follows event owned (horizon - execution.environmentRecall.length) execution (by omega)
        boundary.supported ready absent stopped hit reached
  have appEq := activation_application setup leaks before middle who observed
  have recalls := app.environmentStep_recall before middle (.activate who) observed
  have length : middle.environmentRecall.length = before.environmentRecall.length + 1 := by
    rw [(app.activation_visible before middle who observed).2, List.length_append,
      List.length_singleton]
  have supported : app.RoundSupported (initialLaw setup) horizon scheduler players
      (some ⟨horizon - middle.environmentRecall.length, some who, middle⟩) :=
    ⟨by dsimp only; omega, before.environmentRecall.length, before, .activate who, length,
      actual, selected, rfl, observed⟩
  have first : sourceServiceTurn setup leaks who event (middle.recall who)
      (middle.observe app who) = some 0 := by
    have viewTurn : (middle.observe app who).application.publicView.ownTurn? who = some event :=
      turn
    unfold sourceServiceTurn
    simp only [viewTurn, ↓reduceIte]
    apply congrArg some
    apply List.countP_eq_zero.mpr
    intro entry member seen
    have noInputMiddle : sourceServiceTurnInput? setup leaks who event (middle.recall who) =
        none := by rw [recalls]; exact noInput
    exact (sourceServiceTurnInput?_eq_none_iff who event _).mp noInputMiddle entry member
      (of_decide_eq_true seen)
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    before.environmentRecall.length bounded.le before actual
  have firstBefore : sourceServiceTurn setup leaks who event (before.recall who)
      (middle.observe app who) = some 0 := by rw [← recalls]; exact first
  have fits := firstTurn_inclusionFits contract timely trace
    (roundsFrom_activationsAnswered before.environmentRecall.length before actual) owned
    (configEq.symm ▸ ready) firstBefore
  have middleFits : middle.application.publicView.InclusionFitsDeadline (runtime setup) bound
      event := by rw [appEq]; exact fits
  refine ⟨middle, response, supported, ?_, first, middleFits, chosen, result, ?_⟩
  · exact (congrArg State.config appEq).trans configEq
  · rw [result]
    exact sourceServiceTurnInput?_respond who event middle turn response

end Vegas
