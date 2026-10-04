/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceOriginalFirstInput
import Interaction.ReactiveHistory
import Interaction.ReactivePassageBayes
import GameTheory.Analysis.Protocol.InformationLocalization

/-! # First event inputs retained by actual native passage

The chronological first event input remains in actual own recall after later
activations. At a first event information site, this terminal readout records
exactly passage through that site. Stopping and continuing therefore preserve
the input law, including arbitrary scheduler depths and later silent responses.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private def namesTurn (who : Player) (event : (graph setup).EventId)
    (played : (application setup leaks).Info × (application setup leaks).Action) : Bool :=
  match played.1 with
  | none => false
  | some (_, view) => decide (view.application.publicView.ownTurn? who = some event)

/-- The earliest actual before-response input at an own turn for the event.
Later turns preserve it, because it is read chronologically from own recall. -/
def sourceServiceFirstInput? (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry) : (application setup leaks).Info :=
  (((application setup leaks).recallOwnPlay past).reverse.find?
    (namesTurn setup leaks who event)).bind Prod.fst

variable {setup leaks}

private theorem namedFind_none (who : Player) (event : (graph setup).EventId)
    (played : List ((application setup leaks).Info × (application setup leaks).Action)) :
    ((played.find? (namesTurn setup leaks who event)).bind Prod.fst = none) ↔
      played.find? (namesTurn setup leaks who event) = none := by
  cases found : played.find? (namesTurn setup leaks who event) with
  | none => simp only [Option.bind_none]
  | some selected =>
      have named := List.find?_some found
      cases info : selected.1 with
      | none => simp only [namesTurn, info, Bool.false_eq_true] at named
      | some input => simp only [Option.bind_some, info, Option.some_ne_none]

private theorem firstFind_none (who : Player) (event : (graph setup).EventId)
    (past : List (application setup leaks).PlayerEntry)
    (absent : sourceServiceTurnInput? setup leaks who event past = none) :
    ((application setup leaks).recallOwnPlay past).reverse.find?
      (namesTurn setup leaks who event) = none := by
  change (((application setup leaks).recallOwnPlay past).find?
    (namesTurn setup leaks who event)).bind Prod.fst = none at absent
  have original := (namedFind_none who event _).mp absent
  apply List.find?_eq_none.mpr
  intro played member
  exact List.find?_eq_none.mp original played (List.mem_reverse.mp member)

/-- Appending further actual entries cannot overwrite an existing first input. -/
theorem sourceServiceFirstInput?_append_present (who : Player)
    (event : (graph setup).EventId) (past : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry) (input : (application setup leaks).Info)
    (present : sourceServiceFirstInput? setup leaks who event past = input)
    (nonempty : input ≠ none) :
    sourceServiceFirstInput? setup leaks who event (past ++ [entry]) = input := by
  cases input with
  | none => exact (nonempty rfl).elim
  | some input =>
      obtain ⟨played, found, selected⟩ := Option.bind_eq_some_iff.mp present
      unfold sourceServiceFirstInput?
      rw [ReactiveApplication.recallOwnPlay_append, List.reverse_cons, List.find?_append, found]
      simpa only [Option.some_or, Option.bind_some] using selected

/-- The first actual input is stable along any extension of own recall. -/
theorem sourceServiceFirstInput?_prefix (who : Player) (event : (graph setup).EventId)
    (before after : List (application setup leaks).PlayerEntry)
    (retained : before <+: after) (input : (application setup leaks).Info)
    (present : sourceServiceFirstInput? setup leaks who event before = input)
    (nonempty : input ≠ none) :
    sourceServiceFirstInput? setup leaks who event after = input := by
  obtain ⟨suffix, rfl⟩ := retained
  induction suffix using List.reverseRecOn with
  | nil => simpa only [List.append_nil] using present
  | append_singleton suffix entry ih =>
      rw [← List.append_assoc]
      exact sourceServiceFirstInput?_append_present who event _ entry input ih nonempty

/-- A real first named response records exactly its actual before-response
input, independent of the response lottery. -/
theorem sourceServiceFirstInput?_first_response (who : Player) (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution)
    (absent : sourceServiceTurnInput? setup leaks who event (execution.recall who) = none)
    (turn : execution.application.publicView.ownTurn? who = some event)
    (response : (application setup leaks).Action) :
    sourceServiceFirstInput? setup leaks who event
        ((execution.respond (application setup leaks) who response).recall who) =
      some (execution.recall who, execution.observe (application setup leaks) who) := by
  unfold sourceServiceFirstInput?
  rw [ReactiveApplication.respond_ownPlay, List.reverse_cons, List.find?_append,
    firstFind_none who event _ absent]
  have named : namesTurn setup leaks who event
      (some (execution.recall who, execution.observe (application setup leaks) who), response) =
        true := by
    change decide (execution.application.publicView.ownTurn? who = some event) = true
    exact decide_eq_true turn
  simp only [Option.none_or, List.find?_cons_of_pos named, Option.bind_some]

/-- A complete native history passed a first-event information site exactly
when its genuine chronological input readout records that site's input. -/
theorem sourceServiceFirstInput?_eq_iff_passage
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) (who : Player)
    (event : (graph setup).EventId)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (turn : view.application.publicView.ownTurn? who = some event)
    (absent : sourceServiceTurnInput? setup leaks who event past = none)
    (final : (menu.protocol initial horizon scheduler).History)
    (terminal : (menu.protocol initial horizon scheduler).terminal final.state) :
    sourceServiceFirstInput? setup leaks who event
        ((application setup leaks).recallAt who final.state) = site.1 ↔
      ∃ before : (menu.information initial horizon scheduler).InformationHistory who site.1,
        (menu.protocol initial horizon scheduler).HistoryReaches before.1 final := by
  classical
  let app := application setup leaks
  let model := menu.information initial horizon scheduler
  let protocol := menu.protocol initial horizon scheduler
  constructor
  · intro equal
    rw [observed] at equal
    obtain ⟨played, found, inputEq⟩ := Option.bind_eq_some_iff.mp equal
    have member := List.mem_reverse.mp (List.mem_of_find?_eq_some found)
    have own : played ∈ model.ownPlay who final.trace := by
      change played ∈ (menu.signals initial horizon scheduler).ownPlay who final.trace
      rw [← menu.ownPlay_toRawTrace initial horizon scheduler who final.trace,
        app.trace_ownPlay]
      exact member
    obtain ⟨before, infoEq, _active, _running, reached⟩ :=
      model.exists_decision_ancestor_of_mem_ownPlay who final.trace own
    exact ⟨⟨before, infoEq.trans (inputEq.trans observed.symm)⟩, reached⟩
  · rintro ⟨before, fuel, path⟩
    have infoEq : app.observe who before.1.state = some (past, view) := by
      rw [← menu.info initial horizon scheduler who before.1.trace]
      exact before.2.trans observed
    obtain ⟨remaining, execution, current, recallEq, viewEq⟩ :
        ∃ remaining execution,
          before.1.state = some ⟨remaining, some who, execution⟩ ∧
          execution.recall who = past ∧ execution.observe app who = view := by
      cases stateEq : before.1.state with
      | none => simp only [stateEq, ReactiveApplication.observe] at infoEq; contradiction
      | some control =>
          by_cases actor : control.actor = some who
          · simp only [stateEq, ReactiveApplication.observe, actor, ↓reduceIte] at infoEq
            obtain ⟨recallEq, viewEq⟩ := Prod.mk.inj (Option.some.inj infoEq)
            exact ⟨control.remaining, control.execution, by cases control; cases actor; rfl,
              recallEq, viewEq⟩
          · simp only [stateEq, ReactiveApplication.observe, actor, ↓reduceIte] at infoEq
            contradiction
    cases path with
    | refl =>
        exact ((menu.informationSite_allNonterminal initial horizon scheduler who site before)
          terminal).elim
    | @step steps history target joint legal reached realized rest =>
        have acting : protocol.active before.1.state who := by
          change app.actor before.1.state = some who
          rw [current]
          rfl
        obtain ⟨response, selected⟩ :=
          (protocol.legalOption_of_legal legal who).exists_eq_some_of_active (joint who) acting
        have stateEq : reached = some ⟨remaining, none, execution.respond app who response⟩ := by
          change reached ∈ (app.transition initial horizon scheduler before.1.state joint).support
            at realized
          rw [current] at realized
          change reached ∈ (PMF.pure (some
            ⟨remaining, none, execution.respond app who ((joint who).getD ⟨none⟩)⟩)).support
              at realized
          rw [selected, Option.getD_some] at realized
          exact (PMF.mem_support_pure_iff _ _).mp realized
        have post : sourceServiceFirstInput? setup leaks who event
            ((execution.respond app who response).recall who) = some (past, view) := by
          rw [← recallEq, ← viewEq]
          apply sourceServiceFirstInput?_first_response who event execution
          · rwa [recallEq]
          · change (execution.observe app who).application.publicView.ownTurn? who = some event
            rwa [viewEq]
        obtain ⟨last, finalEq⟩ : ∃ last : app.Control, final.state = some last := by
          cases finalState : final.state with
          | none => change app.terminal final.state at terminal
                    rw [finalState] at terminal
                    exact terminal.elim
          | some last => exact ⟨last, rfl⟩
        have retained := app.reaches_recall_prefix initial horizon scheduler
          (menu.reaches_raw initial horizon scheduler rest)
          ⟨remaining, none, execution.respond app who response⟩ last stateEq finalEq who
        rw [finalEq]
        exact (sourceServiceFirstInput?_prefix who event _ _ retained _ post
          (Option.some_ne_none _)).trans observed.symm

open Classical in
/-- The actual terminal first-input passage probability is the native
information mass. Histories at this site need not share a decision depth. -/
theorem sourceServiceFirstInput?_terminal_passage_mass [Fintype Player]
    (menu : (application setup leaks).ResponseMenu)
    (initial : PMF (application setup leaks).State) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (strategy : ∀ who, (menu.information initial horizon scheduler).BehavioralPolicy who)
    (who : Player) (event : (graph setup).EventId)
    (site : (menu.information initial horizon scheduler).InformationSite who)
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (observed : site.1 = some (past, view))
    (turn : view.application.publicView.ownTurn? who = some event)
    (absent : sourceServiceTurnInput? setup leaks who event past = none) :
    let model := menu.information initial horizon scheduler
    let certificate := (menu.bounded initial horizon scheduler).wellFoundedHistories
    (((model.runBehavioralTerminalFrom certificate strategy
      (menu.protocol initial horizon scheduler).initHistory).map fun final =>
        decide (sourceServiceFirstInput? setup leaks who event
          ((application setup leaks).recallAt who final.state) = site.1)) true) =
      model.informationMass strategy who site := by
  classical
  intro model certificate
  let terminal := model.runBehavioralTerminalFrom certificate strategy
    (menu.protocol initial horizon scheduler).initHistory
  have law : (terminal.map fun final => decide (sourceServiceFirstInput? setup leaks who event
        ((application setup leaks).recallAt who final.state) = site.1)) =
      (terminal.map (site.ancestor? model)).map Option.isSome := by
    rw [PMF.map_comp]
    apply map_congr_on_support terminal
    intro final supported
    have complete := model.runBehavioralTerminalFrom_support_terminal certificate strategy
      (menu.protocol initial horizon scheduler).initHistory final supported
    have passage := sourceServiceFirstInput?_eq_iff_passage menu initial horizon scheduler who
      event site past view observed turn absent final complete
    by_cases recorded : sourceServiceFirstInput? setup leaks who event
        ((application setup leaks).recallAt who final.state) = site.1
    · have encountered := passage.mp recorded
      simp only [Function.comp_apply]
      unfold InformationModel.InformationSite.ancestor?
      rw [dite_eq_left encountered]
      simp only [recorded, decide_true, Option.isSome_some]
    · have missing := fun reached => recorded (passage.mpr reached)
      simp only [Function.comp_apply]
      unfold InformationModel.InformationSite.ancestor?
      rw [dite_eq_right missing]
      simp only [recorded, decide_false, Option.isSome_none]
  rw [law]
  exact site.terminal_ancestor_passage model
    (menu.decisionInformationAntichain initial horizon scheduler who site) certificate strategy

private theorem firstInput_round (who : Player) (event : (graph setup).EventId)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (execution next : (application setup leaks).Execution)
    (reached : next ∈ ((application setup leaks).round scheduler players execution).support)
    (input : (application setup leaks).Info)
    (present : sourceServiceFirstInput? setup leaks who event (execution.recall who) = input)
    (nonempty : input ≠ none) :
    sourceServiceFirstInput? setup leaks who event (next.recall who) = input := by
  let app := application setup leaks
  obtain ⟨command, _selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  have recallEq := app.environmentStep_recall execution middle command moved
  cases actor : command.actor? app with
  | none =>
      change next ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      rw [recallEq]
      exact present
  | some owner =>
      change next ∈ (app.resume players (command.actor? app) middle).support at resumed
      rw [actor] at resumed
      obtain ⟨response, _chosen, rfl⟩ := PMF.support_map .. ▸ resumed
      exact sourceServiceFirstInput?_prefix who event _ _
        (app.respond_recall_prefix middle owner who response) input (recallEq ▸ present) nonempty

private theorem firstInput_runRounds (who : Player) (event : (graph setup).EventId)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (count : Nat) (execution : (application setup leaks).Execution)
    (input : (application setup leaks).Info)
    (present : sourceServiceFirstInput? setup leaks who event (execution.recall who) = input)
    (nonempty : input ≠ none) :
    ∀ final ∈ ((application setup leaks).runRounds scheduler players count execution).support,
      sourceServiceFirstInput? setup leaks who event (final.recall who) = input := by
  induction count generalizing execution with
  | zero =>
      intro final reached
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact present
  | succ count ih =>
      intro final reached
      obtain ⟨middle, moved, rest⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      exact ih middle (firstInput_round who event scheduler players execution middle moved input
        present nonempty) final rest

/-- The complete continuation preserves the first input already present in
actual recall, without any scheduler or strategy restriction. -/
theorem sourceServiceFirstInput?_runToHorizon (who : Player) (event : (graph setup).EventId)
    (scheduler : (application setup leaks).Scheduler)
    (players : Player → (application setup leaks).Policy)
    (horizon : Nat) (execution : (application setup leaks).Execution)
    (input : (application setup leaks).Info)
    (present : sourceServiceFirstInput? setup leaks who event (execution.recall who) = input)
    (nonempty : input ≠ none) :
    (((application setup leaks).runToHorizon scheduler players horizon execution).map
      fun final => sourceServiceFirstInput? setup leaks who event (final.recall who)) =
        PMF.pure input := by
  calc
    _ = ((application setup leaks).runToHorizon scheduler players horizon execution).map
        (fun _ => input) := map_congr_on_support _
      (firstInput_runRounds who event scheduler players _ execution input present nonempty)
    _ = _ := PMF.map_const _ _

/-- The real full-horizon input law from an untouched completion boundary is
the actual first-activation stopped input law. The input is taken from actual
recall and retained through every later scheduler command and response. -/
theorem sourceServiceFirstActivation_terminal_input
    {scheduler : (application setup leaks).Scheduler} {horizon turns : Nat}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (players : Player → (application setup leaks).Policy) (who : Player)
    (profile : BehavioralProfile setup.program)
    (follows : players who = sourceServiceTurnPolicy setup leaks bound turns
      (firstTurnTiming setup turns) profile who)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (within : execution.environmentRecall.length ≤ horizon) :
    (((application setup leaks).runToHorizon scheduler players horizon execution).map
      fun final => sourceServiceFirstInput? setup leaks who event (final.recall who)) =
    (((application setup leaks).runUntilHorizon scheduler players
      (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution).map fun stopped =>
        sourceServiceTurnInput? setup leaks who event (stopped.recall who)) := by
  classical
  let app := application setup leaks
  rw [app.runToHorizon_eq_runUntilHorizon_bind scheduler players
    (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none),
    PMF.map_bind]
  change _ = (app.runUntilHorizon scheduler players
    (fun final => sourceServiceTurnInput? setup leaks who event (final.recall who) ≠ none)
      horizon execution).bind (fun stopped => PMF.pure
        (sourceServiceTurnInput? setup leaks who event (stopped.recall who)))
  apply bind_congr_on_support _
  intro stopped reached
  obtain ⟨middle, response, _actual, _configEq, first, _fits, _chosen, after, inputEq⟩ :=
    sourceServiceFirstActivation_input contract timely players who turns profile follows event
      owned execution boundary within stopped reached
  have absent : sourceServiceTurnInput? setup leaks who event (middle.recall who) = none := by
    apply (sourceServiceTurnInput?_eq_none_iff who event _).mpr
    unfold sourceServiceTurn at first
    split at first
    · have zero := Option.some.inj first
      intro entry member named
      have excluded := List.countP_eq_zero.mp zero entry member
      exact excluded (decide_eq_true named)
    · cases first
  have turn : middle.application.publicView.ownTurn? who = some event := by
    unfold sourceServiceTurn at first
    split at first
    · assumption
    · cases first
  have present : sourceServiceFirstInput? setup leaks who event (stopped.recall who) =
      sourceServiceTurnInput? setup leaks who event (stopped.recall who) := by
    rw [inputEq, after]
    exact sourceServiceFirstInput?_first_response who event middle absent turn response
  apply sourceServiceFirstInput?_runToHorizon who event scheduler players horizon stopped _
    present
  rw [inputEq]
  exact Option.some_ne_none _

end Vegas
