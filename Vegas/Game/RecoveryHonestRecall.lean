/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RecoveryHonestContinuation
import Vegas.Game.HonestContinuationIntended
import GameTheory.Analysis.Protocol.RestrictionDomination
import Vegas.Game.OnePacketNextEvent

/-! # Honest ready callbacks are recorded under actual recovery service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {initial : PMF (RecoveryState (graph setup))}
  (initialized : ∀ state ∈ initial.support, ∃ inputs,
    state = (RecoveryState.mk (State.initial inputs) ∅ : RecoveryState (graph setup)))
  (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
  {horizon : Nat}
  {recoveryScheduler : (recoveryApplication (runtime setup) leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : Recovery.Opportunity (runtime setup) leaks initial horizon recoveryScheduler delay)
  (timely : (runtime setup).AsyncTimely delay bound)

local notation "scheduler" => RecoveryProjection.nativeScheduler (runtime setup) leaks
  recoveryScheduler
local notation "menu" => bounds.onePacketMenu (runtime setup) leaks
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler

private def ReadyTurnsRecorded (execution : (application setup leaks).Execution) : Prop :=
  ∀ event : (graph setup).EventId, event ∉ execution.application.config.cut.completed →
    ∀ who entry, entry ∈ execution.recall who → ActivatedAt setup leaks who event entry →
      (runtime setup).eventRecorded leaks (execution.recall who) event = true

include initialized nativeLaw opportunity timely in
private theorem readyTurnsRecorded_transition
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (history : (E).History) (control : (application setup leaks).Control)
    (state : history.state = some control)
    (point : ProtocolState setup.program)
    (decoded : decodedPoint setup control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (recorded : ReadyTurnsRecorded control.execution)
    (choices : ∀ player, (N).Choice player ((N).infoOf player history.trace))
    (chosen : ∀ player, choices player ∈
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source player
        ((N).infoOf player history.trace)).support)
    (final : (E).History) (supported : final ∈ ((N).localStep history choices).support) :
    ∃ next : (application setup leaks).Control, final.state = some next ∧
      ReadyTurnsRecorded next.execution := by
  classical
  by_cases stopped : (E).terminal history.state
  · rw [InformationModel.localStep, dite_eq_left stopped, PMF.mem_support_pure_iff] at supported
    subst final
    exact ⟨control, state, recorded⟩
  rw [InformationModel.localStep, dite_eq_right stopped,
    PMF.mem_support_bindOnSupport_iff] at supported
  obtain ⟨after, realized, finalMem⟩ := supported
  change final ∈ (PMF.pure _).support at finalMem
  cases (PMF.mem_support_pure_iff _ _).mp finalMem
  have moved : after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some control) (fun player => (choices player).1)).support := by
    let joint : Player → Option (application setup leaks).Action := fun player => (choices player).1
    change after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      history.state joint).support at realized
    change after ∈ ((application setup leaks).transition (initialLaw setup) horizon scheduler
      (some control) joint).support
    rw [state] at realized
    exact realized
  obtain ⟨next, afterEq, configStep⟩ := transition_some_configStep (initialLaw setup) horizon
    scheduler control after (fun player => (choices player).1) moved
  refine ⟨next, afterEq, ?_⟩
  have trace : (E).Trace (some control) := state ▸ history.trace
  have raw := (menu).toRawTrace (initialLaw setup) horizon scheduler trace
  have clear := exclusionEvidence_of_decodedIntended raw decoded intended
  have forced : ∀ player, ForcedState setup leaks player (some control) := fun player =>
    (forcedState_iff_decodedPoint control).mpr
      ⟨point, decoded, forcedPoint_of_intended player intended⟩
  have notOwed : ∀ player found, decodedPoint setup control.execution.application.config =
      some found → ¬ ProtocolState.OwesFailure player setup.program found := by
    intro player found foundDecoded
    cases Option.some.inj (decoded.symm.trans foundDecoded)
    exact ProtocolState.Intended.not_owesFailure player setup.program point intended
  rcases control with ⟨remaining, actor, execution⟩
  cases actor with
  | none =>
      cases remaining with
      | zero =>
          cases (PMF.mem_support_pure_iff _ _).mp moved
          cases Option.some.inj afterEq
          exact recorded
      | succ remaining =>
          obtain ⟨command, _, continued⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ moved)
          obtain ⟨ending, step, same⟩ := PMF.support_map .. ▸ continued
          cases Option.some.inj (same.trans afterEq)
          intro event unfinished player entry member activated
          have recallEq := (application setup leaks).environmentStep_recall execution ending
            command step
          rw [recallEq] at member ⊢
          exact recorded event (fun done => unfinished (configStep.completed_mono done))
            player entry member activated
  | some actor =>
      have observed : (N).infoOf actor history.trace = some (execution.recall actor,
          execution.observe (application setup leaks) actor) := by
        have observes := (menu).info (initialLaw setup) horizon scheduler actor history.trace
        change (N).infoOf actor history.trace =
          (application setup leaks).observe actor history.state at observes
        exact observes.trans (by rw [state]; simp [ReactiveApplication.observe])
      have localLegal := ((N).menu_adequate actor history.trace (choices actor).1).mp
        (choices actor).2
      have selected : ∃ response, (choices actor).1 = some response := by
        cases choiceEq : (choices actor).1 with
        | none =>
            rw [choiceEq] at localLegal
            exfalso
            apply localLegal
            change (application setup leaks).actor history.state = some actor
            rw [state]
            rfl
        | some response => exact ⟨response, rfl⟩
      obtain ⟨response, selected⟩ := selected
      change after ∈ (PMF.pure _).support at moved
      have same := (PMF.mem_support_pure_iff _ _).mp moved
      simp only [selected, Option.getD_some] at same
      cases Option.some.inj (same.symm.trans afterEq)
      intro event unfinished player entry member activated
      rw [((runtime setup).reactive_respond_application leaks execution actor response).1]
        at unfinished
      rcases (application setup leaks).respond_entry_origin execution actor player response
          entry member with earlier | ⟨samePlayer, sameView⟩
      · exact (runtime setup).eventRecorded_respond_of_recorded leaks execution actor player
          response event (recorded event unfinished player entry earlier activated)
      · subst player
        have turn : execution.application.publicView.ownTurn? actor = some event := by
          change entry.beforeView.application.publicView.ownTurn? actor = some event at activated
          rw [sameView] at activated
          change execution.application.publicView.ownTurn? actor = some event at activated
          exact activated
        cases old : (runtime setup).eventRecorded leaks (execution.recall actor) event with
        | true =>
            exact (runtime setup).eventRecorded_respond_of_recorded leaks execution actor actor
              response event old
        | false =>
            have pending := pendingEvent_of_spec (setup := setup) (leaks := leaks) (who := actor)
              (past := execution.recall actor)
              (view := execution.observe (application setup leaks) actor) turn old
            have never : ∀ earlier ∈ execution.recall actor,
                ¬ ActivatedAt setup leaks actor event earlier := by
              intro earlier remembered previous
              have yes := recorded event unfinished actor earlier remembered
                previous
              rw [old] at yes
              cases yes
            have fits := recovery_firstActivation_inclusionFits initialized nativeLaw opportunity
              timely raw rfl clear event turn never
            have rawSupported : (choices actor).1 ∈
                ((honestChoice setup leaks bounds (initialLaw setup) horizon scheduler source actor
                  (some (execution.recall actor,
                    execution.observe (application setup leaks) actor))).map
                      Subtype.val).support := by
              let rawLaw : (application setup leaks).Info →
                  PMF (Option (application setup leaks).Action) := fun info =>
                (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source actor
                  info).map Subtype.val
              have mapped : (choices actor).1 ∈ (rawLaw ((N).infoOf actor history.trace)).support :=
                (PMF.mem_support_map_iff Subtype.val _ _).mpr
                ⟨choices actor, chosen actor, rfl⟩
              exact Eq.mp (congrArg (fun info => (choices actor).1 ∈ (rawLaw info).support)
                observed) mapped
            obtain ⟨choice, localSupported, choiceEq⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp rawSupported
            obtain ⟨action, material, canonical, transmits, _⟩ :=
              honestChoice_canonical_of_debtFree wellFormed covers capacity source trace actor
                (forced actor) (notOwed actor) event pending bound fits _ localSupported
            have responseEq := Option.some.inj ((choiceEq.trans selected).symm.trans canonical)
            subst response
            apply (runtime setup).eventRecorded_respond
            rcases (runtime setup).canonicalServiceDecision_cases leaks actor
                (execution.recall actor) (execution.observe (application setup leaks) actor)
                event action with silent | named
            · rw [silent] at transmits
              cases transmits
            · exact named

variable
  (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks initial horizon recoveryScheduler
    bound)
  (completes : Recovery.CompletesPlay (runtime setup) leaks initial horizon recoveryScheduler)

include initialized nativeLaw opportunity timely inclusion completes in
/-- Honest play from an intended recovery boundary has no unanswered earlier
ready callback at any information state it reaches. -/
theorem recovery_honest_reached_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History) (anchor : (application setup leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∀ fuel (history : (E).History), history ∈ ((N).runBehavioralFrom
      (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source) fuel
        start).support → ∀ who, ¬ LateDelivery setup leaks who ((N).infoOf who history.trace) := by
  classical
  let players := honestProfile setup leaks bounds (initialLaw setup) horizon scheduler source
  have law := recovery_honest_boundary_readout_law initialized nativeLaw opportunity inclusion
    timely completes wellFormed covers capacity source certificate rank start anchor state boundary
    point decoded intended
  change _ = (setup.continuationLaw (setup.intendedOpeningProfile source.strategy)
    (sourceServicePrefix? setup rank anchor.application.config)).map some at law
  rw [decoded] at law
  have static := decodedPoint_staticAt
    ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded)
  have maintained : ∀ fuel (history : (E).History),
      history ∈ ((N).runBehavioralFrom players fuel start).support →
      ∃ control : (application setup leaks).Control, history.state = some control ∧
        ReadyTurnsRecorded control.execution := by
    intro fuel
    induction fuel with
    | zero =>
        intro history supported
        change history ∈ (PMF.pure start).support at supported
        cases (PMF.mem_support_pure_iff _ _).mp supported
        refine ⟨_, state, fun event unfinished who entry member activated => ?_⟩
        have beyond : rank ≤ event.val := by
          by_contra earlier
          exact unfinished ((boundary.ordered.2 event).mpr (by omega))
        exact (boundary.untouched event beyond who entry member
          (PublicView.ownTurn?_spec _ who event activated).1).elim
    | succ fuel ih =>
        intro history supported
        rw [(N).runBehavioralFrom_add players fuel 1 start] at supported
        obtain ⟨middle, earlier, next⟩ := (PMF.mem_support_bind_iff _ _ _).mp supported
        obtain ⟨control, current, recorded⟩ := ih middle earlier
        obtain ⟨sourcePoint, sourceDecoded, sourceIntended⟩ :=
          honest_reached_intended_of_readout_law bounds wellFormed source certificate start point
            static intended law fuel middle earlier control current
        rw [(N).runBehavioralFrom_one_localStep] at next
        obtain ⟨choices, drawn, stepped⟩ := (PMF.mem_support_bind_iff _ _ _).mp next
        exact readyTurnsRecorded_transition initialized nativeLaw opportunity timely wellFormed
          covers capacity source middle control current sourcePoint sourceDecoded sourceIntended
          recorded choices ((independentProduct_support_iff _ _).mp drawn) history stepped
  intro fuel history supported who late
  obtain ⟨control, current, recorded⟩ := maintained fuel history supported
  obtain ⟨past, view, event, same, pending, entry, member, activated⟩ := late
  rw [same] at pending
  have observes := (menu).info (initialLaw setup) horizon scheduler who history.trace
  have actual : (application setup leaks).observe who history.state = some (past, view) :=
    observes.symm.trans same
  rw [current] at actual
  rcases control with ⟨remaining, actor, execution⟩
  by_cases acting : actor = some who
  · subst actor
    simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      at actual
    obtain ⟨pastEq, viewEq⟩ := actual
    have pendingAt : pendingEvent setup leaks who (some (execution.recall who,
        execution.observe (application setup leaks) who)) = some event := by
      rw [pastEq, viewEq]
      exact pending
    obtain ⟨_, ready, _, unsent⟩ := pendingEvent_spec pendingAt
    have unfinished := ((execution.application.publicView_eventReady event).mp ready).1
    have remembered : entry ∈ execution.recall who := pastEq.symm ▸ member
    have yes := recorded event unfinished who entry remembered activated
    rw [unsent] at yes
    cases yes
  · simp [ReactiveApplication.observe, acting] at actual

end Vegas
