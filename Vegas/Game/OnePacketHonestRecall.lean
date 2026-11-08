/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketHonestContinuation
import Vegas.Game.OnePacketForcedPrefix
import Vegas.Game.OnePacketForcedRegular
import Vegas.Game.OnePacketDebtFreeResponse
import Vegas.Game.HonestContinuationIntended
import GameTheory.Analysis.Protocol.RestrictionDomination
import Interaction.ReactiveHistory
import Vegas.Pending.ReactiveGraphSteps
import Vegas.EventGraph.ObservationStep
import Vegas.Game.SourceDebtObservation

/-! # Honest ready callbacks are recorded under counted native service -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}
  {horizon : Nat}
  {scheduler : (application setup timeouts leaks).Scheduler}
  {delay bound : (graph setup).EventId → Nat}
  (opportunity : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    OpportunityAt timeouts leaks control.execution delay)
  (timely : (AsyncTimely timeouts) delay bound)

local notation "menu" => bounds.onePacketMenu timeouts leaks
local notation "N" => onePacketModel setup timeouts leaks bounds (initialLaw setup) horizon
  scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol menu (initialLaw setup) horizon
  scheduler

private def ReadyTurnsRecorded (execution : (application setup timeouts leaks).Execution) : Prop :=
  ∀ event : (graph setup).EventId, event ∉ execution.application.config.cut.completed →
    ∀ who entry, entry ∈ execution.logs who → ActivatedAt setup timeouts leaks who event entry →
      (eventRecorded timeouts) leaks (execution.logs who) event = true

include opportunity timely in
private theorem readyTurnsRecorded_transition
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (history : (E).History) (control : (application setup timeouts leaks).Control)
    (state : history.state = some control)
    (point : ProtocolState setup.program)
    (decoded : decodedPoint setup control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    (recorded : ReadyTurnsRecorded (timeouts := timeouts) control.execution)
    (choices : ∀ player, (N).Choice player ((N).infoOf player history.trace))
    (chosen : ∀ player, choices player ∈
      (honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler source player
        ((N).infoOf player history.trace)).support)
    (final : (E).History) (supported : final ∈ ((N).localStep history choices).support) :
    ∃ next : (application setup timeouts leaks).Control, final.state = some next ∧
      ReadyTurnsRecorded (timeouts := timeouts) next.execution := by
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
  have moved : after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
    scheduler
      (some control) (fun player => (choices player).1)).support := by
    let joint : Player → Option (application setup timeouts leaks).Action := fun player => (choices
      player).1
    change after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
      scheduler
      history.state joint).support at realized
    change after ∈ ((application setup timeouts leaks).transition (initialLaw setup) horizon
      scheduler
      (some control) joint).support
    rw [state] at realized
    exact realized
  obtain ⟨next, afterEq, _⟩ :=
    (application setup timeouts leaks).transition_recall_prefix (initialLaw setup) horizon
      scheduler control after (fun player => (choices player).1) moved
  have path := (reactive_protocol_graph_steps timeouts) leaks (initialLaw setup) horizon scheduler
    control next (fun player => (choices player).1) (by simpa only [afterEq] using moved)
  have completed := EventGraph.completed_subset_of_history_prefix _ _
    (EventGraph.Config.Step.path_history_prefix path)
  refine ⟨next, afterEq, ?_⟩
  have trace : (E).Trace (some control) := state ▸ history.trace
  have raw := (menu).toRawTrace (initialLaw setup) horizon scheduler trace
  have clear := defaulted_eq_empty_of_decodedIntended decoded intended
  have forced : ∀ player, ForcedState setup timeouts leaks player (some control) := fun player =>
    (forcedState_iff_decodedPoint (timeouts := timeouts) control).mpr
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
          have recallEq := (application setup timeouts leaks).environmentStep_recall execution
            ending
            command step
          rw [recallEq] at member ⊢
          exact recorded event (fun done => unfinished (completed done))
            player entry member activated
  | some actor =>
      have observed : (N).infoOf actor history.trace = some (execution.logs actor,
          execution.observe (application setup timeouts leaks) actor) := by
        have observes := (menu).info (initialLaw setup) horizon scheduler actor history.trace
        change (N).infoOf actor history.trace =
          (application setup timeouts leaks).observe actor history.state at observes
        exact observes.trans (by rw [state]; simp [ReactiveApplication.observe])
      have localLegal := ((N).menu_adequate actor history.trace (choices actor).1).mp
        (choices actor).2
      have selected : ∃ response, (choices actor).1 = some response := by
        cases choiceEq : (choices actor).1 with
        | none =>
            rw [choiceEq] at localLegal
            exfalso
            apply localLegal
            change (application setup timeouts leaks).actor history.state = some actor
            rw [state]
            rfl
        | some response => exact ⟨response, rfl⟩
      obtain ⟨response, selected⟩ := selected
      change after ∈ (PMF.pure _).support at moved
      have same := (PMF.mem_support_pure_iff _ _).mp moved
      simp only [selected, Option.getD_some] at same
      cases Option.some.inj (same.symm.trans afterEq)
      intro event unfinished player entry member activated
      rw [((reactive_respond_application timeouts) leaks execution actor response).1]
        at unfinished
      rcases (application setup timeouts leaks).respond_entry_origin execution actor player response
          entry member with earlier | ⟨samePlayer, sameView⟩
      · exact (eventRecorded_respond_of_recorded timeouts) leaks execution actor player
          response event (recorded event unfinished player entry earlier activated)
      · subst player
        have turn : execution.application.publicView.ownTurn? actor = some event := by
          change entry.beforeView.application.publicView.ownTurn? actor = some event at activated
          rw [sameView] at activated
          change execution.application.publicView.ownTurn? actor = some event at activated
          exact activated
        cases old : (eventRecorded timeouts) leaks (execution.logs actor) event with
        | true =>
            exact (eventRecorded_respond_of_recorded timeouts) leaks execution actor actor
              response event old
        | false =>
            have pending := pendingEvent_of_spec (timeouts := timeouts) (setup := setup) (leaks :=
              leaks) (who := actor)
              (past := execution.logs actor)
              (view := execution.observe (application setup timeouts leaks) actor) turn old
            have never : ∀ earlier ∈ execution.logs actor,
                ¬ ActivatedAt setup timeouts leaks actor event earlier := by
              intro earlier remembered previous
              have yes := recorded event unfinished actor earlier remembered
                previous
              rw [old] at yes
              cases yes
            have fits := firstActivation_inclusionFits_of_counted_opportunity setup timeouts leaks
              bounds horizon
              scheduler delay bound opportunity timely trace rfl clear event turn never
            have rawSupported : (choices actor).1 ∈
                ((honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
                  source actor
                  (some (execution.logs actor,
                    execution.observe (application setup timeouts leaks) actor))).map
                      Subtype.val).support := by
              let rawLaw : (application setup timeouts leaks).Info →
                  PMF (Option (application setup timeouts leaks).Action) := fun info =>
                (honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler
                  source actor
                  info).map Subtype.val
              have mapped : (choices actor).1 ∈ (rawLaw ((N).infoOf actor history.trace)).support :=
                (PMF.mem_support_map_iff Subtype.val _ _).mpr
                ⟨choices actor, chosen actor, rfl⟩
              exact Eq.mp (congrArg (fun info => (choices actor).1 ∈ (rawLaw info).support)
                observed) mapped
            obtain ⟨choice, localSupported, choiceEq⟩ :=
              (PMF.mem_support_map_iff _ _ _).mp rawSupported
            obtain ⟨action, material, canonical, transmits, _⟩ :=
              honestChoice_canonical_of_debtFree (timeouts := timeouts) wellFormed covers capacity
                source trace actor
                (forced actor) (notOwed actor) event pending bound fits _ localSupported
            have responseEq := Option.some.inj ((choiceEq.trans selected).symm.trans canonical)
            subst response
            apply (eventRecorded_respond timeouts)
            rcases (canonicalServiceDecision_cases timeouts) leaks actor
                (execution.logs actor) (execution.observe (application setup timeouts leaks) actor)
                event action with silent | named
            · rw [silent] at transmits
              cases transmits
            · exact named

variable
  (inclusion : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    ProtectedInclusionAt timeouts leaks control.execution bound)
  (completes : ∀ control : (application setup timeouts leaks).Control,
    ((bounds.onePacketMenu timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some control) →
    control.execution.application.config.defaulted = ∅ →
    (application setup timeouts leaks).terminal (some control) →
    control.execution.application.config.cut.Terminal)

include opportunity timely inclusion completes in
/-- Honest play from an intended counted boundary has no unanswered earlier
ready callback at any information state it reaches. -/
theorem counted_honest_reached_not_late
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment)
    (certificate : (E).WellFoundedHistories)
    (rank : Nat) (start : (E).History) (anchor : (application setup timeouts leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup timeouts leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    ∀ fuel (history : (E).History), history ∈ ((N).runBehavioralFrom
      (honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler source) fuel
        start).support → ∀ who, ¬ LateDelivery setup timeouts leaks who ((N).infoOf who
          history.trace) := by
  classical
  let players := honestProfile setup timeouts leaks bounds (initialLaw setup) horizon scheduler
    source
  have law := counted_honest_boundary_readout_law (timeouts := timeouts) opportunity inclusion
    timely completes covers capacity source certificate rank start anchor state boundary
    point decoded intended
  change _ = (setup.continuationLaw (setup.intendedOpeningProfile source.strategy)
    (sourceServicePrefix? setup rank anchor.application.config)).map some at law
  rw [decoded] at law
  have static := decodedPoint_staticAt
    ((decodedPoint_eq_of_isPrefix boundary.ordered).trans decoded)
  have maintained : ∀ fuel (history : (E).History),
      history ∈ ((N).runBehavioralFrom players fuel start).support →
      ∃ control : (application setup timeouts leaks).Control, history.state = some control ∧
        ReadyTurnsRecorded (timeouts := timeouts) control.execution := by
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
          honest_reached_intended_of_readout_law bounds wellFormed source
            certificate start point
            static intended law fuel middle earlier control current
        rw [(N).runBehavioralFrom_one_localStep] at next
        obtain ⟨choices, drawn, stepped⟩ := (PMF.mem_support_bind_iff _ _ _).mp next
        exact readyTurnsRecorded_transition (timeouts := timeouts) opportunity timely wellFormed
          covers capacity source middle control current sourcePoint sourceDecoded sourceIntended
          recorded choices ((independentProduct_support_iff _ _).mp drawn) history stepped
  intro fuel history supported who late
  obtain ⟨control, current, recorded⟩ := maintained fuel history supported
  obtain ⟨past, view, event, same, pending, entry, member, activated⟩ := late
  rw [same] at pending
  have observes := (menu).info (initialLaw setup) horizon scheduler who history.trace
  have actual : (application setup timeouts leaks).observe who history.state = some (past, view) :=
    observes.symm.trans same
  rw [current] at actual
  rcases control with ⟨remaining, actor, execution⟩
  by_cases acting : actor = some who
  · subst actor
    simp only [ReactiveApplication.observe, ↓reduceIte, Option.some.injEq, Prod.mk.injEq]
      at actual
    obtain ⟨pastEq, viewEq⟩ := actual
    have pendingAt : pendingEvent setup timeouts leaks who (some (execution.logs who,
        execution.observe (application setup timeouts leaks) who)) = some event := by
      rw [pastEq, viewEq]
      exact pending
    obtain ⟨_, ready, _, unsent⟩ := pendingEvent_spec (timeouts := timeouts) pendingAt
    have unfinished := ((execution.application.publicView_eventReady event).mp ready).1
    have remembered : entry ∈ execution.logs who := pastEq.symm ▸ member
    have yes := recorded event unfinished who entry remembered activated
    rw [unsent] at yes
    cases yes
  · simp [ReactiveApplication.observe, acting] at actual

end Vegas
