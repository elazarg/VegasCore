/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceCleanCompletionLaw
import Interaction.ReactiveRecallEntries
import Interaction.ReactiveRecordedResponse

/-! # Source-relative prescriptions at native information

First turns and binding deferrals retain arbitrary-source compatibility
witnesses. At a later unrecorded resolution turn, the owner's actual recall
must instead give positive reference silence likelihood at its protected
first turn. A silence caused only by a source tremble at a pure-opening
reference input does not meet this condition.

The condition is a property of recalled information, not a runtime gate.
Its first-turn containment is structural; neither posterior transport nor
sequential rationality is asserted.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram Interaction EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

/-- Every actual first entry for this event was protected silence with
positive likelihood under the fixed reference source profile. -/
def protectedFirstSilence (reference : BehavioralProfile service.setup.program)
    (who : Player) (event : (graph service.setup).EventId)
    (past : List (application service.setup service.leaks).PlayerEntry) : Prop :=
  ∀ before entry after, past = before ++ entry :: after →
    sourceServiceTurn service.setup service.leaks who event before entry.beforeView = some 0 →
      entry.action = ⟨none⟩ ∧
        (runtime service.setup).eventRecorded service.leaks before event = false ∧
        entry.beforeView.application.publicView.InclusionFitsDeadline (runtime service.setup)
          service.bound event ∧
        (⟨none⟩ : (application service.setup service.leaks).Action) ∈
          (sourceServiceCanonicalOpportunity service.setup service.leaks service.bound reference
            who event before entry.beforeView).support

/-- Source compatibility retains a later unrecorded resolution only when
the fixed reference can produce its actual protected first silence. -/
def sourcePrescribedInfo (reference : BehavioralProfile service.setup.program) (who : Player)
    (info : (application service.setup service.leaks).Info) : Prop :=
  service.sourceCompatibleInfo who info ∧
    ∀ past view, info = some (past, view) →
      ∀ event payload, view.application.publicView.ownTurn? who = some event →
        (graph service.setup).outputLayout event = .publication payload →
        (runtime service.setup).eventRecorded service.leaks past event = false →
          sourceServiceTurn service.setup service.leaks who event past view = some 0 ∨
            service.protectedFirstSilence reference who event past

/-- Every compatible first own turn remains prescribed, independently of
which source profile supplied its compatibility witness. -/
theorem sourcePrescribedInfo_of_first_turn
    (reference : BehavioralProfile service.setup.program) (who : Player)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId)
    (first : sourceServiceTurn service.setup service.leaks who event past view = some 0) :
    service.sourcePrescribedInfo reference who (some (past, view)) := by
  refine ⟨compatible, ?_⟩
  intro otherPast otherView same current _payload turn _layout _unrecorded
  cases Option.some.inj same
  have sameEvent : current = event := Option.some.inj
    (turn.symm.trans (sourceServiceTurn_first first).1)
  subst current
  exact Or.inl first

/-- Compatible binding turns are prescribed even after earlier deferrals.
The additional filter concerns publications alone. -/
theorem sourcePrescribedInfo_of_binding
    (reference : BehavioralProfile service.setup.program) (who : Player)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (compatible : service.sourceCompatibleInfo who (some (past, view)))
    (event : (graph service.setup).EventId) (owner : Player) (payload : L.Ty)
    (turn : view.application.publicView.ownTurn? who = some event)
    (binding : (graph service.setup).outputLayout event = .binding owner payload) :
    service.sourcePrescribedInfo reference who (some (past, view)) := by
  refine ⟨compatible, ?_⟩
  intro otherPast otherView same current _publication serving layout _unrecorded
  cases Option.some.inj same
  have sameEvent : current = event := Option.some.inj (serving.symm.trans turn)
  subst current
  rw [binding] at layout
  cases layout

/-- A zero reference silence likelihood at an actual recalled first turn
excludes a later unrecorded resolution information value. -/
theorem sourcePrescribedInfo_excludes_zero_first_silence
    (reference : BehavioralProfile service.setup.program) (who : Player)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (turn : view.application.publicView.ownTurn? who = some event)
    (publication : (graph service.setup).outputLayout event = .publication payload)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false)
    (later : sourceServiceTurn service.setup service.leaks who event past view ≠ some 0)
    (before : List (application service.setup service.leaks).PlayerEntry)
    (entry : (application service.setup service.leaks).PlayerEntry)
    (after : List (application service.setup service.leaks).PlayerEntry)
    (recalled : past = before ++ entry :: after)
    (first : sourceServiceTurn service.setup service.leaks who event before entry.beforeView =
      some 0)
    (zero : (sourceServiceCanonicalOpportunity service.setup service.leaks service.bound reference
      who event before entry.beforeView) ⟨none⟩ = 0) :
    ¬ service.sourcePrescribedInfo reference who (some (past, view)) := by
  intro prescribed
  rcases prescribed.2 past view rfl event payload turn publication unrecorded with firstNow | kept
  · exact later firstNow
  · exact (PMF.mem_support_iff _ _).mp (kept before entry after recalled first).2.2.2 zero

omit [Fintype Player] in
private theorem firstTurn_protected_at_legal_history
    (menu : (application service.setup service.leaks).ResponseMenu)
    (who : Player) (remaining : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (trace : (menu.protocol (initialLaw service.setup) service.horizon service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩))
    (event : (graph service.setup).EventId)
    (first : sourceServiceTurn service.setup service.leaks who event (execution.recall who)
      (execution.observe (application service.setup service.leaks) who) = some 0) :
    execution.application.publicView.InclusionFitsDeadline (runtime service.setup) service.bound
      event := by
  let app := application service.setup service.leaks
  have actual := menu.roundSupported_uniform (initialLaw service.setup) service.horizon
    service.scheduler trace
  obtain ⟨_lengthEq, count, prior, command, counted, priorMem, selected, active, moved⟩ := actual
  have commandEq : command = .activate who := by
    cases command with
    | activate principal =>
        exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
    | wait | «include» _ | application _ => cases active
  subst commandEq
  have appEq := activation_application service.setup service.leaks prior execution who moved
  have recallEq := app.environmentStep_recall prior execution (.activate who) moved
  have ownTurn := (sourceServiceTurn_first first).1
  have served := PublicView.ownTurn?_spec execution.application.publicView who event ownTurn
  obtain ⟨rawTrace⟩ := app.raw_trace_roundsFrom (initialLaw service.setup) service.horizon
    service.scheduler menu.uniformResponses count (by omega) prior priorMem
  have firstBefore : sourceServiceTurn service.setup service.leaks who event (prior.recall who)
      (execution.observe app who) = some 0 := by rw [← recallEq]; exact first
  have fits := firstTurn_inclusionFits service.contract service.timely rawTrace
    (roundsFrom_activationsAnswered count prior priorMem) served.2
    (by rw [← appEq]; exact (execution.application.publicView_eventReady event).mp served.1)
      firstBefore
  rw [appEq]
  exact fits

/-- Actual first-turn play can recall an unrecorded event's first response
only as protected silence having positive reference source likelihood. -/
theorem firstTurnProfile_recalled_first_silence
    (turns : Nat) (reference : BehavioralProfile service.setup.program)
    (permitted : ∀ who, (reference who).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (fuel : Nat)
    (history : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
          (service.firstTurnProfile turns reference) fuel).support)
    (who : Player) (remaining : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (event : (graph service.setup).EventId)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
      event = false)
    (before : List (application service.setup service.leaks).PlayerEntry)
    (entry : (application service.setup service.leaks).PlayerEntry)
    (after : List (application service.setup service.leaks).PlayerEntry)
    (recalled : execution.recall who = before ++ entry :: after)
    (first : sourceServiceTurn service.setup service.leaks who event before entry.beforeView =
      some 0) :
    entry.action = ⟨none⟩ ∧
      (runtime service.setup).eventRecorded service.leaks before event = false ∧
      entry.beforeView.application.publicView.InclusionFitsDeadline (runtime service.setup)
        service.bound event ∧
      (⟨none⟩ : (application service.setup service.leaks).Action) ∈
        (sourceServiceCanonicalOpportunity service.setup service.leaks service.bound reference
          who event before entry.beforeView).support := by
  let app := application service.setup service.leaks
  let risk := service.bounds.riskMenu (runtime service.setup) service.leaks service.bound
  let canonical := service.bounds.canonicalMenu (runtime service.setup) service.leaks
  let model := canonical.information (initialLaw service.setup) service.horizon service.scheduler
  let players := sourceServiceTurnPolicy service.setup service.leaks service.bound turns
    (firstTurnTiming service.setup turns) reference
  have actual := service.firstTurnProfile_initialized_roundSupported turns reference permitted fuel
    history reached
  have allClear : (runtime service.setup).AllPersistentServiceRiskClear service.leaks service.bound
      history.state := by
    intro control same player
    have full := sourceServiceFirstTurn_serviceRisk_clear_roundSupported service.contract
      service.timely players player turns reference rfl control (same ▸ actual)
    exact ((runtime service.setup).serviceRisk_clear_iff service.leaks service.bound player
      _ _).mp full |>.1
  have riskTrace : (risk.protocol (initialLaw service.setup) service.horizon
      service.scheduler).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  obtain ⟨canonicalTrace, _sameRaw⟩ := service.bounds.riskTrace_canonical_of_persistentClear
    (runtime service.setup) service.leaks service.bound (initialLaw service.setup) service.horizon
    service.scheduler riskTrace (by
      intro control same player
      exact allClear control (current.trans same) player)
  let canonicalHistory : (canonical.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History := ⟨_, canonicalTrace⟩
  have observed : model.infoOf who canonicalTrace =
      some (execution.recall who, execution.observe app who) := by
    change (canonical.signals (initialLaw service.setup) service.horizon service.scheduler).infoOf
      who canonicalTrace = _
    rw [canonical.info]
    simp only [ReactiveApplication.observe, ↓reduceIte]
    rfl
  have member : (some (before, entry.beforeView), entry.action) ∈
      model.ownPlay who canonicalTrace := by
    rw [canonical.ownPlay_of_info_some (initialLaw service.setup) service.horizon service.scheduler
      who canonicalHistory _ _ observed, recalled]
    unfold ReactiveApplication.recallOwnPlay
    rw [app.ownPlayFrom_concat]
    apply List.mem_append_left
    simp only [List.nil_append, ReactiveApplication.ownPlayFrom, List.mem_append,
      List.mem_singleton]
    exact Or.inr trivial
  obtain ⟨prior, joint, legal, _next, _moved, _count, input, chosen, _path⟩ :=
    model.ownPlay_prefix who canonicalTrace member
  have nativeInput :=
    (canonical.info (initialLaw service.setup) service.horizon service.scheduler who
      prior.trace).symm.trans input
  have acting := (app.observe_isSome who prior.state).mp (by
    rw [nativeInput]
    exact Option.isSome_some)
  cases state : prior.state with
  | none => rw [state] at acting; cases acting
  | some control =>
      obtain ⟨earlierRemaining, earlierActor, earlier⟩ := control
      rw [state] at acting
      change earlierActor = some who at acting
      subst earlierActor
      rw [state] at nativeInput
      simp only [ReactiveApplication.observe, ↓reduceIte] at nativeInput
      have pastEq := congrArg Prod.fst (Option.some.inj nativeInput)
      have viewEq := congrArg Prod.snd (Option.some.inj nativeInput)
      change earlier.recall who = before at pastEq
      change earlier.observe app who = entry.beforeView at viewEq
      have earlierTrace : (canonical.protocol (initialLaw service.setup) service.horizon
          service.scheduler).Trace (some ⟨earlierRemaining, some who, earlier⟩) :=
        state ▸ prior.trace
      have admitted : entry.action ∈ service.bounds.canonicalActions (runtime service.setup)
          service.leaks who before entry.beforeView := by
        have permitted := legal.2 who
        rw [chosen, state] at permitted
        have atEarlier : entry.action ∈ service.bounds.canonicalActions (runtime service.setup)
            service.leaks who (earlier.recall who) (earlier.observe app who) := permitted.2
        simpa only [pastEq, viewEq] using atEarlier
      have entryMember : entry ∈ execution.recall who := by
        rw [recalled]
        exact List.mem_append_right _ List.mem_cons_self
      have neverNamed : (runtime service.setup).submittedEvent? service.leaks entry.action ≠
          some event := by
        intro named
        have recorded : (runtime service.setup).eventRecorded service.leaks (execution.recall who)
            event = true := List.any_eq_true.mpr ⟨entry, entryMember, decide_eq_true named⟩
        rw [unrecorded] at recorded
        cases recorded
      have silent : entry.action = ⟨none⟩ := by
        rcases service.bounds.canonicalActions_cases (runtime service.setup) service.leaks who
            before entry.beforeView entry.action admitted with silent |
            ⟨other, action, served, _, _, _, _, _, decided⟩
        · exact silent
        · have sameEvent : other = event := Option.some.inj
            (served.symm.trans (sourceServiceTurn_first first).1)
          subst other
          rcases (runtime service.setup).canonicalServiceDecision_cases service.leaks who before
              entry.beforeView event action with silent | named
          · exact decided.trans silent
          · exact (neverNamed (decided ▸ named)).elim
      have unrecordedBefore : (runtime service.setup).eventRecorded service.leaks before event =
          false := by
        have unsent := unrecorded
        rw [recalled, (runtime service.setup).eventRecorded_append] at unsent
        exact (Bool.or_eq_false_iff.mp unsent).1
      have firstEarlier : sourceServiceTurn service.setup service.leaks who event
          (earlier.recall who) (earlier.observe app who) = some 0 := by
        rw [pastEq, viewEq]
        exact first
      have fits := service.firstTurn_protected_at_legal_history canonical who earlierRemaining
        earlier earlierTrace event firstEarlier
      have fitsView : entry.beforeView.application.publicView.InclusionFitsDeadline
          (runtime service.setup) service.bound event := by
        rw [← viewEq]
        exact fits
      refine ⟨silent, unrecordedBefore, fitsView, ?_⟩
      let raw := app.information (initialLaw service.setup) service.horizon service.scheduler
      let rawHistory := risk.toRawHistory (initialLaw service.setup) service.horizon
        service.scheduler history
      have mappedPositive :
          (((risk.information (initialLaw service.setup) service.horizon
            service.scheduler).runBehavioral (service.firstTurnProfile turns reference) fuel).map
              (risk.toRawHistory (initialLaw service.setup) service.horizon service.scheduler))
                rawHistory ≠ 0 := by
        rw [pmf_map_apply_of_injective _ (risk.toRawHistory_injective _ _ _)]
        exact (PMF.mem_support_iff _ _).mp reached
      have physicalMass := sourceServiceTurnPolicy_cleanPrefix_probability service.bounds
        service.values service.initialValues service.capacity service.bound turns
          (firstTurnTiming service.setup turns) reference permitted service.horizon
            service.scheduler fuel rawHistory allClear
      have physicalSupport : rawHistory ∈
          (raw.runBehavioral (fun player => app.encodePolicy (players player)) fuel).support :=
        (PMF.mem_support_iff _ _).mpr (physicalMass ▸ mappedPositive)
      have depth := (app.protocol (initialLaw service.setup) service.horizon
        service.scheduler).runRandomizedFor_terminal_or_length (raw.randomizedChooser
          (fun player => app.encodePolicy (players player))) fuel _ _ physicalSupport
      have atDepth : rawHistory.trace.length = fuel := by
        have maximum := ((app.protocol (initialLaw service.setup) service.horizon
          service.scheduler).runRandomizedFor_reachesWithin
            (raw.randomizedChooser (fun player => app.encodePolicy (players player))) fuel _ _
              physicalSupport).trace_length_le_add
        simp only [ExecutionProtocol.initHistory, Trace.length, zero_add] at maximum
        rcases depth with terminal | depth
        · change (app.protocol (initialLaw service.setup) service.horizon
            service.scheduler).terminal history.state at terminal
          rw [current] at terminal
          cases terminal.2
        · simp only [ExecutionProtocol.initHistory, Trace.length, zero_add] at depth
          omega
      have positive : 0 <
          (raw.historyReachWeight (fun player => app.encodePolicy (players player))
            rawHistory).toReal := by
        apply pmf_toReal_pos_iff.mpr
        simpa only [InformationModel.historyReachWeight, atDepth] using physicalSupport
      have rawMember : (some (before, entry.beforeView), entry.action) ∈
          raw.ownPlay who rawHistory.trace := by
        change _ ∈ (app.signals (initialLaw service.setup) service.horizon
          service.scheduler).ownPlay who rawHistory.trace
        rw [app.trace_ownPlay]
        change (some (before, entry.beforeView), entry.action) ∈
          app.recallOwnPlay (app.recallAt who history.state)
        rw [current]
        change _ ∈ app.recallOwnPlay (execution.recall who)
        rw [recalled]
        unfold ReactiveApplication.recallOwnPlay
        rw [app.ownPlayFrom_concat]
        apply List.mem_append_left
        simp only [List.nil_append, ReactiveApplication.ownPlayFrom, List.mem_append,
          List.mem_singleton]
        exact Or.inr trivial
      have supported := raw.ownPlay_supported_of_historyReach_pos
        (fun player => app.encodePolicy (players player)) who rawHistory.trace positive rawMember
      simp only [ReactiveApplication.encodePolicy, PMF.map_comp, Function.comp_def,
        PMF.support_map] at supported
      obtain ⟨response, supported, same⟩ := supported
      cases Option.some.inj same
      have owned := (PublicView.ownTurn?_spec entry.beforeView.application.publicView who event
        (sourceServiceTurn_first first).1).2
      have selected := sourceServiceTurnPolicy_firstTurn (profile := reference) (turns := turns)
        (bound := service.bound) owned first
      change entry.action ∈ (sourceServiceTurnPolicy service.setup service.leaks service.bound
        turns (firstTurnTiming service.setup turns) reference who before entry.beforeView).support
        at supported
      rw [selected, silent] at supported
      exact supported

/-- The later-turn condition is not vacuous: prescribed unrecorded
resolutions have an actual protected first-silence entry in own recall. -/
theorem sourcePrescribedInfo_later_resolution_witness
    (reference : BehavioralProfile service.setup.program) (who : Player)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (prescribed : service.sourcePrescribedInfo reference who (some (past, view)))
    (event : (graph service.setup).EventId) (payload : L.Ty)
    (turn : view.application.publicView.ownTurn? who = some event)
    (publication : (graph service.setup).outputLayout event = .publication payload)
    (unrecorded : (runtime service.setup).eventRecorded service.leaks past event = false)
    (later : sourceServiceTurn service.setup service.leaks who event past view ≠ some 0) :
    ∃ before entry after, past = before ++ entry :: after ∧
      sourceServiceTurn service.setup service.leaks who event before entry.beforeView = some 0 ∧
      entry.action = ⟨none⟩ ∧
        (runtime service.setup).eventRecorded service.leaks before event = false ∧
        entry.beforeView.application.publicView.InclusionFitsDeadline (runtime service.setup)
          service.bound event ∧
        (⟨none⟩ : (application service.setup service.leaks).Action) ∈
          (sourceServiceCanonicalOpportunity service.setup service.leaks service.bound reference
            who event before entry.beforeView).support := by
  classical
  have seen : ∃ entry ∈ past,
      entry.beforeView.application.publicView.ownTurn? who = some event := by
    by_contra absent
    apply later
    unfold sourceServiceTurn
    simp only [turn, ↓reduceIte, Option.some.injEq]
    rw [List.countP_eq_zero]
    intro entry member chosen
    exact absent ⟨entry, member, of_decide_eq_true chosen⟩
  obtain ⟨before, entry, after, recalled, first⟩ := exists_first_turn past seen
  rcases prescribed.2 past view rfl event payload turn publication unrecorded with now | kept
  · exact (later now).elim
  · exact ⟨before, entry, after, recalled, first, kept before entry after recalled first⟩

/-- Every decision visited by the fixed reference's exact first-turn profile
is prescribed, including later resolution silence that the reference allows. -/
theorem firstTurnProfile_sourcePrescribedInfo
    (turns : Nat) (reference : BehavioralProfile service.setup.program)
    (permitted : ∀ player, (reference player).Admitted service.setup.program
      (CommitmentInterface.values service.setup.program))
    (effective : ∀ player, (reference player).EffectiveDisclosures service.setup.program []
      (Revelations.initial service.setup.context))
    (fuel : Nat)
    (history : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).History)
    (reached : history ∈
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
          (service.firstTurnProfile turns reference) fuel).support)
    (who : Player)
    (active : ((service.bounds.riskMenu (runtime service.setup) service.leaks
      service.bound).protocol (initialLaw service.setup) service.horizon service.scheduler).active
        history.state who) :
    service.sourcePrescribedInfo reference who
      (((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who
          history.trace) := by
  have compatible := service.firstTurnProfile_sourceCompatibleInfo turns reference permitted
    effective fuel history reached who active
  have atState :
      ((service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).information
        (initialLaw service.setup) service.horizon service.scheduler).infoOf who history.trace =
      (application service.setup service.leaks).observe who history.state :=
    (service.bounds.riskMenu (runtime service.setup) service.leaks service.bound).info
      (initialLaw service.setup) service.horizon service.scheduler who history.trace
  refine ⟨compatible, ?_⟩
  rw [atState]
  cases current : history.state with
  | none => rw [current] at active; cases active
  | some control =>
      obtain ⟨remaining, actor, execution⟩ := control
      rw [current] at active
      change actor = some who at active
      subst actor
      intro past view observed event _payload _turn _publication unrecorded
      have native := observed
      simp only [ReactiveApplication.observe, ↓reduceIte] at native
      cases Option.some.inj native
      by_cases first : sourceServiceTurn service.setup service.leaks who event
          (execution.recall who) (execution.observe (application service.setup service.leaks) who) =
            some 0
      · exact Or.inl first
      · refine Or.inr ?_
        intro before entry after recalled first
        exact service.firstTurnProfile_recalled_first_silence turns reference permitted fuel history
          reached who remaining execution current event unrecorded before entry after recalled first

end Vegas.AsyncServiceSpec
