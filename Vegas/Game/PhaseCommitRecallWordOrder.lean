/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseBindingRecallWord
import Vegas.Pending.PhaseBindingRecallOrder
import Vegas.Game.PhaseCommitWordRecall
import Vegas.Pending.PhaseBindingReadiness
import Vegas.Pending.PhaseFailureCoverage
import Vegas.EventGraph.ReadySemanticStability

/-! # Source order of the actual parsed current-attempt commitment word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}
  (whole : SourceProgram Player L Γ O) (mode : ExecutionMode)
  (runtime : EventGraphRuntime ((toEventGraph whole).withMode mode))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph whole).withMode mode)))

local notation "app" => phaseApplication runtime leaks

private def parsedBinding? (low high generation : Nat) (entry : (app).PlayerEntry) :
    Option (((toEventGraph whole).withMode mode).EventId × OwnAction Player L) :=
  if entry.beforeView.application.2.attempt = ⟨low, generation⟩ then
    match entry.action.transmission with
    | none => none
    | some material =>
        match material.call.packet with
        | .commitment event _ =>
            if low ≤ event.val ∧ event.val < high then
              (phaseBindingAction? whole mode runtime leaks entry.action).map (event, ·)
            else none
        | _ => none
  else none

private theorem parsedBinding?_spec (low high generation : Nat) (entry : (app).PlayerEntry)
    (record : ((toEventGraph whole).withMode mode).EventId × OwnAction Player L)
    (present : parsedBinding? whole mode runtime leaks low high generation entry = some record) :
    entry.beforeView.application.2.attempt = ⟨low, generation⟩ ∧
      low ≤ record.1.val ∧ record.1.val < high ∧
      ∃ (material : WitnessedSubmission ((toEventGraph whole).withMode mode))
        (candidate : Handle ((toEventGraph whole).withMode mode)),
        entry.action.transmission = some material ∧
        material.call.packet = .commitment record.1 candidate ∧
        phaseBindingAction? whole mode runtime leaks entry.action = some record.2 := by
  unfold parsedBinding? at present
  split at present
  · rename_i attempt
    cases transmitted : entry.action.transmission with
    | none => simp only [transmitted, reduceCtorEq] at present
    | some material =>
        simp only [transmitted] at present
        cases packet : material.call.packet with
        | commitment event candidate =>
            simp only [packet] at present
            split at present
            · rename_i inside
              obtain ⟨action, decoded, paired⟩ := Option.map_eq_some_iff.mp present
              cases paired
              exact ⟨attempt, inside.1, inside.2, material, candidate, rfl, packet, decoded⟩
            · cases present
        | opening | malformed => simp only [packet, reduceCtorEq] at present
  · cases present

private theorem parsedBinding?_word (low high generation : Nat)
    (past : List (app).PlayerEntry) :
    ((past.filterMap (parsedBinding? whole mode runtime leaks low high generation)).map
      Prod.snd) = phaseCommitRecallWord whole mode runtime leaks low high generation past := by
  simp only [phaseCommitRecallWord, List.map_filterMap]
  apply congrArg (fun read => past.filterMap read)
  funext entry
  unfold parsedBinding?
  by_cases attempt : entry.beforeView.application.2.attempt = ⟨low, generation⟩
  · simp only [ite_eq_left attempt]
    cases transmitted : entry.action.transmission with
    | none => rfl
    | some material =>
        change WitnessedSubmission ((toEventGraph whole).withMode mode) at material
        rcases material with ⟨⟨packet, preparation⟩, evidence⟩
        cases packet with
        | commitment event candidate =>
            dsimp only
            by_cases inside : low ≤ event.val ∧ event.val < high
            · simp only [ite_eq_left inside, Option.map_map]
              cases phaseBindingAction? whole mode runtime leaks entry.action <;> rfl
            · simp only [ite_eq_right inside, Option.map_none]
        | opening | malformed => rfl
  · simp only [ite_eq_right attempt, Option.map_none]

variable [Fintype Player]

private theorem parsedBinding?_ordered
    (bounds : MessageBounds ((toEventGraph whole).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (low high generation : Nat) :
    ((control.execution.recall who).filterMap
      (parsedBinding? whole mode runtime leaks low high generation)).Pairwise
        (fun first second => first.1.val < second.1.val) := by
  let read := parsedBinding? whole mode runtime leaks low high generation
  have ordered : ∀ (rest earlier : List (app).PlayerEntry),
      control.execution.recall who = earlier ++ rest →
        (rest.filterMap read).Pairwise (fun first second => first.1.val < second.1.val) := by
    intro rest
    induction rest with
    | nil => intro earlier _same; exact .nil
    | cons entry rest ih =>
        intro earlier same
        have after : control.execution.recall who = (earlier ++ [entry]) ++ rest := by
          simpa only [List.append_assoc, List.singleton_append] using same
        have tail := ih (earlier ++ [entry]) after
        cases firstRead : read entry with
        | none => simpa only [List.filterMap_cons, firstRead] using tail
        | some first =>
            simp only [List.filterMap_cons, firstRead]
            apply List.pairwise_cons.mpr
            refine ⟨?_, tail⟩
            intro second member
            obtain ⟨laterEntry, retained, secondRead⟩ := List.mem_filterMap.mp member
            obtain ⟨middle, later, splitRest⟩ := List.mem_iff_append.mp retained
            obtain ⟨firstTag, _firstLow, _firstHigh, firstMaterial, firstCandidate, firstSent,
              firstNamed, _firstDecoded⟩ := parsedBinding?_spec whole mode runtime leaks low high
                generation entry first firstRead
            obtain ⟨secondTag, _secondLow, _secondHigh, secondMaterial, secondCandidate,
              secondSent, secondNamed, _secondDecoded⟩ := parsedBinding?_spec whole mode runtime
                leaks low high generation laterEntry second secondRead
            have recalled : control.execution.recall who =
                earlier ++ entry :: (middle ++ laterEntry :: later) := by rw [same, splitRest]
            exact PhaseCount.recorded_binding_rank_lt runtime leaks bounds plan
              ((toEventGraph whole).withMode_revealRelaxedOrdered
                (toEventGraph_barrierOrdered whole) mode) inputs horizon scheduler trace clear who
                  earlier entry middle laterEntry later recalled firstMaterial secondMaterial
                    firstSent secondSent first.1 second.1 firstCandidate secondCandidate
                      firstNamed
                      secondNamed (firstTag.trans secondTag.symm)
  exact ordered _ [] rfl

/-- Actual parsed current-attempt sends retain strictly increasing static
event addresses. The witnesses are the raw records themselves; no sortedness
condition is imposed on the history or its source interpretation. -/
theorem phaseCommitRecallWord_ordered
    (bounds : MessageBounds ((toEventGraph whole).withMode mode))
    (plan : RuntimePhasePlan ((toEventGraph whole).withMode mode))
    (inputs : PMF ((toEventGraph whole).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) {control : (app).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (who : Player) (low high generation : Nat) :
    ∃ records : List (((toEventGraph whole).withMode mode).EventId × OwnAction Player L),
      records.map Prod.snd = phaseCommitRecallWord whole mode runtime leaks low high generation
        (control.execution.recall who) ∧
      records.Pairwise (fun first second => first.1.val < second.1.val) ∧
      ∀ record ∈ records, low ≤ record.1.val ∧ record.1.val < high := by
  let read := parsedBinding? whole mode runtime leaks low high generation
  refine ⟨(control.execution.recall who).filterMap read, parsedBinding?_word whole mode runtime
    leaks low high generation _, ?_, ?_⟩
  · exact parsedBinding?_ordered whole mode runtime leaks bounds plan inputs horizon scheduler trace
      clear who low high generation
  · intro record member
    obtain ⟨entry, _retained, decoded⟩ := List.mem_filterMap.mp member
    have present := parsedBinding?_spec whole mode runtime leaks low high generation entry record
      decoded
    exact ⟨present.2.1, present.2.2.1⟩


/-- Below the current ready binding, the literal current-attempt raw sends
are exactly the surviving chronological original own actions. Original failed
results are retained. All completion and earlier-callback coverage follows from
the actual initialized trace and the selected word member's consistency. -/
theorem phaseCommitRecallWord_eq_completed
    (setup : Setup (Player := Player) (L := L))
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    {start finish : SourceCtx Player L} {startOpen finishOpen : Finset VarId}
    (block : CommitPrefix start startOpen finish finishOpen) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player) (word : DecisionView who finish)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout selected = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (inside : low ≤ selected.val ∧ selected.val < low + block.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (consistent : (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded who word).Consistent
        (control.execution.recall who)) :
    phaseCommitRecallWord setup.program mode runtime leaks low selected.val generation
        (control.execution.recall who) =
      decodeCompletions setup.program
        ((((serviceGraph setup mode).ownCompletions who
          control.execution.application.current.native.config.history).filter
            (fun completion => decide (low ≤ completion.event.val ∧
              completion.event.val < selected.val))).map
                ((toEventGraph setup.program).fromModeCompletion mode)) := by
  classical
  let graph := serviceGraph setup mode
  let native := control.execution.application.current.native
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let read := parsedBinding? setup.program mode runtime leaks low selected.val generation
  let decoded := fun completion : graph.Completion =>
    (decodeEventAction setup.program completion.event completion.action).map
      (completion.event, ·)
  let completed := (graph.ownCompletions who native.config.history).filter
    (fun completion => decide (low ≤ completion.event.val ∧ completion.event.val < selected.val))
  let actual := (control.execution.recall who).filterMap read
  let expected := completed.filterMap decoded
  have raw := menu.toRawTrace initial horizon scheduler trace
  obtain ⟨_draw, invariant⟩ := phaseNativeInvariant_history runtime leaks plan inputs horizon
    scheduler raw
  have reachable := invariant.active.reachable
  have valid := (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have coverage := (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    raw).active
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  obtain ⟨phase, remaining, installed, commitment, selectedMember⟩ :=
    phase_ready_binding_phase runtime leaks plan ordered maximal inputs horizon scheduler raw who
      selected payload binding request.2.2.1
  have phaseLow : phase.low = low := by
    have lower := congrArg CommitAttemptId.phase address
    simpa only [PhaseRuntimeState.attempt, installed, List.head?_cons, Option.map_some,
      Option.getD_some] using lower
  have selectedHigh := ((phase.mem_events selected).mp selectedMember).2
  have kind (event : graph.EventId) (lower : low ≤ event.val) (upper : event.val < selected.val)
      (actor : graph.actor? event = some who) :
      ∃ value, graph.outputLayout event = .binding who value := by
    have fields := phase.fields event (phaseLow ▸ lower) (by omega)
    rw [commitment] at fields
    obtain ⟨owner, value, shape⟩ := fields
    have same := Option.some.inj ((EventGraph.actor?_of_outputLayout_binding graph shape).symm.trans
      actor)
    cases same
    exact ⟨value, shape⟩
  have done (event : graph.EventId) (upper : event.val < selected.val)
      (actor : graph.actor? event = some who) : event ∈ native.config.cut.completed := by
    exact (ordered.ready_visible_iff native.config.cut request.2.2.1 request.2.2.2.1
      (EventCode.output_visible_of_actor (graph.nodes event) who actor)
      (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))
      (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))).mpr upper
  have receipt (event : graph.EventId) (value : L.Ty)
      (shape : graph.outputLayout event = .binding who value)
      (finished : event ∈ native.config.cut.completed) :
      native.accepted (.inr event) ≠ none := by
    intro absent
    have failed : native.PublicFailure event := Or.inl
      ((native.publicView_missedBinding event who value shape).mpr ⟨finished, absent⟩)
    have excluded := coverage.covered event who
      (EventGraph.actor?_of_outputLayout_binding graph shape) failed
    rw [clear] at excluded
    exact Finset.notMem_empty _ excluded
  have meaning (completion : graph.Completion) (retained : completion ∈ native.config.history)
      (value : L.Ty) (shape : graph.outputLayout completion.event = .binding who value)
      (candidate : Handle graph)
      (accepted : native.accepted (.inr completion.event) = some candidate)
      (result : PublicationResult (L.Val value))
      (agrees : native.bindingResult candidate value = result) :
      decodeEventAction setup.program completion.event completion.action =
        decodeEventAction setup.program completion.event
          (cast (congrArg EventField.Action shape.symm) result) := by
    have action := valid.recorded_binding_action reachable completion.event who value shape
      completion.action retained
    rw [accepted, Option.elim_some, agrees] at action
    have original := congrArg (cast (congrArg EventField.Action shape.symm)) action
    simpa only [cast_cast, cast_eq] using congrArg
      (decodeEventAction setup.program completion.event) original
  have membership : ∀ pair, pair ∈ actual ↔ pair ∈ expected := by
    intro pair
    constructor
    · intro present
      obtain ⟨entry, retained, readAt⟩ := List.mem_filterMap.mp present
      obtain ⟨attempt, lower, upper, material, candidate, sent, named, parsed⟩ :=
        parsedBinding?_spec setup.program mode runtime leaks low selected.val generation entry pair
          readAt
      obtain ⟨earlier, later, recalled⟩ := List.mem_iff_append.mp retained
      obtain ⟨before, _prior, _prefix, _actor, _past, _viewed, beforeRequest, _legal⟩ :=
        PhaseCount.recorded_binding_request runtime leaks bounds plan ordered inputs horizon
          scheduler trace clear who earlier entry later recalled material sent pair.1 candidate
            named
      have actor := beforeRequest.2.2.2.1
      obtain ⟨value, shape⟩ := kind pair.1 lower upper actor
      have finished := done pair.1 upper actor
      obtain ⟨acceptedCandidate, accepted⟩ := Option.ne_none_iff_exists'.mp
        (receipt pair.1 value shape finished)
      obtain ⟨_oldEntry, _serial, _retained, _attempt, _declared, _handle, agrees, _decoded⟩ :=
        phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment block
          low generation slotWeight slotNonnegative slotBounded who word plan inputs
            horizon scheduler trace clear pair.1 value shape (by omega) address acceptedCandidate
              accepted consistent
      obtain ⟨_serial, _declared, _handle, forward⟩ := phaseCommitWordRecall_record setup mode
        runtime
        leaks bounds wellFormed assessment block low generation slotWeight slotNonnegative
          slotBounded who word plan inputs horizon scheduler trace clear earlier entry later
            recalled
            pair.1 value shape (by omega) attempt material sent candidate named consistent
      obtain ⟨action, recorded, _typed⟩ := valid.completed_binding_action reachable pair.1 who value
        shape finished
      let completion : graph.Completion := ⟨pair.1, action⟩
      have decodedAt := meaning completion recorded value shape acceptedCandidate accepted _ agrees
      refine List.mem_filterMap.mpr ⟨completion, ?_, ?_⟩
      · exact List.mem_filter.mpr ⟨List.mem_filter.mpr ⟨recorded, by
          simpa only [decide_eq_true_eq] using actor⟩, by
            simpa only [decide_eq_true_eq] using And.intro lower upper⟩
      · change (decodeEventAction setup.program pair.1 action).map (pair.1, ·) = some pair
        rw [decodedAt, ← forward, parsed]
        rfl
    · intro present
      obtain ⟨completion, completedAt, decodedAt⟩ := List.mem_filterMap.mp present
      obtain ⟨own, inside⟩ := List.mem_filter.mp completedAt
      obtain ⟨retained, actor⟩ := List.mem_filter.mp own
      have actor : graph.actor? completion.event = some who := of_decide_eq_true actor
      have inside : low ≤ completion.event.val ∧ completion.event.val < selected.val :=
        of_decide_eq_true inside
      obtain ⟨action, actionAt, equal⟩ := Option.map_eq_some_iff.mp decodedAt
      cases equal
      obtain ⟨value, shape⟩ := kind completion.event inside.1 inside.2 actor
      have finished := (native.config.history_exact completion.event).mp
        (List.mem_map.mpr ⟨completion, retained, rfl⟩)
      obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp
        (receipt completion.event value shape finished)
      obtain ⟨entry, serial, recalled, attempt, declared, _handle, agrees, parsed⟩ :=
        phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment block
          low generation slotWeight slotNonnegative slotBounded who word plan inputs
            horizon scheduler trace clear completion.event value shape (by omega) address candidate
              accepted consistent
      have decodedAction := meaning completion retained value shape candidate accepted _ agrees
      have parsedAction := parsed.trans (decodedAction.symm.trans actionAt)
      let material : WitnessedSubmission graph :=
        ⟨⟨.commitment completion.event (who, .prepared serial), match
          (phaseRecoveryBindingData setup mode completion.event who value shape
            (CommitRecoveryMove.lift
              (block.wordAction who (completion.event.val - low) word))).1 with
          | .failure => none
          | .success output => some ⟨value, output⟩⟩, .none⟩
      have sent : entry.action.transmission = some material := by rw [declared]; rfl
      refine List.mem_filterMap.mpr ⟨entry, recalled, ?_⟩
      change parsedBinding? setup.program mode runtime leaks low selected.val generation entry = _
      unfold parsedBinding?
      rw [ite_eq_left attempt, sent]
      change (if low ≤ completion.event.val ∧ completion.event.val < selected.val then
        (phaseBindingAction? setup.program mode runtime leaks entry.action).map
          (completion.event, ·) else none) = _
      rw [ite_eq_left inside, parsedAction]
      rfl
  have actualOrder : actual.Pairwise (fun first second => first.1.val < second.1.val) :=
    parsedBinding?_ordered setup.program mode runtime leaks bounds plan inputs horizon scheduler
      trace clear who low selected.val generation
  have expectedOrder : expected.Pairwise (fun first second => first.1.val < second.1.val) := by
    have sourceOrder := ordered.ownEventIds_pairwise reachable who
    have ownOrder : (graph.ownCompletions who native.config.history).Pairwise
        (fun first second => first.event.val < second.event.val) := by
      simpa only [ownEventIds, List.pairwise_map] using sourceOrder
    apply List.Pairwise.filterMap decoded ?_ (ownOrder.filter _)
    intro first second before firstPair firstAt secondPair secondAt
    obtain ⟨_action, _decoded, firstEq⟩ := Option.map_eq_some_iff.mp firstAt
    obtain ⟨_action, _decoded, secondEq⟩ := Option.map_eq_some_iff.mp secondAt
    cases firstEq
    cases secondEq
    exact before
  have equal : actual = expected := actualOrder.eq_of_mem_iff expectedOrder membership
  have values := congrArg (List.map Prod.snd) equal
  rw [parsedBinding?_word setup.program mode runtime leaks] at values
  exact values.trans (by
    simp only [expected, completed, decoded, List.map_filterMap, decodeCompletions,
      List.filterMap_map]
    apply congrArg (fun function => completed.filterMap function)
    funext completion
    change ((decodeEventAction setup.program completion.event completion.action).map
      (completion.event, ·)).map Prod.snd =
        decodeEventAction setup.program completion.event completion.action
    cases decodeEventAction setup.program completion.event completion.action <;> rfl)

end Vegas
