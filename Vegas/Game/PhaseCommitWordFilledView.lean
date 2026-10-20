/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitWordSourceView
import Vegas.Source.CommitPrefixWordHistory

/-! # The conditioned original source view is the actual filled callback view -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Concrete accepted-result agreement at an actual ready callback identifies
its exact filled source view. Foreign holes retain their legal latent failed
values; neither a positive fill mass nor source intendedness is required. -/
theorem phaseCommitWord_sourceView_eq_fill_of_accepted
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode))
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : SourceProgram.BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : SourceProgram.Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (earlier.prepend (later.prepend suffix))) (low : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (earlier.prepend (later.prepend suffix)) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (who : Player)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (selected : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (atEnd : selected.val = low + earlier.length)
    (word : DecisionView who Ξ)
    (agrees : phaseCommitWordAgrees setup mode (earlier.append later) low who
      control.execution.application.current.native selected.val word) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let prior := (before.bind (later.prefixLaw suffix current)).map (SourceProgram.Config.view who)
    word ∈ prior.support →
      later.entryView who word =
        (fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
          control.execution.application.current.native.config.store entry).view who := by
  intro current before prior supported
  obtain ⟨final, sampled, finalView⟩ := (PMF.mem_support_map_iff ..).mp supported
  obtain ⟨point, pointSupported, tailSupported⟩ := (PMF.mem_support_bind_iff ..).mp sampled
  obtain ⟨pointAttempt⟩ := earlier.prefixLaw_attempt (later.prepend suffix) profile entry point
    pointSupported
  obtain ⟨tailAttempt⟩ := later.prefixLaw_attempt suffix current point final tailSupported
  have projected : later.entryView who word = point.view who := by
    rw [← finalView]
    exact CommitPrefix.Attempt.entryView_eq later point final tailAttempt who
  let graph := serviceGraph setup mode
  let native := control.execution.application.current.native
  let filled := fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
    native.config.store entry
  let raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler trace
  have valid := (phaseBindingRecord_history runtime leaks plan inputs horizon scheduler raw).active
  have coverage := (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
    raw).active
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  have sameActions : ∀ position < earlier.length,
      earlier.wordAction who position (point.view who) =
        earlier.wordAction who position (filled.view who) := by
    intro position beforeSelected
    let index : Fin (eventCount (earlier.prepend (later.prepend suffix))) :=
      ⟨position, by have count := earlier.eventCount_prepend (later.prepend suffix); omega⟩
    by_cases owned : eventOwner? (earlier.prepend (later.prepend suffix)) index = some who
    · obtain ⟨owner, payload, _ownerMember, layout⟩ := earlier.binding_before_length
        (later.prepend suffix) index beforeSelected
      have sameOwner : owner = who := by
        have actor := EventGraph.actor?_of_outputLayout_binding
          (toEventGraph (earlier.prepend (later.prepend suffix))) layout
        rw [eventOwner?_eq_actor, actor] at owned
        exact Option.some.inj owned
      subst owner
      have binding : graph.outputLayout (embedding.event index) = .binding who payload :=
        (embedding.layout_eq index).trans layout
      have actor : graph.actor? (embedding.event index) = some who :=
        EventGraph.actor?_of_outputLayout_binding graph binding
      have below : (embedding.event index).val < selected.val := by
        rw [rank]
        dsimp only [index]
        omega
      have done : embedding.event index ∈ native.config.cut.completed :=
        (ordered.ready_visible_iff native.config.cut request.2.2.1 request.2.2.2.1
          (EventCode.output_visible_of_actor (graph.nodes (embedding.event index)) who actor)
          (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))
          (IndependentReveals.not_of_actor_eq (by rw [actor, request.2.2.2.1]))).mpr below
      have present : native.accepted (.inr (embedding.event index)) ≠ none := by
        intro absent
        have failed : native.PublicFailure (embedding.event index) := Or.inl
          ((native.publicView_missedBinding (embedding.event index) who payload binding).mpr
            ⟨done, absent⟩)
        have excluded := coverage.covered (embedding.event index) who actor failed
        exact request.2.2.2.2 excluded
      obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp present
      have meaning := agrees (embedding.event index) payload binding candidate
        ⟨by rw [rank]; omega, below⟩ accepted
      have offset : (embedding.event index).val - low = index.val := by rw [rank]; omega
      rw [offset, CommitPrefix.wordAction_append_prefix earlier later who index.val word
        beforeSelected, projected] at meaning
      let field : FieldRef (graphLayout setup.program) (.binding who payload) :=
        ⟨.inr (embedding.event index), binding⟩
      have available : (field.get? native.config.store).isSome = true := by
        apply field.get?_isSome
        change (native.config.store (.inr (embedding.event index))).isSome = true
        rw [EventGraph.Config.store_output, native.config.output_available]
        exact done
      obtain ⟨result, stored⟩ := Option.isSome_iff_exists.mp available
      have storedMeaning := valid.binding_value field result stored
      change result = (native.accepted (.inr (embedding.event index))).elim .failure
        (fun candidate => native.bindingResult candidate payload) at storedMeaning
      rw [accepted] at storedMeaning
      have readResult : (field.get? native.config.store).getD .failure =
          (phaseRecoveryBindingData setup mode (embedding.event index) who payload binding
            (CommitRecoveryMove.lift (earlier.wordAction who index.val (point.view who)))).1 := by
        rw [stored, Option.getD_some]
        exact storedMeaning.trans meaning
      have filledRead := fillCommitPrefix_wordAction setup.program earlier (later.prepend suffix)
        embedding actions native.config.store entry who index beforeSelected payload binding
      change earlier.wordAction who index.val (point.view who) =
        earlier.wordAction who index.val (filled.view who)
      rw [filledRead, readResult]
      exact (phaseCommitWordAction_decode setup mode earlier (later.prepend suffix) embedding
        actions who index beforeSelected payload binding (point.view who)).symm
    · rw [compiledCommitPrefix_wordAction_none_of_unowned earlier (later.prepend suffix) who
        index owned (point.view who), compiledCommitPrefix_wordAction_none_of_unowned earlier
          (later.prepend suffix) who index owned (filled.view who)]
  have filledAttempt := fillCommitPrefix_attempt setup.program earlier (later.prepend suffix)
    embedding native.config.store entry
  have leftWord := CommitPrefix.Attempt.wordAction_history earlier entry who point pointAttempt
  have rightWord := CommitPrefix.Attempt.wordAction_history earlier entry who filled filledAttempt
  have sameHistory : point.history who = filled.history who := by
    rw [leftWord, rightWord]
    apply congrArg (entry.history who ++ ·)
    apply List.filterMap_congr
    intro position beforeSelected
    exact sameActions position (List.mem_range.mp beforeSelected)
  rw [projected]
  exact CommitPrefix.Attempt.view_eq_of_history_eq earlier entry entry who rfl point filled
    pointAttempt filledAttempt sameHistory

/-- Every genuinely supported canonical member compatible with the full actual
recall reads the actual filled view. Accepted agreement is derived from the
real earlier callbacks, rather than supplied to this concrete endpoint. -/
theorem phaseCommitWord_sourceView_eq_fill_of_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : CommitPrefix Γ O Δ P) (later : CommitPrefix Δ P Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : SourceProgram.BehavioralProfile (earlier.prepend (later.prepend suffix)))
    (entry : SourceProgram.Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (earlier.prepend (later.prepend suffix))) (low generation : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (earlier.prepend (later.prepend suffix)) index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (who : Player)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (atEnd : selected.val = low + earlier.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (word : DecisionView who Ξ)
    (consistent : (phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      (earlier.append later) low generation slotWeight slotNonnegative slotBounded who
        word).Consistent (control.execution.recall who)) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let prior := (before.bind (later.prefixLaw suffix current)).map (SourceProgram.Config.view who)
    word ∈ prior.support →
      later.entryView who word =
        (fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
          control.execution.application.current.native.config.store entry).view who := by
  intro current before prior supported
  have agrees : phaseCommitWordAgrees setup mode (earlier.append later) low who
      control.execution.application.current.native selected.val word := by
    intro event payload binding candidate interval accepted
    obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
      phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment
        (earlier.append later) low generation slotWeight slotNonnegative slotBounded who word
          plan inputs horizon scheduler trace clear event payload binding
            (by rw [CommitPrefix.length_append]; omega) address candidate accepted consistent
    exact meaning
  exact phaseCommitWord_sourceView_eq_fill_of_accepted setup mode runtime leaks bounds earlier
    later suffix profile entry embedding low rank actions who plan inputs horizon scheduler trace
      selected request atEnd word agrees supported

end Vegas
