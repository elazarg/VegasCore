/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitWordFilledView

/-! # Actual unsent recall conditions the original word on the filled source view

This is a fixed saved-entry private-word posterior identity. Original foreign
failures and repeated-owner dependence are retained in the chronological prior;
no external observation likelihood or auxiliary assessment Bayes is asserted.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The actual filled callback view has positive original source-prefix mass,
and the concrete implementation's entire own-recall posterior is precisely
its original complete-word law conditioned on that view. -/
theorem phaseCommitWordPolicy_posterior_filled_of_history
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
    (inside : low ≤ selected.val ∧ selected.val < low + (earlier.append later).length)
    (atEnd : selected.val = low + earlier.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall who), PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, selected⟩) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let prior := (before.bind (later.prefixLaw suffix current)).map (SourceProgram.Config.view who)
    let family := phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      (earlier.append later) low generation slotWeight slotNonnegative slotBounded who
    let filled := fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
      control.execution.application.current.native.config.store entry
    ((phaseApplication runtime leaks).policyMixture prior family).policy.Consistent
        (control.execution.recall who) →
      filled.view who ∈ (before.map (SourceProgram.Config.view who)).support ∧
        ((phaseApplication runtime leaks).policyMixture prior family).posterior
            (control.execution.recall who) =
          fiberPosterior prior (later.entryView who) (filled.view who) := by
  classical
  intro current before prior family filled consistent
  let app := phaseApplication runtime leaks
  let native := control.execution.application.current.native
  let accepts := fun word => decide (phaseCommitWordAgrees setup mode (earlier.append later) low
    who native selected.val word)
  obtain ⟨original, possible⟩ := (app.policyMixture prior family).posterior
    (control.execution.recall who) |>.support_nonempty
  have admitted := app.policyMixture_posterior_mem_initial prior family
    (control.execution.recall who) consistent original possible
  have member := app.policyMixture_member_consistent prior family (control.execution.recall who)
    consistent original possible
  have originalFill : later.entryView who original = filled.view who :=
    phaseCommitWord_sourceView_eq_fill_of_history setup mode runtime leaks bounds wellFormed
      assessment earlier later suffix profile entry embedding low generation rank actions
        slotWeight slotNonnegative slotBounded who plan inputs horizon scheduler trace clear
          selected request atEnd address original member admitted
  have projection : prior.map (later.entryView who) =
      before.map (SourceProgram.Config.view who) :=
    earlier.prefixLaw_split_entryView later suffix profile entry who
  have present : filled.view who ∈ (before.map (SourceProgram.Config.view who)).support := by
    rw [← originalFill, ← projection]
    exact (PMF.mem_support_map_iff ..).mpr ⟨original, admitted, rfl⟩
  have originalAgrees : phaseCommitWordAgrees setup mode (earlier.append later) low who native
      selected.val original := by
    intro event payload binding candidate interval accepted
    obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
      phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment
        (earlier.append later) low generation slotWeight slotNonnegative slotBounded who original
          plan inputs horizon scheduler trace clear event payload binding (by omega)
            address candidate accepted member
    exact meaning
  have positive : true ∈ (prior.map accepts).support := by
    apply (PMF.mem_support_map_iff ..).mpr
    exact ⟨original, admitted, by simp only [accepts, decide_eq_true_eq]; exact originalAgrees⟩
  have acceptedLaw := phaseCommitWordPolicy_posterior_accepted_of_history setup mode runtime leaks
    bounds wellFormed assessment (earlier.append later) low generation slotWeight slotNonnegative
      slotBounded who plan inputs horizon scheduler trace clear selected request inside
        address unsent prior consistent
  refine ⟨present, acceptedLaw.trans ?_⟩
  apply fiberPosterior_eq_of_support_fiber
  intro word supported
  simp only [decide_eq_true_eq]
  constructor
  · intro agrees
    have retained : word ∈ ((app.policyMixture prior family).posterior
        (control.execution.recall who)).support := by
      rw [acceptedLaw]
      change word ∈ (fiberPosterior prior accepts true).support
      rw [fiberPosterior_support prior accepts true positive]
      exact ⟨by simpa only [accepts, Set.mem_ofPred_eq, decide_eq_true_eq] using agrees,
        supported⟩
    have compatible := app.policyMixture_member_consistent prior family
      (control.execution.recall who) consistent word retained
    exact phaseCommitWord_sourceView_eq_fill_of_history setup mode runtime leaks bounds wellFormed
      assessment earlier later suffix profile entry embedding low generation rank actions
        slotWeight slotNonnegative slotBounded who plan inputs horizon scheduler trace clear
          selected request atEnd address word compatible supported
  · intro sameView event payload binding candidate interval accepted
    have meaning := originalAgrees event payload binding candidate interval accepted
    have bounded : event.val - low < earlier.length := by omega
    rw [CommitPrefix.wordAction_append_prefix earlier later who (event.val - low) original bounded,
      originalFill] at meaning
    rw [CommitPrefix.wordAction_append_prefix earlier later who (event.val - low) word bounded,
      sameView]
    exact meaning

/-- After the actual full recall, the next owned action read from the original
complete source word has exactly the nonmissing chronological source kernel
at the actual filled view. Fresh physical omission draws remain separate. -/
theorem phaseCommitWordPolicy_next_action_of_history
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
    (runtime : EventGraphRuntime (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : CommitPrefix Γ O Δ P)
    (later : CommitPrefix ((name, .commitment owner payload) :: Δ) (insert name P) Ξ Q)
    (suffix : SourceProgram Player L Ξ Q)
    (profile : SourceProgram.BehavioralProfile
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (entry : SourceProgram.Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (earlier.prepend (.commit name owner fresh guard (later.prepend suffix))))
    (low generation : Nat)
    (rank : ∀ index, (embedding.event index).val = low + index.val)
    (actions : ∀ index action, decodeEventAction setup.program (embedding.event index) action =
      decodeEventAction (earlier.prepend (.commit name owner fresh guard (later.prepend suffix)))
        index
        (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (inside : low ≤ selected.val ∧ selected.val <
      low + (earlier.append (.commit name owner fresh guard later)).length)
    (atEnd : selected.val = low + earlier.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall owner), PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, selected⟩) :
    let rest := CommitPrefix.commit name owner fresh guard later
    let current := earlier.tailProfile (rest.prepend suffix) profile
    let before := earlier.prefixLaw (rest.prepend suffix) profile entry
    let prior := (before.bind (rest.prefixLaw suffix current)).map (SourceProgram.Config.view owner)
    let family := phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed assessment
      (earlier.append rest) low generation slotWeight slotNonnegative slotBounded owner
    let filled := fillCommitPrefix setup.program earlier (rest.prepend suffix) embedding
      control.execution.application.current.native.config.store entry
    ((phaseApplication runtime leaks).policyMixture prior family).policy.Consistent
        (control.execution.recall owner) →
      (((phaseApplication runtime leaks).policyMixture prior family).posterior
          (control.execution.recall owner)).map
            ((earlier.append rest).wordAction owner earlier.length) =
        (commitKernel current (filled.view owner)).map
          (fun result => some (OwnAction.commit owner name payload result)) := by
  intro rest current before prior family filled consistent
  obtain ⟨present, posterior⟩ := phaseCommitWordPolicy_posterior_filled_of_history setup mode
    runtime leaks bounds wellFormed assessment earlier rest suffix profile entry embedding low
      generation rank actions slotWeight slotNonnegative slotBounded owner plan inputs
        horizon scheduler trace clear selected request inside atEnd address unsent consistent
  rw [posterior]
  have prediction := earlier.prefixLaw_owned_word_conditional fresh guard later suffix profile
    entry (filled.view owner) present
  simpa only [rest, current, filled, CommitPrefix.entryView, CommitPrefix.prepend, decide_true]
    using prediction

end Vegas
