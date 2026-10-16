/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlanPosterior

/-! # Accepted source-word meaning under the actual varying finite timing plan -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))
  (runtimePlan : RuntimePhasePlan (serviceGraph setup mode))
  (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)
  (bound : (serviceGraph setup mode).EventId → Nat)

local notation "app" => phaseApplication runtime leaks
local notation "menu" => PhaseCount.onePacketMenu runtime leaks bounds
local notation "initial" => inputs.map (PhaseRuntimeState.initial runtimePlan)
variable [Fintype ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).History]
  [∀ who, DecidableEq (((PhaseCount.onePacketMenu runtime leaks bounds).information
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).InfoState who)]

local notation "N" => ReactiveApplication.ResponseMenu.information (menu) initial horizon scheduler
local notation "Agent" => InformationModel.InformationAgent (N)
  (InformationModel.playedInformation (N))
local notation "isFree" => fun agent : Agent => PhasePublicExclusion setup mode runtime leaks
  (Subtype.val (Sigma.snd agent))
local notation "isKeyed" => fun agent : Agent => PhaseUnprotected runtime leaks bound
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "poolKey" => fun agent : Agent => phaseTimingKey runtime leaks
  (Sigma.fst agent) (Subtype.val (Sigma.snd agent))
local notation "Pool" => FreeKeyedPool isFree isKeyed poolKey
local notation "Parts" => PhaseTimingPart setup mode runtime leaks bounds initial horizon
  scheduler bound

/-- For one ORIGINAL complete timing plan and saved source entry, the full
actual NON-RAW recall conditions the ONE chronological word on its actual
filled source view. Operational keys may choose different options. Neither
future omissions nor canonical failed bindings are discarded. -/
theorem phaseTimingWordPlanPolicy_posterior_filled_of_history
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    (earlier : SourceProgram.CommitPrefix Γ O Δ P) (later : SourceProgram.CommitPrefix Δ P Ξ Q)
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
    (timingPlan : (p : Pool) → Parts p) (who : Player)
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, selected⟩)
    (inside : low ≤ selected.val ∧ selected.val < low + (earlier.append later).length)
    (atEnd : selected.val = low + earlier.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩) :
    let current := earlier.tailProfile (later.prepend suffix) profile
    let before := earlier.prefixLaw (later.prepend suffix) profile entry
    let prior := (before.bind (later.prefixLaw suffix current)).map (SourceProgram.Config.view who)
    let family := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source (earlier.append later) low generation slotWeight
        slotNonnegative slotBounded timingPlan who
    let filled := fillCommitPrefix setup.program earlier (later.prepend suffix) embedding
      control.execution.application.current.native.config.store entry
    ((app).policyMixture prior family).policy.Consistent (control.execution.recall who) →
      filled.view who ∈ (before.map (SourceProgram.Config.view who)).support ∧
        ((app).policyMixture prior family).posterior (control.execution.recall who) =
          fiberPosterior prior (later.entryView who) (filled.view who) := by
  classical
  intro current before prior family filled consistent
  let native := control.execution.application.current.native
  obtain ⟨original, possible⟩ := ((app).policyMixture prior family).posterior
    (control.execution.recall who) |>.support_nonempty
  have admitted := (app).policyMixture_posterior_mem_initial prior family
    (control.execution.recall who) consistent original possible
  have member := (app).policyMixture_member_consistent prior family
    (control.execution.recall who) consistent original possible
  have originalAgrees : phaseCommitWordAgrees setup mode (earlier.append later) low who native
      selected.val original := by
    intro event payload binding candidate interval accepted
    obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
      phaseTimingWordPlanRecall_accepted setup mode runtime leaks bounds runtimePlan inputs horizon
        scheduler bound fallback wellFormed source (earlier.append later) low generation slotWeight
          slotNonnegative slotBounded timingPlan who original trace clear event payload
            binding (by omega) address candidate accepted member
    exact meaning
  have originalFill : later.entryView who original = filled.view who :=
    phaseCommitWord_sourceView_eq_fill_of_accepted setup mode runtime leaks bounds earlier later
      suffix profile entry embedding low rank actions who runtimePlan inputs horizon scheduler
        trace clear selected request atEnd original originalAgrees admitted
  have projection : prior.map (later.entryView who) =
      before.map (SourceProgram.Config.view who) :=
    earlier.prefixLaw_split_entryView later suffix profile entry who
  have present : filled.view who ∈ (before.map (SourceProgram.Config.view who)).support := by
    rw [← originalFill, ← projection]
    exact (PMF.mem_support_map_iff ..).mpr ⟨original, admitted, rfl⟩
  have acceptedLaw := phaseTimingWordPlanPolicy_posterior_accepted_of_history setup mode runtime
    leaks bounds runtimePlan inputs horizon scheduler bound fallback wellFormed source
      (earlier.append later) low generation slotWeight slotNonnegative slotBounded timingPlan who
        trace clear selected request inside address unsent prior consistent
  refine ⟨present, acceptedLaw.trans ?_⟩
  apply fiberPosterior_eq_of_support_fiber
  intro word supported
  simp only [decide_eq_true_eq]
  constructor
  · intro agrees
    exact phaseCommitWord_sourceView_eq_fill_of_accepted setup mode runtime leaks bounds earlier
      later suffix profile entry embedding low rank actions who runtimePlan inputs horizon scheduler
        trace clear selected request atEnd word agrees supported
  · intro sameView event payload binding candidate interval accepted
    have meaning := originalAgrees event payload binding candidate interval accepted
    have bounded : event.val - low < earlier.length := by omega
    rw [SourceProgram.CommitPrefix.wordAction_append_prefix earlier later who
      (event.val - low) original bounded,
      originalFill] at meaning
    rw [SourceProgram.CommitPrefix.wordAction_append_prefix earlier later who
      (event.val - low) word bounded,
      sameView]
    exact meaning


/-- At an actual unsent callback, the next result read from the one ORIGINAL
source word after the entire varying-plan recall is the chronological
nonmissing source kernel at the actual filled view. Timing WAIT and the
original omission draw remain separate physical factors. -/
theorem phaseTimingWordPlanPolicy_next_action_of_history
    (fallback : (who : Player) → (N).Policy who) (wellFormed : setup.WellFormed)
    (source : setup.commitRecoveryModel.BehavioralAssessment)
    {Γ Δ Ξ : SourceCtx Player L} {O P Q : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Δ.map Prod.fst) (guard : SourceGuard L Δ owner name payload)
    (earlier : SourceProgram.CommitPrefix Γ O Δ P)
    (later : SourceProgram.CommitPrefix ((name, .commitment owner payload) :: Δ)
      (insert name P) Ξ Q)
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
        index (cast (congrArg EventField.Action (embedding.layout_eq index)) action))
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (timingPlan : (p : Pool) → Parts p)
    {control : (app).Control}
    (trace : ((menu).protocol initial horizon scheduler).Trace (some control))
    (clear : control.execution.application.current.excluded = ∅)
    (selected : (serviceGraph setup mode).EventId)
    (request : control.execution.application.SeedRequest owner
      ⟨control.execution.application.attempt, selected⟩)
    (inside : low ≤ selected.val ∧ selected.val <
      low + (earlier.append (.commit name owner fresh guard later)).length)
    (atEnd : selected.val = low + earlier.length)
    (address : control.execution.application.attempt = ⟨low, generation⟩)
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall owner),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩) :
    let rest := SourceProgram.CommitPrefix.commit name owner fresh guard later
    let current := earlier.tailProfile (rest.prepend suffix) profile
    let before := earlier.prefixLaw (rest.prepend suffix) profile entry
    let prior := (before.bind (rest.prefixLaw suffix current)).map (SourceProgram.Config.view owner)
    let family := phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial horizon
      scheduler bound fallback wellFormed source (earlier.append rest) low generation slotWeight
        slotNonnegative slotBounded timingPlan owner
    let filled := fillCommitPrefix setup.program earlier (rest.prepend suffix) embedding
      control.execution.application.current.native.config.store entry
    ((app).policyMixture prior family).policy.Consistent (control.execution.recall owner) →
      (((app).policyMixture prior family).posterior (control.execution.recall owner)).map
          ((earlier.append rest).wordAction owner earlier.length) =
        (commitKernel current (filled.view owner)).map
          (fun result => some (OwnAction.commit owner name payload result)) := by
  intro rest current before prior family filled consistent
  obtain ⟨present, posterior⟩ := phaseTimingWordPlanPolicy_posterior_filled_of_history setup mode
    runtime leaks bounds runtimePlan inputs horizon scheduler bound fallback wellFormed source
      earlier rest suffix profile entry embedding low generation rank actions slotWeight
        slotNonnegative slotBounded timingPlan owner trace clear selected request inside
          atEnd address unsent consistent
  rw [posterior]
  have prediction := earlier.prefixLaw_owned_word_conditional fresh guard later suffix profile
    entry (filled.view owner) present
  simpa only [rest, current, filled, SourceProgram.CommitPrefix.entryView,
    SourceProgram.CommitPrefix.prepend, decide_true]
    using prediction

end Vegas
