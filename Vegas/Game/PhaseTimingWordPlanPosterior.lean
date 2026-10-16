/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordPlan
import Vegas.Game.PhaseTimingWordPlanChannels
import Vegas.Game.PhaseCommitWordFilledView

/-! # Accepted source-word meaning under the actual varying finite timing plan -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Protocol.InformationModel
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

variable {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
  (fallback : (who : Player) →
    ((PhaseCount.onePacketMenu runtime leaks bounds).information
      (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).Policy who)
  (wellFormed : setup.WellFormed)
  (source : setup.commitRecoveryModel.BehavioralAssessment)
  (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (timingPlan : (p : FreeKeyedPool
    (fun agent : InformationModel.InformationAgent
        ((PhaseCount.onePacketMenu runtime leaks bounds).information
          (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler)
        (InformationModel.playedInformation
          ((PhaseCount.onePacketMenu runtime leaks bounds).information
            (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler)) =>
      PhasePublicExclusion setup mode runtime leaks (Subtype.val (Sigma.snd agent)))
    (fun agent => PhaseUnprotected runtime leaks bound (Sigma.fst agent)
      (Subtype.val (Sigma.snd agent)))
    (fun agent => phaseTimingKey runtime leaks (Sigma.fst agent)
      (Subtype.val (Sigma.snd agent)))) →
    PhaseTimingPart setup mode runtime leaks bounds
      (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler bound p) (who : Player)

local notation "family" => phaseTimingWordPlanPolicy setup mode runtime leaks bounds initial
  horizon scheduler bound fallback wellFormed source block low generation slotWeight
    slotNonnegative slotBounded timingPlan who

variable
  {control : (phaseApplication runtime leaks).Control}
  (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
    (inputs.map (PhaseRuntimeState.initial runtimePlan)) horizon scheduler).Trace (some control))
  (clear : control.execution.application.current.excluded = ∅)
  (selected : (serviceGraph setup mode).EventId)
  (request : control.execution.application.SeedRequest who
    ⟨control.execution.application.attempt, selected⟩)
  (inside : low ≤ selected.val ∧ selected.val < low + block.length)
  (address : control.execution.application.attempt = ⟨low, generation⟩)

include trace clear inside address in
private theorem plan_agrees_of_consistent (word : DecisionView who Δ)
    (consistent : (family word).Consistent (control.execution.recall who)) :
    phaseCommitWordAgrees setup mode block low who control.execution.application.current.native
      selected.val word := by
  intro event payload binding candidate interval accepted
  obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
    phaseTimingWordPlanRecall_accepted setup mode runtime leaks bounds runtimePlan inputs horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded timingPlan who word trace clear event payload binding (by omega)
          address candidate accepted consistent
  exact meaning

include trace clear request address in
private theorem plan_consistent_of_agrees
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (original word : DecisionView who Δ)
    (consistent : (family original).Consistent (control.execution.recall who))
    (agrees : phaseCommitWordAgrees setup mode block low who
      control.execution.application.current.native selected.val word) :
    (family word).Consistent (control.execution.recall who) := by
  classical
  let graph := serviceGraph setup mode
  let native := control.execution.application.current.native
  have raw := (menu).toRawTrace initial horizon scheduler trace
  have coverage := (phaseFailureCoverage_history runtime leaks runtimePlan inputs horizon scheduler
    raw).active
  let ordered := serviceGraph_revealRelaxedOrdered setup mode
  have record : ∀ (earlier : List (app).PlayerEntry) (entry : (app).PlayerEntry)
      (later : List (app).PlayerEntry),
      control.execution.recall who = earlier ++ entry :: later →
        entry.action ∈ (family word earlier entry.beforeView).support := by
    intro earlier entry later recalled
    have faithful := recalled ▸ consistent
    have atRecord : (family original).Consistent (earlier ++ [entry]) :=
      ReactiveApplication.Policy.Consistent.of_append (by
        simpa only [List.append_assoc, List.singleton_append] using faithful)
    have sampled := ((family original).consistent_snoc_iff earlier entry).mp atRecord |>.2
    obtain ⟨law, constant⟩ | ⟨event, payload, binding, addressed, tag, kernel, silentMass,
      nonsilentShape, channels⟩ := phaseTimingWordPlanPolicy_channels setup mode runtime leaks
        bounds runtimePlan inputs horizon scheduler bound fallback wellFormed source block low
          generation slotWeight slotNonnegative slotBounded timingPlan who earlier entry.beforeView
    · simpa only [constant] using sampled
    · by_cases silent : entry.action = ⟨none⟩
      · have atom : family original earlier entry.beforeView entry.action =
            family word earlier entry.beforeView entry.action := by
          rw [channels original, channels word, silent]
          exact silentMass _ _
        rw [PMF.mem_support_iff] at sampled ⊢
        rwa [← atom]
      · rw [channels original] at sampled
        obtain ⟨serial, declared⟩ := nonsilentShape _ entry.action sampled silent
        let result := (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift (block.wordAction who (event.val - low) original))).1
        let material : WitnessedSubmission graph :=
          ⟨⟨.commitment event (who, .prepared serial), match result with
            | .failure => none
            | .success value => some ⟨payload, value⟩⟩, .none⟩
        have sent : entry.action.transmission = some material := by rw [declared]; rfl
        have before : event.val < selected.val :=
          PhaseCount.recorded_binding_rank_lt_of_unsent_request runtime leaks bounds runtimePlan
            ordered inputs horizon scheduler trace clear who earlier entry later recalled material
              sent event (who, .prepared serial) rfl (tag.trans address.symm) selected request
                unsent
        have done : event ∈ native.config.cut.completed :=
          (ordered.ready_visible_iff native.config.cut request.2.2.1 request.2.2.2.1
            (EventCode.output_visible_of_actor (graph.nodes event) who
              (EventGraph.actor?_of_outputLayout_binding graph binding))
            (IndependentReveals.not_of_actor_eq (by
              rw [EventGraph.actor?_of_outputLayout_binding graph binding, request.2.2.2.1]))
            (IndependentReveals.not_of_actor_eq (by
              rw [EventGraph.actor?_of_outputLayout_binding graph binding, request.2.2.2.1]))).mpr
                before
        have receipt : native.accepted (.inr event) ≠ none := by
          intro absent
          have failed : native.PublicFailure event := Or.inl
            ((native.publicView_missedBinding event who payload binding).mpr ⟨done, absent⟩)
          have excluded := coverage.covered event who
            (EventGraph.actor?_of_outputLayout_binding graph binding) failed
          rw [clear] at excluded
          exact Finset.notMem_empty _ excluded
        obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp receipt
        obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
          phaseTimingWordPlanRecall_accepted setup mode runtime leaks bounds runtimePlan inputs
            horizon scheduler bound fallback wellFormed source block low generation slotWeight
              slotNonnegative slotBounded timingPlan who original trace clear event payload
                binding addressed address candidate accepted consistent
        have target := agrees event payload binding candidate ⟨addressed.1, before⟩ accepted
        have equal := meaning.symm.trans target
        rw [channels word, ← equal]
        exact sampled
  have build : ∀ past : List (app).PlayerEntry, past.IsPrefix (control.execution.recall who) →
      (family word).Consistent past := by
    intro past
    induction past using List.reverseRecOn with
    | nil => intro _prefix; exact .nil
    | append_singleton earlier entry ih =>
      intro isPrefix
      have priorPrefix := (List.prefix_append earlier [entry]).trans isPrefix
      obtain ⟨later, same⟩ := isPrefix
      have recalled : control.execution.recall who = earlier ++ entry :: later := by
        simpa only [List.append_assoc, List.singleton_append] using same.symm
      exact .snoc entry (ih priorPrefix) (record earlier entry later recalled)
  exact build _ (List.prefix_refl _)

include trace clear request inside address in
open Classical in
/-- With the ORIGINAL entire timing plan fixed, actual full recall at an
unsent callback conditions its ONE original source word only by surviving
earlier accepted results. Each key may select a different WAIT or serial.
RAW draws are excluded from this exact non-RAW consistency statement. -/
theorem phaseTimingWordPlanPolicy_posterior_accepted_of_history
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (prior : PMF (DecisionView who Δ))
    (consistent : ((app).policyMixture prior family).policy.Consistent
      (control.execution.recall who)) :
    ((app).policyMixture prior family).posterior (control.execution.recall who) =
      fiberPosterior prior (fun word => decide (phaseCommitWordAgrees setup mode block low who
        control.execution.application.current.native selected.val word)) true := by
  classical
  rw [phaseTimingWordPlanPolicy_posterior_consistency_fiber setup mode runtime leaks bounds
    initial horizon scheduler bound fallback wellFormed source block low generation slotWeight
      slotNonnegative slotBounded timingPlan who prior (control.execution.recall who) consistent]
  obtain ⟨original, possible⟩ := ((app).policyMixture prior family).posterior
    (control.execution.recall who) |>.support_nonempty
  have member := (app).policyMixture_member_consistent prior family (control.execution.recall who)
    consistent original possible
  apply fiberPosterior_eq_of_support_fiber
  intro word _supported
  simp only [decide_eq_true_eq]
  constructor
  · exact plan_agrees_of_consistent setup mode runtime leaks bounds runtimePlan inputs horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded timingPlan who trace clear selected inside address word
  · exact plan_consistent_of_agrees setup mode runtime leaks bounds runtimePlan inputs horizon
      scheduler bound fallback wellFormed source block low generation slotWeight slotNonnegative
        slotBounded timingPlan who trace clear selected request address unsent original word
          member

end Vegas
