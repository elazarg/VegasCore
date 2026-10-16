/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCommitRecallHistory
import Vegas.Pending.PhaseBindingRecallOrder

/-! # Actual unsent binding recall conditions the original completed word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  {Γ Δ : SourceCtx Player L} {O P : Finset VarId}

/-- A complete word agrees with the owner's surviving earlier binding results.
The predicate reads actual accepted meanings, including failure; it does not
replace the original prior or introduce a latent execution process. -/
def phaseCommitWordAgrees (block : CommitPrefix Γ O Δ P) (low : Nat) (who : Player)
    (native : EventGraphRuntime.State (serviceGraph setup mode)) (high : Nat)
    (word : DecisionView who Δ) : Prop :=
  ∀ (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (candidate : Handle (serviceGraph setup mode)),
    low ≤ event.val ∧ event.val < high → native.accepted (.inr event) = some candidate →
      native.bindingResult candidate payload =
        (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1

variable (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (block : CommitPrefix Γ O Δ P) (low generation : Nat)
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
  (inside : low ≤ selected.val ∧ selected.val < low + block.length)
  (address : control.execution.application.attempt = ⟨low, generation⟩)

local notation "app" => phaseApplication runtime leaks
local notation "family" => phaseCommitWordPolicy setup mode runtime leaks bounds wellFormed
  assessment block low generation slotWeight slotNonnegative slotBounded who

include trace clear inside address in
private theorem agrees_of_consistent (word : DecisionView who Δ)
    (consistent : (family word).Consistent (control.execution.recall who)) :
    phaseCommitWordAgrees setup mode block low who control.execution.application.current.native
      selected.val word := by
  intro event value shape candidate interval accepted
  obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
    phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment block low
      generation slotWeight slotNonnegative slotBounded who word plan inputs horizon
        scheduler trace clear event value shape (by omega) address candidate accepted consistent
  exact meaning

include trace clear request address in
private theorem consistent_of_agrees
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
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have raw := menu.toRawTrace initial horizon scheduler trace
  have coverage := (phaseFailureCoverage_history runtime leaks plan inputs horizon scheduler
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
    obtain ⟨law, constant⟩ | ⟨event, value, shape, addressed, tag, channels⟩ :=
      phaseCommitWordPolicy_cases setup mode runtime leaks bounds wellFormed assessment block low
        generation slotWeight slotNonnegative slotBounded who earlier entry.beforeView
    · simpa only [constant] using sampled
    · by_cases silent : entry.action = ⟨none⟩
      · have atom : family original earlier entry.beforeView entry.action =
            family word earlier entry.beforeView entry.action := by
          rw [channels original, channels word, silent]
          unfold PhaseCount.phaseBindingWordPolicy
          split
          · exact PhaseCount.phaseBindingWordResponse_silence_congr runtime leaks bounds who event
              value _ _ slotWeight slotNonnegative slotBounded _ _ earlier entry.beforeView
          · rfl
        rw [PMF.mem_support_iff] at sampled ⊢
        rwa [← atom]
      · rw [channels original] at sampled
        unfold PhaseCount.phaseBindingWordPolicy at sampled
        split at sampled
        · rename_i guard
          obtain ⟨serial, declared⟩ := PhaseCount.phaseBindingWordResponse_nonsilent runtime leaks
            bounds who event value _ _ slotWeight slotNonnegative slotBounded _ earlier
              entry.beforeView entry.action sampled silent
          let result := (phaseRecoveryBindingData setup mode event who value shape
            (CommitRecoveryMove.lift (block.wordAction who (event.val - low) original))).1
          let material : WitnessedSubmission graph :=
            ⟨⟨.commitment event (who, .prepared serial), match result with
              | .failure => none
              | .success output => some ⟨value, output⟩⟩, .none⟩
          have sent : entry.action.transmission = some material := by rw [declared]; rfl
          have before : event.val < selected.val :=
            PhaseCount.recorded_binding_rank_lt_of_unsent_request runtime leaks bounds plan ordered
              inputs horizon scheduler trace clear who earlier entry later recalled material sent
                event (who, .prepared serial) rfl (tag.trans address.symm) selected request unsent
          have done : event ∈ native.config.cut.completed :=
            (ordered.ready_visible_iff native.config.cut request.2.2.1 request.2.2.2.1
              (EventCode.output_visible_of_actor (graph.nodes event) who
                (EventGraph.actor?_of_outputLayout_binding graph shape))
              (IndependentReveals.not_of_actor_eq (by
                rw [EventGraph.actor?_of_outputLayout_binding graph shape, request.2.2.2.1]))
              (IndependentReveals.not_of_actor_eq (by
                rw [EventGraph.actor?_of_outputLayout_binding graph shape, request.2.2.2.1]))).mpr
                  before
          have receipt : native.accepted (.inr event) ≠ none := by
            intro absent
            have failed : native.PublicFailure event := Or.inl
              ((native.publicView_missedBinding event who value shape).mpr ⟨done, absent⟩)
            have excluded := coverage.covered event who
              (EventGraph.actor?_of_outputLayout_binding graph shape) failed
            rw [clear] at excluded
            exact Finset.notMem_empty _ excluded
          obtain ⟨candidate, accepted⟩ := Option.ne_none_iff_exists'.mp receipt
          obtain ⟨_entry, _serial, _retained, _attempt, _declared, _handle, meaning, _decoded⟩ :=
            phaseCommitWordRecall_accepted setup mode runtime leaks bounds wellFormed assessment
              block low generation slotWeight slotNonnegative slotBounded who original plan
                inputs horizon scheduler trace clear event value shape addressed address candidate
                  accepted consistent
          have target := agrees event value shape candidate ⟨addressed.1, before⟩ accepted
          have equal := meaning.symm.trans target
          rw [channels word]
          unfold PhaseCount.phaseBindingWordPolicy
          rw [ite_eq_left guard]
          dsimp only at sampled ⊢
          rw [← equal]
          exact sampled
        · have impossible := (PMF.mem_support_pure_iff ..).mp sampled
          exact (silent impossible).elim
  have build : ∀ (past : List (app).PlayerEntry), past.IsPrefix (control.execution.recall who) →
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
/-- Before a genuine still-unsent owned callback, the concrete whole-word
implementation posterior is exactly its original prior conditioned by the
owner's surviving earlier typed binding results. Earlier WAITs, slot choices,
openings and dormant callbacks add no further word-dependent likelihood.
This identifies the private word law, not the auxiliary assessment posterior. -/
theorem phaseCommitWordPolicy_posterior_accepted_of_history
    (unsent : ∀ message ∈ (app).outputs (control.execution.recall who),
      PhaseCount.event? message.payload ≠ some ⟨control.execution.application.attempt, selected⟩)
    (prior : PMF (DecisionView who Δ))
    (consistent : ((app).policyMixture prior family).policy.Consistent
      (control.execution.recall who)) :
    ((app).policyMixture prior family).posterior (control.execution.recall who) =
      fiberPosterior prior (fun word => decide (phaseCommitWordAgrees setup mode block low who
        control.execution.application.current.native selected.val word)) true := by
  classical
  rw [phaseCommitWordPolicy_posterior_consistency_fiber setup mode runtime leaks bounds wellFormed
    assessment block low generation slotWeight slotNonnegative slotBounded who prior
      (control.execution.recall who) consistent]
  obtain ⟨original, possible⟩ := ((app).policyMixture prior family).posterior
    (control.execution.recall who) |>.support_nonempty
  have member := (app).policyMixture_member_consistent prior family (control.execution.recall who)
    consistent original possible
  apply fiberPosterior_eq_of_support_fiber
  intro word _supported
  simp only [decide_eq_true_eq]
  constructor
  · exact agrees_of_consistent setup mode runtime leaks bounds wellFormed assessment block low
      generation slotWeight slotNonnegative slotBounded who plan inputs horizon scheduler
        trace clear selected inside address word
  · exact consistent_of_agrees setup mode runtime leaks bounds wellFormed assessment block low
      generation slotWeight slotNonnegative slotBounded who plan inputs horizon scheduler
        trace clear selected request address unsent original word member

end Vegas
