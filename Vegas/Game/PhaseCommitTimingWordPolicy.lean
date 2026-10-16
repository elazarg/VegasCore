/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseTimingWordResponse
import Vegas.Game.PhaseCommitWordPolicy

/-! # Globally legal timing members carrying one original commitment word -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

open Classical in
private def timingWordBinding {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ)
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  if same : owner = who then
    if low ≤ event.val ∧ event.val < low + block.length ∧
        view.application.2.attempt = ⟨low, generation⟩ then
      phaseBindingTimingWordResponse setup mode runtime leaks bounds owner event payload
        ((assessment.strategy owner (setup.commitRecoveryClearInformation wellFormed owner
          (phaseSourceView? setup mode runtime leaks owner event view))).map
            (fun choice => CommitRecoveryMove.missed choice.1)) option slotWeight
        slotNonnegative slotBounded
        (phaseRecoveryBindingData setup mode event owner payload binding
          (CommitRecoveryMove.lift (block.wordAction owner (event.val - low)
            (cast (congrArg (fun owner => DecisionView owner Δ) same.symm) word)))).1 past view
    else mix slotWeight slotNonnegative slotBounded
      (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment owner
        event payload binding past view)
      (phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed assessment owner
        event payload binding option past view)
  else PMF.pure ⟨none⟩

private theorem timingWordBinding_covered {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ)
    (owner : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (timingWordBinding setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who word owner event
        payload binding past view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds owner past view := by
  classical
  unfold timingWordBinding at supported
  split at supported
  · split at supported
    · exact phaseBindingTimingWordResponse_covered setup mode runtime leaks bounds owner event
        payload _ option slotWeight slotNonnegative slotBounded _ past view response supported
    · rcases support_mix_subset _ _ _ _ _ supported with slots | selected
      · exact phaseRecoverySlotPolicy_covered setup mode runtime leaks bounds wellFormed assessment
          owner event payload binding past view response slots
      · exact phaseRecoveryTimingPolicy_covered setup mode runtime leaks bounds wellFormed
          assessment
          owner event payload binding option past view response selected
  · cases (PMF.mem_support_pure_iff ..).mp supported
    exact PhaseCount.silence_onePacket runtime leaks bounds owner past view

open Classical in
/-- A timing member keeps one complete original word across the addressed
block. Main WAIT is silent at every event; the independent slot tier still
uses its original canonical opening. Other blocks use the original timing
recipe, independently of the latent word. -/
def phaseCommitTimingWordPolicy {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  mix slotWeight slotNonnegative slotBounded
    (phasePolicyDispatch setup mode runtime leaks (fun owner event payload binding =>
        PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
        PMF.pure true))
      (timingWordBinding setup mode runtime leaks bounds wellFormed assessment block low generation
        1 (by norm_num) le_rfl none who word) who past view)
    (match option with
    | none => PMF.pure ⟨none⟩
    | some serial => phasePolicyDispatch setup mode runtime leaks (fun owner event payload binding
        => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _
        => PMF.pure true))
        (timingWordBinding setup mode runtime leaks bounds wellFormed assessment block low
          generation 0 le_rfl (by norm_num) (some serial) who word) who past view)

/-- The complete timing member respects the actual counted finite menu at
all inputs, including dormant branches and an unavailable selected serial. -/
theorem phaseCommitTimingWordPolicy_covered {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed
      assessment block low generation slotWeight slotNonnegative slotBounded option who word past
        view).support) :
    response ∈ PhaseCount.onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseCommitTimingWordPolicy at supported
  rcases support_mix_subset _ _ _ _ _ supported with slots | selected
  · exact phasePolicyDispatch_covered (opened := (fun owner event payload binding past view
      response supported => PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner event
      payload binding (fun _ _ => PMF.pure true) past view response supported)) setup mode runtime
      leaks bounds (fun owner event payload binding => PhaseCount.phaseOpeningPolicy runtime leaks
      bounds owner event payload binding (fun _ _ => PMF.pure true)) _
      (timingWordBinding_covered setup mode runtime leaks bounds wellFormed assessment
      block low generation 1 (by norm_num) le_rfl none who word) who past view response slots
  · cases option with
    | none =>
        cases (PMF.mem_support_pure_iff ..).mp selected
        exact PhaseCount.silence_onePacket runtime leaks bounds who past view
    | some serial =>
        exact phasePolicyDispatch_covered (opened := (fun owner event payload binding past view
            response supported => PhaseCount.phaseOpeningPolicy_covered runtime leaks bounds owner
            event payload binding (fun _ _ => PMF.pure true) past view response supported)) setup
            mode runtime leaks bounds (fun owner event payload binding =>
            PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _
            _ => PMF.pure true)) _
          (timingWordBinding_covered setup mode runtime leaks bounds wellFormed assessment block low
            generation 0 le_rfl (by norm_num) (some serial) who word) who past view response
            selected

/-- Every full input either has a word-independent law or reads exactly the
addressed original binding result. Timing WAIT does not erase the word. -/
theorem phaseCommitTimingWordPolicy_cases {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    (∃ law, ∀ word, phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed
      assessment block low generation slotWeight slotNonnegative slotBounded option who word past
        view = law) ∨
    ∃ event payload, ∃ binding :
      (serviceGraph setup mode).outputLayout event = .binding who payload,
      (low ≤ event.val ∧ event.val < low + block.length) ∧
      view.application.2.attempt = ⟨low, generation⟩ ∧
      ∀ word, phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
        block low generation slotWeight slotNonnegative slotBounded option who word past view =
        phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload
          ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
            (phaseSourceView? setup mode runtime leaks who event view))).map
              (fun choice => CommitRecoveryMove.missed choice.1)) option slotWeight
              slotNonnegative
          slotBounded (phaseRecoveryBindingData setup mode event who payload binding
            (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1 past view
              := by
  classical
  let bindingFamily := fun index : Bool × DecisionView who Δ =>
    if index.1 then timingWordBinding setup mode runtime leaks bounds wellFormed assessment block
      low generation 1 (by norm_num) le_rfl none who index.2
    else timingWordBinding setup mode runtime leaks bounds wellFormed assessment block low
      generation 0 le_rfl (by norm_num) option who index.2
  obtain ⟨law, constant⟩ | ⟨event, payload, binding, selected⟩ :=
    phasePolicyDispatch_indexed_cases setup mode runtime leaks (fun owner event payload binding =>
        PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding (fun _ _ =>
        PMF.pure true)) bindingFamily who past view
  · refine Or.inl ⟨mix slotWeight slotNonnegative slotBounded law
        (match option with | none => PMF.pure ⟨none⟩ | some _ => law), ?_⟩
    intro word
    have slots := constant (true, word)
    have main := constant (false, word)
    simp only [bindingFamily, Bool.false_eq_true, ↓reduceIte] at slots main
    cases option <;> simp only [phaseCommitTimingWordPolicy, slots, main]
  · by_cases addressed : low ≤ event.val ∧ event.val < low + block.length ∧
        view.application.2.attempt = ⟨low, generation⟩
    · refine Or.inr ⟨event, payload, binding, ⟨addressed.1, addressed.2.1⟩, addressed.2.2, ?_⟩
      intro word
      have slots := selected (true, word)
      have main := selected (false, word)
      simp only [bindingFamily, Bool.false_eq_true, ↓reduceIte] at slots main
      cases option <;>
        simp only [phaseCommitTimingWordPolicy, slots, main, timingWordBinding, dite_true,
          cast_eq, ite_eq_left addressed, phaseBindingTimingWordResponse, mix_one, mix_zero]
    · refine Or.inl ⟨mix slotWeight slotNonnegative slotBounded
        (phaseRecoverySlotPolicy setup mode runtime leaks bounds wellFormed assessment who event
          payload binding past view)
        (match option with
        | none => PMF.pure ⟨none⟩
        | some serial => phaseRecoveryTimingPolicy setup mode runtime leaks bounds wellFormed
            assessment who event payload binding (some serial) past view), ?_⟩
      intro word
      have slots := selected (true, word)
      have main := selected (false, word)
      simp only [bindingFamily, Bool.false_eq_true, ↓reduceIte] at slots main
      cases option <;>
        simp only [phaseCommitTimingWordPolicy, slots, main, timingWordBinding, dite_true,
          ite_eq_right addressed, mix_one, mix_zero]

/-- Supported atoms have equal likelihood across compatible latent source
words. The RAW perturbation tier is deliberately not part of this family. -/
theorem phaseCommitTimingWordPolicy_apply_eq_of_support
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player)
    (first second : DecisionView who Δ)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (left : response ∈ (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed
      assessment block low generation slotWeight slotNonnegative slotBounded option who first
        past view).support)
    (right : response ∈ (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed
      assessment block low generation slotWeight slotNonnegative slotBounded option who second
        past view).support) :
    phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who first past view
        response =
      phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who second past view
        response := by
  obtain ⟨law, constant⟩ | ⟨event, payload, binding, _inside, _address, selected⟩ :=
    phaseCommitTimingWordPolicy_cases setup mode runtime leaks bounds wellFormed assessment block
      low generation slotWeight slotNonnegative slotBounded option who past view
  · rw [constant first, constant second]
  · rw [selected first] at left ⊢
    rw [selected second] at right ⊢
    exact phaseBindingTimingWordResponse_apply_eq_of_support setup mode runtime leaks bounds who
      event payload _ option slotWeight slotNonnegative slotBounded _ _ past view response left
        right

open Classical in
/-- For a fixed actual timing member, complete recall filters the original
word prior by the actual member-consistency fiber. A WAIT record supplies no
spurious source-result constraint. -/
theorem phaseCommitTimingWordPolicy_posterior_consistency_fiber
    {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player)
    (prior : PMF (DecisionView who Δ))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (consistent : ((phaseApplication runtime leaks).policyMixture prior
      (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who)).policy.Consistent
        past) :
    ((phaseApplication runtime leaks).policyMixture prior
      (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who)).posterior past =
      fiberPosterior prior (fun word => decide ((phaseCommitTimingWordPolicy setup mode runtime
        leaks
        bounds wellFormed assessment block low generation slotWeight slotNonnegative slotBounded
          option who word).Consistent past)) true := by
  apply (phaseApplication runtime leaks).policyMixture_posterior_consistency_fiber prior _ ?_ past
    consistent
  intro earlier view response first second left right
  exact phaseCommitTimingWordPolicy_apply_eq_of_support setup mode runtime leaks bounds wellFormed
    assessment block low generation slotWeight slotNonnegative slotBounded option who first second
      earlier view response left
        right

/-- A genuine addressed binding request reads its selected original word
result through the actual timing channel, without any menu-success premise. -/
theorem phaseCommitTimingWordPolicy_binding {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ)
    (execution : (phaseApplication runtime leaks).Execution) {inputs}
    (valid : execution.application.Invariant inputs)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : execution.application.SeedRequest who ⟨execution.application.attempt, event⟩)
    (inside : low ≤ event.val ∧ event.val < low + block.length)
    (address : execution.application.attempt = ⟨low, generation⟩) :
    phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who word
        (execution.recall who)
          (execution.observe (phaseApplication runtime leaks) who) =
      phaseBindingTimingWordResponse setup mode runtime leaks bounds who event payload
        ((assessment.strategy who (setup.commitRecoveryClearInformation wellFormed who
          (phaseSourceView? setup mode runtime leaks who event
            (execution.observe (phaseApplication runtime leaks) who)))).map
              (fun choice => CommitRecoveryMove.missed choice.1)) option slotWeight
              slotNonnegative
        slotBounded (phaseRecoveryBindingData setup mode event who payload binding
          (CommitRecoveryMove.lift (block.wordAction who (event.val - low) word))).1
        (execution.recall who) (execution.observe (phaseApplication runtime leaks) who) := by
  classical
  have addressed : low ≤ event.val ∧ event.val < low + block.length ∧
      (execution.observe (phaseApplication runtime leaks) who).application.2.attempt =
        ⟨low, generation⟩ := ⟨inside.1, inside.2, address⟩
  have slots := phasePolicyDispatch_binding setup mode runtime leaks (fun owner event payload
      binding => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload binding
      (fun _ _ => PMF.pure true))
    (timingWordBinding setup mode runtime leaks bounds wellFormed assessment block low generation
      1 (by norm_num) le_rfl none who word) execution valid who event payload binding request
  cases option with
  | none =>
      simp only [phaseCommitTimingWordPolicy, slots, timingWordBinding, dite_true, cast_eq,
        ite_eq_left addressed, phaseBindingTimingWordResponse, mix_one]
  | some serial =>
      have main := phasePolicyDispatch_binding setup mode runtime leaks (fun owner event payload
          binding => PhaseCount.phaseOpeningPolicy runtime leaks bounds owner event payload
          binding (fun _ _ => PMF.pure true))
        (timingWordBinding setup mode runtime leaks bounds wellFormed assessment block low
          generation
          0 le_rfl (by norm_num) (some serial) who word) execution valid who event payload binding
            request
      simp only [phaseCommitTimingWordPolicy, slots, main, timingWordBinding, dite_true, cast_eq,
        ite_eq_left addressed, phaseBindingTimingWordResponse, mix_one, mix_zero]

/-- Restrict the globally legal timing-word member to the actual finite
physical menu. The complete latent word is shared across its played agents. -/
def phaseCommitTimingWordStrategy {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ) :
    ((PhaseCount.onePacketMenu runtime leaks bounds).information initial horizon
      scheduler).BehavioralPolicy who :=
  (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy initial horizon scheduler who
    (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment block low
      generation slotWeight slotNonnegative slotBounded option who word)

theorem phaseCommitTimingWordStrategy_map_val {Γ Δ : SourceCtx Player L} {O P : Finset VarId}
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (block : SourceProgram.CommitPrefix Γ O Δ P) (low generation : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (initial : PMF (phaseApplication runtime leaks).State) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (option : LateOption bounds.candidateCount) (who : Player) (word : DecisionView who Δ)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    ((phaseCommitTimingWordStrategy setup mode runtime leaks bounds wellFormed assessment block low
      generation slotWeight slotNonnegative slotBounded initial horizon scheduler option who word)
        (some (past, view))).map Subtype.val =
      (phaseCommitTimingWordPolicy setup mode runtime leaks bounds wellFormed assessment
      block low generation slotWeight slotNonnegative slotBounded option who word past view).map
        some := by
  exact (PhaseCount.onePacketMenu runtime leaks bounds).restrictPolicy_map_val initial horizon
    scheduler who _ past view (fun response supported => phaseCommitTimingWordPolicy_covered setup
      mode runtime leaks bounds wellFormed assessment block low generation slotWeight
        slotNonnegative
        slotBounded option who word past view response supported)

end Vegas
