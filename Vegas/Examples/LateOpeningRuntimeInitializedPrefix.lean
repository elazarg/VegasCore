/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeProtectedPrefix
import Vegas.Examples.LateOpeningRuntimeLatePrefixKernel
import Vegas.Examples.LateOpeningRuntimeAliceFirstWitness
import Interaction.ReactivePolicyInvariant

/-! # Initialized raw probabilities before the first receiver binding

The physical prefix retains the original prior and every protected raw
response. For a receiver class remembering empty receipts after clock zero,
all protected transmissions contribute exactly zero. Its probability is the
prior-weighted original protected-silence probability times the complete
original first-late response and continuation law. No clean-history menu or
posterior is substituted for the native execution distribution.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeInitializedPrefix

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeBindingPrefix LateOpeningRuntimeProtectedRecall
  LateOpeningRuntimeAliceFirstWitness LateOpeningRuntimeLatePrefixKernel

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

def protectedDecision (bit : Bool) (label : Fin 3) : app.Execution :=
  let start := initialExecution bit label
  recorded start (.activate alice) start.application

def afterProtected (players : Player → app.Policy) (execution : app.Execution) :
    PMF app.Execution :=
  (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 10 execution).bind
    (fun before => before.environmentStep app (.activate bob))

private theorem initialized_law : initial = prior.map
    (fun parameter => initialPhysical parameter.1 parameter.2) := by
  change (prior.map (fun parameter => sourceInitial parameter.1 parameter.2)).map _ = _
  rw [PMF.map_comp]
  rfl

theorem protected_round (players : Player → app.Policy) (bit : Bool) (label : Fin 3) :
    app.round (LateOpeningRuntimeService.scheduler weight nonnegative) players
      (initialExecution bit label) = app.invoke players alice (protectedDecision bit label) := by
  rw [fixed_round weight nonnegative players (initialExecution bit label)
    (protectedDecision bit label) 0 (.activate alice) rfl rfl
    (recorded_activation _ alice (by rfl))]
  rfl

/-- The actual full prefix before any filtering, including every protected
raw response and all later private representations. -/
theorem initialized_binding_law
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who) :
    bindingPrefix weight nonnegative profile =
      let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile
      (prior.bind fun parameter =>
        (app.invoke players alice (protectedDecision parameter.1 parameter.2)).bind
          (afterProtected weight nonnegative players)).map
            (fun execution => some ⟨14, some bob, execution⟩) := by
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
  change (app.roundsFrom initial (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 11).bind (fun execution => (execution.environmentStep app (.activate bob)).map
      (fun next => some (⟨14, some bob, next⟩ : app.Control))) =
    (prior.bind fun parameter =>
      (app.invoke players alice (protectedDecision parameter.1 parameter.2)).bind
        (afterProtected weight nonnegative players)).map
          (fun execution => some (⟨14, some bob, execution⟩ : app.Control))
  unfold ReactiveApplication.roundsFrom
  rw [initialized_law, PMF.bind_map, PMF.bind_bind]
  simp only [Function.comp_def]
  rw [PMF.map_bind]
  apply bind_congr_on_support _
  intro parameter _
  have first := protected_round weight nonnegative players parameter.1 parameter.2
  unfold initialExecution at first
  rw [ReactiveApplication.runRounds, first, PMF.bind_bind]
  simp only [afterProtected, PMF.map_bind]

/-- After protected silence the original first-late response is still drawn
from its complete native policy, then followed by the original future policy. -/
theorem silent_protected_law (players : Player → app.Policy) (bit : Bool) (label : Fin 3) :
    afterProtected weight nonnegative players (protectedSilent bit label) =
      (players alice ((firstLateDecision bit label).recall alice)
        ((firstLateDecision bit label).observe app alice)).bind fun response =>
          firstBindingLaw weight nonnegative (decisionHistory weight nonnegative bit label)
            response players := by
  let silent := protectedSilent bit label
  let waited := recorded silent .wait silent.application
  let ticked := recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players silent = PMF.pure waited := by
    rw [fixed_round weight nonnegative players silent waited 1 .wait rfl rfl
      (recorded_wait silent)]
    rfl
  have second : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players waited = PMF.pure ticked := by
    rw [fixed_round weight nonnegative players waited ticked 2
      (.application .advanceClock) rfl rfl (recorded_clock waited)]
    rfl
  have third : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players ticked = app.invoke players alice (firstLateDecision bit label) := by
    rw [fixed_round weight nonnegative players ticked (firstLateDecision bit label) 3
      (.activate alice) rfl rfl (recorded_activation ticked alice (by rfl))]
    rfl
  change ((app.runRounds _ players 10 silent).bind _) = _
  rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, second, PMF.pure_bind,
    ReactiveApplication.runRounds, third, PMF.bind_bind]
  unfold ReactiveApplication.invoke
  rw [PMF.bind_map]
  rfl

private def ProtectedPacket (execution : app.Execution) : Prop :=
  ∃ entry ∈ execution.recall alice,
    entry.beforeView.application.publicView.clock = 0 ∧ entry.action.transmission.isSome

private theorem protected_packet_invariant (players : Player → app.Policy) :
    app.PolicyInvariant players ProtectedPacket where
  respond execution who response present _ := by
    obtain ⟨entry, recalled, clockZero, issued⟩ := present
    exact ⟨entry, app.respond_recall_mono execution who alice response recalled, clockZero, issued⟩
  environment execution next command present reached := by
    change ∃ entry ∈ next.recall alice, _
    rw [app.environmentStep_recall execution next command reached]
    exact present

private theorem responded_protected_packet (bit : Bool) (label : Fin 3)
    (submission : app.Submission) :
    ProtectedPacket ((protectedDecision bit label).respond app alice ⟨some submission⟩) := by
  unfold ProtectedPacket
  simp only [ReactiveApplication.Execution.respond, ↓reduceIte, List.mem_append,
    List.mem_singleton]
  exact ⟨_, Or.inr rfl, rfl, rfl⟩

private theorem after_protected_trace (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (response : app.Action) (final : app.Execution)
    (reached : final ∈ (afterProtected weight nonnegative players
      ((protectedDecision bit label).respond app alice response)).support) :
    Nonempty ((app.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨14, some bob, final⟩)) := by
  obtain ⟨initialTrace⟩ := rawMenu.trace_initial initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) (initialPhysical bit label)
      (initialPhysical_supported bit label)
  obtain ⟨activated⟩ := app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 25 (initialExecution bit label)
      (protectedDecision bit label) (.activate alice)
      (rawMenu.toRawTrace _ _ _ initialTrace)
      (by exact (PMF.mem_support_pure_iff _ _).mpr rfl)
      (by rw [recorded_activation _ alice (by rfl)]; exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  obtain ⟨responded⟩ := app.raw_trace_respond initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 25
      (protectedDecision bit label) alice response activated
  obtain ⟨before, continued, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨beforeTrace⟩ := app.raw_trace_runRounds initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 15 10 _ before
      responded continued
  have cursor := app.runRounds_environmentRecall_length
    (LateOpeningRuntimeService.scheduler weight nonnegative) players 10 _ before continued
  change before.environmentRecall.length = 1 + 10 at cursor
  apply app.raw_trace_environment initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) 14 before final (.activate bob)
      beforeTrace _ moved
  change (.activate bob : app.Command) ∈ (stageChoice weight nonnegative
    before.environmentRecall.length (before.observeEnvironment app)).support
  rw [cursor]
  exact (PMF.mem_support_pure_iff _ _).mpr rfl

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite bob)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    bob site.1) (control : app.Control)
  (current : representative.1.state = some control) (active : control.actor = some bob)
  (remembered : app.PlayerEntry) (member : remembered ∈ control.execution.recall bob)
  (later : 0 < remembered.beforeView.application.publicView.clock)
  (empty : remembered.beforeView.receipts = [])

include current active member later empty in
/-- Every raw protected packet is excluded by the actual remembered receipt
observation, for arbitrary future policies. -/
theorem protected_packet_information_zero (players : Player → app.Policy)
    (bit : Bool) (label : Fin 3) (submission : app.Submission) (event : Set app.Execution)
    (observed : ∀ final ∈ event,
      app.observe bob (some ⟨14, some bob, final⟩) = site.1) :
    (afterProtected weight nonnegative players
      ((protectedDecision bit label).respond app alice ⟨some submission⟩)).toOuterMeasure event =
        0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro final reached selected
  obtain ⟨trace⟩ := after_protected_trace weight nonnegative players bit label
    ⟨some submission⟩ final reached
  have reprInfo := representative.2
  change (rawMenu.signals _ _ _).infoOf bob representative.1.trace = site.1 at reprInfo
  rw [rawMenu.info, current] at reprInfo
  have same := reprInfo.trans (observed final selected).symm
  simp only [ReactiveApplication.observe, active, ↓reduceIte] at same
  have sameRecall := congrArg Prod.fst (Option.some.inj same)
  change control.execution.recall bob = final.recall bob at sameRecall
  have silent := protected_silence_of_empty_receipt_recall weight nonnegative
    ⟨14, some bob, final⟩ trace remembered (sameRecall ▸ member) later empty
  obtain ⟨before, continued, moved⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  have invariant := protected_packet_invariant players
  have pending := invariant.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    10 _ before (responded_protected_packet bit label submission) continued
  obtain ⟨entry, recalled, clockZero, issued⟩ :=
    invariant.environment before final (.activate bob) pending moved
  rw [silent entry recalled clockZero] at issued
  cases issued

include current active member later empty in
/-- Exact original type-prefix weights: prior, protected silence, and every
first-late raw response with the unchanged continuation policy. -/
theorem clean_information_probability
    (profile : ∀ who, (LateOpeningRuntimeNash.model weight nonnegative).BehavioralPolicy who)
    (event : Set app.ProtocolState)
    (observed : ∀ state ∈ event, app.observe bob state = site.1) :
    ((bindingPrefix weight nonnegative profile).toOuterMeasure event).toReal =
      let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
        (LateOpeningRuntimeService.scheduler weight nonnegative) profile
      expect prior fun parameter =>
        (players alice ((protectedDecision parameter.1 parameter.2).recall alice)
          ((protectedDecision parameter.1 parameter.2).observe app alice) ⟨none⟩).toReal *
        (((players alice ((firstLateDecision parameter.1 parameter.2).recall alice)
          ((firstLateDecision parameter.1 parameter.2).observe app alice)).bind
            fun response => firstBindingLaw weight nonnegative
              (decisionHistory weight nonnegative parameter.1 parameter.2) response players
          ).toOuterMeasure
              {final | some ⟨14, some bob, final⟩ ∈ event}).toReal := by
  classical
  let players := rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) profile
  rw [initialized_binding_law weight nonnegative profile, PMF.toOuterMeasure_map_apply]
  rw [toReal_toOuterMeasure_bind]
  apply expect_congr_on_support
  intro parameter _
  unfold ReactiveApplication.invoke
  rw [PMF.bind_map, toReal_toOuterMeasure_bind]
  calc
    _ = expect (players alice ((protectedDecision parameter.1 parameter.2).recall alice)
        ((protectedDecision parameter.1 parameter.2).observe app alice))
        (fun response => if (⟨none⟩ : app.Action) = response then
          ((afterProtected weight nonnegative players
            (protectedSilent parameter.1 parameter.2)).toOuterMeasure
              {final | some ⟨14, some bob, final⟩ ∈ event}).toReal else 0) := by
      apply expect_congr_on_support
      intro response _
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => simp only [Function.comp_apply, ↓reduceIte]; rfl
      | some submission =>
          rw [ite_eq_right (by
            intro same
            cases same)]
          change ((afterProtected weight nonnegative players
            ((protectedDecision parameter.1 parameter.2).respond app alice ⟨some submission⟩)
            ).toOuterMeasure
              {final : app.Execution | some (⟨14, some bob, final⟩ : app.Control) ∈ event}
            ).toReal = 0
          rw [protected_packet_information_zero weight nonnegative site representative control
            current active remembered member later empty players parameter.1 parameter.2
            submission
            {final : app.Execution | some (⟨14, some bob, final⟩ : app.Control) ∈ event}
            (fun final selected => observed (some ⟨14, some bob, final⟩) selected)]
          rfl
    _ = _ := by
      rw [expect_ite_eq, silent_protected_law weight nonnegative]

end Vegas.Examples.LateOpeningRuntimeInitializedPrefix
