/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCountServicePolicy
import Vegas.Game.PhaseObservableDomainValue
import Vegas.Pending.PhaseResponseNormalization
import Interaction.ReactiveAliasLaw

/-! # Operational aliases in the selected counted source prescription

The actual source query uses the current physical view. The timing word,
eligibility test and raw menu retain observations and emissions, but ignore
the hidden syntax of equivalent evidence requests. The original raw aliases
are summed by the existing response-normalization history projection.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (bounds : MessageBounds (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

omit [Fintype Player] in
/-- Normalize response aliases only for the selected owners. Every other
owner's actual raw recall, in particular the focal information, is retained. -/
def phaseCountServiceNormalization (owners : Finset Player) : (app).SubmissionNormalization where
  normalize who view known material := if who ∈ owners then
    (PhaseCount.normalization runtime leaks).normalize who view known material else material
  idempotent who view known material := by
    by_cases inside : who ∈ owners
    · simpa only [ite_eq_left inside] using
        (PhaseCount.normalization runtime leaks).idempotent who view known material
    · simp only [ite_eq_right inside]
  packet state who known material := by
    by_cases inside : who ∈ owners
    · simpa only [ite_eq_left inside] using
        (PhaseCount.normalization runtime leaks).packet state who known material
    · simp only [ite_eq_right inside]
  submit state who known material := by
    by_cases inside : who ∈ owners
    · simpa only [ite_eq_left inside] using
        (PhaseCount.normalization runtime leaks).submit state who known material
    · simp only [ite_eq_right inside]

omit [Fintype Player] in
theorem phaseCountServiceNormalization_recall_fixed (owners : Finset Player) (who : Player)
    (outside : who ∉ owners) (past : List (app).PlayerEntry) :
    (phaseCountServiceNormalization setup mode runtime leaks owners).recall who past = past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [ReactiveApplication.SubmissionNormalization.recall_append_action, ih]
      rcases entry with ⟨before, ⟨transmitted⟩, emitted⟩
      cases transmitted <;>
        simp only [ReactiveApplication.SubmissionNormalization.action,
          phaseCountServiceNormalization, ite_eq_right outside]

omit [Fintype Player] in
/-- A nonselected observer's complete native information is unchanged,
including its original raw actions rather than only an operational projection. -/
theorem phaseCountServiceNormalization_info_fixed (owners : Finset Player) (who : Player)
    (outside : who ∉ owners) (observed : (app).Info) :
    (phaseCountServiceNormalization setup mode runtime leaks owners).info who observed =
      observed := by
  cases observed with
  | none => rfl
  | some pair =>
      rcases pair with ⟨past, view⟩
      simp only [ReactiveApplication.SubmissionNormalization.info, Option.map_some,
        phaseCountServiceNormalization_recall_fixed setup mode runtime leaks owners who outside]

omit [Fintype Player] in
theorem phaseCountService_submissionCount_normal_recall (normal : (app).SubmissionNormalization)
    (who : Player) (past : List (app).PlayerEntry) :
    (app).submissionCount (normal.recall who past) = (app).submissionCount past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [normal.recall_append_action, (app).submissionCount_append,
        (app).submissionCount_append, ih]
      rcases entry with ⟨before, ⟨transmitted⟩, emitted⟩
      cases transmitted <;> rfl

omit [Fintype Player] in
private theorem normalized_localEnvelope (normal : (app).SubmissionNormalization)
    (who actor : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (material : (app).Submission) :
    PhaseCount.localEnvelope runtime leaks actor (normal.recall who past) view material =
      PhaseCount.localEnvelope runtime leaks actor past view material := by
  simp only [PhaseCount.localEnvelope, phaseCountService_submissionCount_normal_recall,
    ReactiveApplication.ResponseMenu.knownPackets, normal.recall_outputs]

omit [Fintype Player] in
private theorem normalized_ownerWord (normal : (app).SubmissionNormalization)
    (who owner : Player) (coordinate : CommitAttemptEvent graph)
    (past : List (app).PlayerEntry) :
    PhaseSeedScheduler.ownerWord runtime leaks coordinate owner (normal.recall who past) =
      PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past := by
  induction past using List.reverseRecOn with
  | nil => rfl
  | append_singleton past entry ih =>
      rw [normal.recall_append_action]
      simp only [PhaseSeedScheduler.ownerWord, List.filter_append, List.map_append] at ih ⊢
      rw [ih]
      by_cases ready : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate
      all_goals simp [ready]

omit [Fintype Player] in
/-- The complete original local timing word ignores evidence-request aliases,
including earlier callbacks at other addresses or retired attempts. -/
theorem phaseCountService_serviceClocks_normal_recall (normal : (app).SubmissionNormalization)
    (who owner : Player) (coordinate : CommitAttemptEvent graph)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
        (normal.recall who past) view =
      PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view := by
  simp only [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput,
    normalized_ownerWord]

/-- The actual counted raw menu, including its evidence-request aliases,
depends on original recall only through unchanged emissions and send counts. -/
theorem phaseCountService_actions_normal_recall (normal : (app).SubmissionNormalization)
    (who actor : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    PhaseCount.onePacketActions runtime leaks bounds actor (normal.recall who past) view =
      PhaseCount.onePacketActions runtime leaks bounds actor past view := by
  classical
  have raw : (PhaseCount.rawMenu runtime leaks bounds).actions actor
      (normal.recall who past) view =
        (PhaseCount.rawMenu runtime leaks bounds).actions actor past view := by
    simp only [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions,
      ReactiveApplication.ResponseMenu.knownPackets, normal.recall_outputs]
  ext response
  simp only [PhaseCount.mem_onePacketActions, raw, PhaseCount.OnePacketResponse,
    normal.recall_outputs, normalized_localEnvelope]

section Policy

variable (plan : RuntimePhasePlan (serviceGraph setup mode))
  (values : ∀ who info, PMF (setup.CommitRecoveryValueChoice who info))
  (choose : Player → CommitAttemptEvent (serviceGraph setup mode) → List Nat → Bool)
  (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)

local notation "selected" => phaseCountServicePolicy setup mode runtime leaks bounds
  (phaseObservableDomainValues setup mode runtime leaks plan values) choose
  failure timing firstNonnegative firstBounded timingNonnegative timingBounded
  slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded

include plan values choose failure timing firstNonnegative firstBounded
  timingNonnegative timingBounded slotWeight slotNonnegative slotBounded
  rawWeight rawNonnegative rawBounded

/-- The literal selected source-domain prescription ignores normalized private
response names at every callback. Its original source law and all tier weights
are unchanged; the current source query is read from the actual physical view. -/
theorem phaseCountServicePolicy_normal_recall (normal : (app).SubmissionNormalization)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    selected who (normal.recall who past) view = selected who past view := by
  classical
  have menu (owner : Player) := phaseCountService_actions_normal_recall
    setup mode runtime leaks bounds normal who owner past view
  have raw (owner : Player) : PhaseCount.countedSendLaw runtime leaks bounds owner
      (normal.recall who past) view =
        PhaseCount.countedSendLaw runtime leaks bounds owner past view := by
    simp only [PhaseCount.countedSendLaw, PhaseCount.countedSends, menu owner]
  have slots (owner : Player) (event : (graph).EventId) (payload : L.Ty) :
      PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload
        (normal.recall who past) view =
          PhaseCount.phaseBindingSlots runtime leaks bounds owner event payload past view := by
    simp only [PhaseCount.phaseBindingSlots, menu owner]
  unfold phaseCountServicePolicy
  apply phasePolicyDispatch_congr_input setup mode runtime leaks _ _ who _ _ view
  · intro owner event payload binding
    rw [raw owner]
    congr 1
    unfold PhaseCount.phaseOpeningPolicy
    split
    · rw [menu owner]
    · rfl
  · intro owner event payload binding
    unfold PhaseCount.bindingServiceReference PhaseCount.bindingServiceBase
      PhaseCount.bindingResultEncoder PhaseCount.phaseBindingSlotPolicy
      PhaseCount.phaseBindingPolicy
    simp only [phaseObservableDomainValues, raw owner,
      phaseCountService_serviceClocks_normal_recall, slots owner, menu owner]

/-- The actual normalized alias law is supported on the existing normalized
counted menu. Its mass is the pushforward of all original request aliases. -/
theorem phaseCountServicePolicy_alias_covered (normal : (app).SubmissionNormalization)
    (who : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action)
    (supported : response ∈ ((selected who past view).map
      (normal.action who past view)).support) :
    response ∈ (normal.menu (PhaseCount.onePacketMenu runtime leaks bounds)).actions
      who past view := by
  obtain ⟨raw, offered, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  exact (normal.menu_mem _ who past view _).mpr ⟨raw,
    phaseCountServicePolicy_covered setup mode runtime leaks bounds
      (phaseObservableDomainValues setup mode runtime leaks plan values) choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded
      slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
      who past view raw offered, rfl⟩

/-- The existing complete history runner sums every original RAW alias into
its actual operational response class. Both sides retain the same physical
initial law and source-domain prescription. -/
theorem phaseCountServicePolicy_alias_history (normal : (app).SubmissionNormalization)
    (initial : PMF (app).State) (horizon : Nat) (scheduler : (app).Scheduler) (fuel : Nat) :
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let stable := fun who past view =>
      phaseCountService_actions_normal_recall setup mode runtime leaks bounds
        normal who who past view
    let native := fun who => menu.restrictPolicy initial horizon scheduler who (selected who)
    let canonical := fun who => (normal.menu menu).restrictPolicy initial horizon scheduler who
      (fun past view => (selected who past view).map (normal.action who past view))
    ((menu.information initial horizon scheduler).runBehavioral native fuel).map
        (normal.history menu stable initial horizon scheduler) =
      ((normal.menu menu).information initial horizon scheduler).runBehavioral canonical fuel := by
  classical
  intro menu stable native canonical
  have projects (who : Player) (observed : (app).Info) :
      (native who observed).map (normal.choice menu stable initial horizon scheduler who observed) =
        canonical who (normal.info who observed) := by
    apply pmf_map_injective Subtype.val_injective
    rw [PMF.map_comp]
    cases observed with
    | none => rfl
    | some pair =>
        rcases pair with ⟨past, view⟩
        change ((menu.restrictPolicy initial horizon scheduler who (selected who)
          (some (past, view))).map (fun choice =>
            normal.optionChoice who (some (past, view)) choice.val)) =
          ((normal.menu menu).restrictPolicy initial horizon scheduler who
            (fun past view => (selected who past view).map (normal.action who past view))
              (some (normal.recall who past, view))).map Subtype.val
        rw [show (fun choice => normal.optionChoice who (some (past, view)) choice.val) =
          (normal.optionChoice who (some (past, view))) ∘ Subtype.val
            from rfl, ← PMF.map_comp]
        rw [menu.restrictPolicy_map_val initial horizon scheduler who (selected who) past view
          (phaseCountServicePolicy_covered setup mode runtime leaks bounds
            (phaseObservableDomainValues setup mode runtime leaks plan values) choose
            failure timing firstNonnegative firstBounded timingNonnegative timingBounded
            slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded who
              past view)]
        rw [(normal.menu menu).restrictPolicy_map_val initial horizon scheduler who _
          (normal.recall who past) view
          (phaseCountServicePolicy_alias_covered setup mode runtime leaks bounds plan values
            choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
            slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded normal who
              (normal.recall who past) view)]
        rw [phaseCountServicePolicy_normal_recall setup mode runtime leaks bounds plan values
          choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded]
        simp only [PMF.map_comp, Function.comp_def,
          ReactiveApplication.SubmissionNormalization.optionChoice,
          Option.map_some, normal.action_recall]
  exact normal.runBehavioral_projection menu stable initial horizon scheduler native canonical
    projects fuel (menu.protocol initial horizon scheduler).initHistory

/-- Summing selected foreign evidence-request aliases preserves the full
focal information jointly with the complete physical application, including
all original retired attempt snapshots. The original initial law is retained. -/
theorem phaseCountServicePolicy_alias_focal_joint (owners : Finset Player) (focal : Player)
    (outside : focal ∉ owners) (initial : PMF (app).State) (horizon : Nat)
    (scheduler : (app).Scheduler) (fuel : Nat) :
    let normal := phaseCountServiceNormalization setup mode runtime leaks owners
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let native := fun who => menu.restrictPolicy initial horizon scheduler who (selected who)
    let canonical := fun who => (normal.menu menu).restrictPolicy initial horizon scheduler who
      (fun past view => (selected who past view).map (normal.action who past view))
    ((menu.information initial horizon scheduler).runBehavioral native fuel).map
        (fun history => ((menu.information initial horizon scheduler).infoOf focal history.trace,
          history.state.map (fun control => control.execution.application))) =
      (((normal.menu menu).information initial horizon scheduler).runBehavioral canonical fuel).map
        (fun history => (((normal.menu menu).information initial horizon scheduler).infoOf
          focal history.trace,
            history.state.map (fun control => control.execution.application))) := by
  classical
  intro normal menu native canonical
  let stable := fun who past view =>
    phaseCountService_actions_normal_recall setup mode runtime leaks bounds
      normal who who past view
  have projection := phaseCountServicePolicy_alias_history setup mode runtime leaks bounds
    plan values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
    normal initial horizon scheduler fuel
  rw [← projection, PMF.map_comp]
  congr 1
  funext history
  apply Prod.ext
  · change (menu.information initial horizon scheduler).infoOf focal history.trace =
      ((normal.menu menu).information initial horizon scheduler).infoOf focal
        (normal.history menu stable initial horizon scheduler history).trace
    rw [normal.history_info menu stable initial horizon scheduler,
      phaseCountServiceNormalization_info_fixed setup mode runtime leaks owners focal outside]
  · change history.state.map (fun control => control.execution.application) =
      (normal.state history.state).map (fun control => control.execution.application)
    cases history.state <;> rfl

end Policy

end Vegas
