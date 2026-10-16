/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountServiceReference
import Interaction.ReactiveMixtureExtraCoordinate

/-! # Original local timing tapes for normalized counted binding service -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

local notation "app" => phaseApplication runtime leaks

/-- The raw-origin coin and the local timing coin are separate from the source
result and from the original builder seed. Only the first timing coin uses
the fixed omission rate. Later coins only tremble the own-service decision. -/
def bindingServiceCoinLaw (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (index : Nat) : PMF (Bool × Bool) :=
  (mix rawWeight rawNonnegative rawBounded (PMF.pure true) (PMF.pure false)).bind fun raw =>
    ((if index = 0 then mix (failure + timing) firstNonnegative firstBounded
        (PMF.pure true) (PMF.pure false)
      else mix timing timingNonnegative timingBounded
        (PMF.pure true) (PMF.pure false)).map (Prod.mk raw))

/-- A fixed local tape chooses only the SEND/WAIT tier. The selected source
result and normalized hidden encoders retain their original independent laws. -/
def bindingServiceCoinResponse (owner : Player) (coordinate : CommitAttemptEvent graph)
    (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (coin : Bool × Bool) : (app).Policy := fun past view =>
  if coin.1 then countedSendLaw runtime leaks bounds owner past view
  else
    let clocks := PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view
    if clocks.length = 1 then
      if coin.2 then PMF.pure ⟨none⟩ else
        bindingResultEncoder runtime leaks bounds owner coordinate.event payload values slotWeight
          slotNonnegative slotBounded past view
    else if choose clocks then
      if coin.2 then PMF.pure ⟨none⟩ else
        bindingResultEncoder runtime leaks bounds owner coordinate.event payload values slotWeight
          slotNonnegative slotBounded past view
    else if coin.2 then
      bindingResultEncoder runtime leaks bounds owner coordinate.event payload values slotWeight
        slotNonnegative slotBounded past view
    else PMF.pure ⟨none⟩

theorem bindingServiceCoinResponse_covered (owner : Player)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (coin : Bool × Bool) (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (response : (app).Action)
    (supported : response ∈ (bindingServiceCoinResponse runtime leaks bounds owner coordinate
      payload values choose slotWeight slotNonnegative slotBounded coin past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  have waitCovered (member : response ∈ (PMF.pure ⟨none⟩ : PMF (app).Action).support) :
      response ∈ onePacketActions runtime leaks bounds owner past view := by
    cases (PMF.mem_support_pure_iff ..).mp member
    exact silence_onePacket runtime leaks bounds owner past view
  have sendCovered (member : response ∈ (bindingResultEncoder runtime leaks bounds owner
      coordinate.event payload values slotWeight slotNonnegative slotBounded past view).support) :
      response ∈ onePacketActions runtime leaks bounds owner past view :=
    bindingResultEncoder_covered runtime leaks bounds owner coordinate.event payload values
      slotWeight
      slotNonnegative slotBounded past view response member
  unfold bindingServiceCoinResponse at supported
  dsimp only at supported
  split at supported
  · exact countedSendLaw_covered runtime leaks bounds owner past view response supported
  · split at supported
    · split at supported
      · exact waitCovered supported
      · exact sendCovered supported
    · split at supported
      · split at supported
        · exact waitCovered supported
        · exact sendCovered supported
      · split at supported
        · exact sendCovered supported
        · exact waitCovered supported

/-- Averaging one fresh original coin gives exactly the normalized reference,
with no source omission resampling and no raw-menu cardinality factor. -/
theorem bindingServiceCoinResponse_average (owner : Player)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) :
    (bindingServiceCoinLaw failure timing firstNonnegative firstBounded timingNonnegative
      timingBounded rawWeight rawNonnegative rawBounded
        (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length).bind
      (fun coin => bindingServiceCoinResponse runtime leaks bounds owner coordinate payload values
        choose slotWeight slotNonnegative slotBounded coin past view) =
    bindingServiceReference runtime leaks bounds owner coordinate payload values choose failure
      timing
      firstNonnegative firstBounded timingNonnegative timingBounded slotWeight slotNonnegative
        slotBounded rawWeight rawNonnegative rawBounded past view := by
  have first : (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner past view).length =
      1 ↔ (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length = 0 := by
    simp [PhaseSeedScheduler.serviceClocks, PhaseSeedScheduler.informationInput]
  unfold bindingServiceCoinLaw
  rw [PMF.bind_bind, mix_bind]
  simp only [PMF.pure_bind, PMF.bind_map]
  unfold bindingServiceCoinResponse bindingServiceReference bindingServiceBase
  dsimp only
  by_cases early : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length = 0
  · simp only [early, ↓reduceIte, first.mpr early, mix_bind, PMF.pure_bind,
    Function.comp_def, mix_self, Bool.false_eq_true]
  · have late := mt first.mp early
    by_cases sending : choose (PhaseSeedScheduler.serviceClocks runtime leaks coordinate owner
        past view) = true
    · simp only [early, late, sending, ↓reduceIte, mix_bind, PMF.pure_bind,
      Function.comp_def, mix_self, Bool.false_eq_true]
    · simp only [early, late, sending, ↓reduceIte, mix_bind, PMF.pure_bind,
      Function.comp_def, mix_self, Bool.false_eq_true]

open Classical in
/-- One finite original table is retained. Outside this physical address its
coins are unread; the ordinary fallback retains complete menu coverage. -/
def bindingServiceTapeMember (outside : (app).Policy) (owner : Player) (coordinate :
  CommitAttemptEvent graph)
    (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat) (tape : Fin horizon → Bool × Bool) : (app).Policy := fun past view =>
  if PhaseRuntimeState.requests view.application.2 owner coordinate then
    if inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length < horizon
    then bindingServiceCoinResponse runtime leaks bounds owner coordinate payload values choose
      slotWeight slotNonnegative slotBounded
        (tape ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length, inside⟩)
          past view
    else bindingServiceReference runtime leaks bounds owner coordinate payload values choose failure
      timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded past view
  else outside past view

theorem bindingServiceTapeMember_covered (outside : (app).Policy) (owner : Player)
    (outsideCovered : ∀ past view response, response ∈ (outside past view).support →
      response ∈ onePacketActions runtime leaks bounds owner past view)
    (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
    (values : List (app).PlayerEntry → (app).PlayerView → PMF (PublicationResult (L.Val payload)))
    (choose : List Nat → Bool) (failure timing : ℝ)
    (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
    (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
    (horizon : Nat) (tape : Fin horizon → Bool × Bool)
    (past : List (app).PlayerEntry) (view : (app).PlayerView) (response : (app).Action)
    (supported : response ∈ (bindingServiceTapeMember runtime leaks bounds outside owner
      coordinate payload
      values choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
        slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon tape
          past view).support) :
    response ∈ onePacketActions runtime leaks bounds owner past view := by
  unfold bindingServiceTapeMember at supported
  split_ifs at supported
  · exact bindingServiceCoinResponse_covered runtime leaks bounds owner coordinate payload values
      choose slotWeight slotNonnegative slotBounded _ past view response supported
  · exact bindingServiceReference_covered runtime leaks bounds owner coordinate payload values
      choose
      failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded past view response supported
  · exact outsideCovered past view response supported

omit [Fintype Player] in
/-- An earlier response at this address strictly advances its local ordinal,
even when several callbacks occur at the same clock. -/
theorem bindingServiceOrdinal_lt (owner : Player) (coordinate : CommitAttemptEvent graph)
    (before past : List (app).PlayerEntry) (entry : (app).PlayerEntry)
    (recorded : before ++ [entry] <+: past)
    (requested : PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate) :
    (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner before).length <
      (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length := by
  classical
  have ordered := (recorded.filter fun item =>
    decide (PhaseRuntimeState.requests item.beforeView.application.2 owner coordinate)).length_le
  have step : (before.filter fun item =>
      decide (PhaseRuntimeState.requests item.beforeView.application.2 owner coordinate)).length <
      (past.filter fun item =>
        decide (PhaseRuntimeState.requests item.beforeView.application.2 owner
          coordinate)).length := by
    simp only [List.filter_append, List.filter_cons, List.filter_nil, requested, decide_true,
      ↓reduceIte, List.length_append, List.length_cons, List.length_nil] at ordered
    omega
  simpa only [PhaseSeedScheduler.ownerWord, List.length_map] using step


section OriginalTape

variable {Rest : Type} (owner : Player) (coordinate : CommitAttemptEvent graph) (payload : L.Ty)
  (values : Rest → List (app).PlayerEntry → (app).PlayerView →
    PMF (PublicationResult (L.Val payload)))
  (choose : List Nat → Bool) (failure timing : ℝ)
  (firstNonnegative : 0 ≤ failure + timing) (firstBounded : failure + timing ≤ 1)
  (timingNonnegative : 0 ≤ timing) (timingBounded : timing ≤ 1)
  (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
  (rawWeight : ℝ) (rawNonnegative : 0 ≤ rawWeight) (rawBounded : rawWeight ≤ 1)
  (horizon : Nat) (restLaw : PMF Rest)


local notation "weights" => fun (index : Fin horizon) =>
  bindingServiceCoinLaw failure timing firstNonnegative firstBounded timingNonnegative timingBounded
    rawWeight rawNonnegative rawBounded (Fin.val index)
local notation "original" => PMF.bind (independentProduct weights)
  (fun tape => PMF.map (Prod.mk tape) restLaw)

/-- The actual current local timing coins keep their ORIGINAL law jointly
with every other tape coordinate and arbitrary updated source/entry memory. -/
theorem bindingServiceTapeMember_posterior
    (outside : Rest → (app).Policy)
    (values : Rest → List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry)
    (inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length < horizon) :
    let selected : Fin horizon :=
      ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length, inside⟩
    ∃ remainder : PMF
        (({index : Fin horizon // index ≠ selected} → Bool × Bool) × Rest),
      (((app).policyMixture original (fun memory : (Fin horizon → Bool × Bool) × Rest =>
      bindingServiceTapeMember runtime leaks bounds (outside memory.2) owner coordinate payload
        (values memory.2)
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
              memory.1)).posterior past).map
          (fun memory => (memory.1 selected,
            (fun index : {index : Fin horizon // index ≠ selected} => memory.1 index.val,
              memory.2))) =
        (weights selected).bind (fun coin => remainder.map (Prod.mk coin)) := by
  classical
  intro selected
  apply (app).policyMixture_posterior_coordinate_extra weights restLaw (fun memory : (Fin
      horizon → Bool × Bool) × Rest =>
      bindingServiceTapeMember runtime leaks bounds (outside memory.2) owner coordinate payload
        (values memory.2)
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
              memory.1) selected past
  intro before entry recorded tape rest part
  by_cases earlierRequest :
      PhaseRuntimeState.requests entry.beforeView.application.2 owner coordinate
  · by_cases earlierInside :
        (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner before).length < horizon
    · have smaller := bindingServiceOrdinal_lt runtime leaks owner coordinate before past entry
        recorded earlierRequest
      have different : (⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate owner
          before).length, earlierInside⟩ : Fin horizon) ≠ selected := by
        intro same
        have equal := congrArg Fin.val same
        dsimp only [selected] at equal
        omega
      simp only [bindingServiceTapeMember, ite_eq_left earlierRequest,
        dite_eq_left earlierInside, Function.update_of_ne different]
    · simp only [bindingServiceTapeMember, ite_eq_left earlierRequest,
        dite_eq_right earlierInside]
  · simp only [bindingServiceTapeMember, ite_eq_right earlierRequest]

/-- Evaluating the immutable local tape reproduces the literal reference at
the actual queried address, averaged only over the genuine updated remainder.
The source memory and every other original coin remain in that remainder. -/
theorem bindingServiceTapeMember_realization
    (outside : Rest → (app).Policy)
    (values : Rest → List (app).PlayerEntry → (app).PlayerView →
      PMF (PublicationResult (L.Val payload)))
    (past : List (app).PlayerEntry)
    (view : (app).PlayerView)
    (request : PhaseRuntimeState.requests view.application.2 owner coordinate)
    (inside : (PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length < horizon) :
    ∃ remainder : PMF Rest,
      remainder = (((app).policyMixture original (fun memory : (Fin horizon → Bool × Bool) × Rest =>
          bindingServiceTapeMember runtime leaks bounds (outside memory.2) owner coordinate
            payload (values memory.2)
            choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
              slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
                memory.1)).posterior past).map Prod.snd ∧
      ((app).policyMixture original (fun memory : (Fin horizon → Bool × Bool) × Rest =>
      bindingServiceTapeMember runtime leaks bounds (outside memory.2) owner coordinate payload
        (values memory.2)
        choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
          slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
              memory.1)).policy past view =
        remainder.bind (fun rest => bindingServiceReference runtime leaks bounds owner coordinate
          payload (values rest) choose failure timing firstNonnegative firstBounded
            timingNonnegative
            timingBounded slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded
              past view) := by
  classical
  let selected : Fin horizon :=
    ⟨(PhaseSeedScheduler.ownerWord runtime leaks coordinate owner past).length, inside⟩
  obtain ⟨remaining, split⟩ := bindingServiceTapeMember_posterior
    (runtime := runtime) (leaks := leaks) (bounds := bounds) (owner := owner)
    (coordinate := coordinate) (payload := payload) (choose := choose)
    (failure := failure) (timing := timing) (firstNonnegative := firstNonnegative)
    (firstBounded := firstBounded) (timingNonnegative := timingNonnegative)
    (timingBounded := timingBounded) (slotWeight := slotWeight)
    (slotNonnegative := slotNonnegative) (slotBounded := slotBounded)
    (rawWeight := rawWeight) (rawNonnegative := rawNonnegative) (rawBounded := rawBounded)
    (horizon := horizon) (restLaw := restLaw) outside values past inside
  let remainder := remaining.map Prod.snd
  refine ⟨remainder, ?_, ?_⟩
  · have mapped := congrArg (PMF.map fun pair => pair.2.2) split
    symm
    simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, PMF.bind_const,
      remainder] using mapped
  · have marginal : (((app).policyMixture original
        (fun memory : (Fin horizon → Bool × Bool) × Rest =>
        bindingServiceTapeMember runtime leaks bounds (outside memory.2) owner coordinate
          payload (values memory.2)
          choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
            slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
                memory.1)).posterior past).map
        (fun memory => (memory.1 selected, memory.2)) =
        (weights selected).bind (fun coin => remainder.map (Prod.mk coin)) := by
      have mapped := congrArg (PMF.map fun pair => (pair.1, pair.2.2)) split
      simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def, remainder] using mapped
    have current (memory : (Fin horizon → Bool × Bool) × Rest) :
        (fun memory : (Fin horizon → Bool × Bool) × Rest =>
        bindingServiceTapeMember runtime leaks bounds (outside memory.2) owner coordinate
          payload (values memory.2)
          choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded
            slotWeight slotNonnegative slotBounded rawWeight rawNonnegative rawBounded horizon
                memory.1) memory past view = bindingServiceCoinResponse runtime leaks bounds
                    owner coordinate
          payload (values (Prod.snd memory)) choose slotWeight slotNonnegative slotBounded
            (memory.1 selected) past view := by
      simp only [bindingServiceTapeMember, ite_eq_left request, dite_eq_left inside, selected]
    rw [ReactiveApplication.policyMixture_policy]
    simp_rw [current]
    have evaluated := congrArg (fun law => law.bind fun pair =>
      bindingServiceCoinResponse runtime leaks bounds owner coordinate payload (values pair.2)
          choose
        slotWeight slotNonnegative slotBounded pair.1 past view) marginal
    rw [PMF.bind_map, PMF.bind_bind] at evaluated
    simp only [PMF.bind_map, Function.comp_def] at evaluated
    rw [evaluated, PMF.bind_comm]
    apply bind_congr_on_support
    intro rest _supported
    exact bindingServiceCoinResponse_average runtime leaks bounds owner coordinate payload
      (values rest)
      choose failure timing firstNonnegative firstBounded timingNonnegative timingBounded slotWeight
        slotNonnegative slotBounded rawWeight rawNonnegative rawBounded past view

end OriginalTape

end Vegas.EventGraphRuntime.PhaseCount
