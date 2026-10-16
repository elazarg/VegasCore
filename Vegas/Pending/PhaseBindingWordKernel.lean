/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingEncodingLaw
import Interaction.ReactivePolicyMixture

/-! # Actual raw observations of one latent binding result

The omission marginal is retained independently of the complete source word.
Sending uses the existing canonical and fresh-slot encoders. A received failed
binding is a sending result, not an omission.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph)

/-- A latent typed result uses the actual physical slot channel, while the
original source omission draw remains a separate random choice. -/
def phaseBindingWordResponse (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : PMF Bool) (serial : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    PMF (phaseApplication runtime leaks).Action :=
  missing.bind fun omitted => if omitted then PMF.pure ⟨none⟩ else
    mix slotWeight slotNonnegative slotBounded
      (phaseBindingSlotPolicy runtime leaks bounds who event payload
        (fun _ _ => PMF.pure result) past view)
      (PMF.pure (phaseBindingResponse runtime leaks who event payload result serial))

/-- Every nonsilent word response names the selected result and a physical
slot. Arbitrary raw actions are not silently identified with this encoder. -/
theorem phaseBindingWordResponse_nonsilent
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : PMF Bool) (serial : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseBindingWordResponse runtime leaks bounds who event payload
      missing serial slotWeight slotNonnegative slotBounded result past view).support)
    (sending : response ≠ ⟨none⟩) :
    ∃ slot, response = phaseBindingResponse runtime leaks who event payload result slot := by
  classical
  obtain ⟨omitted, _, member⟩ := (PMF.mem_support_bind_iff ..).mp supported
  cases omitted with
  | true => exact (sending ((PMF.mem_support_pure_iff ..).mp member)).elim
  | false =>
      change response ∈ (mix slotWeight slotNonnegative slotBounded _ _).support at member
      rcases support_mix_subset _ _ _ _ _ member with fromSlot | canonical
      · unfold phaseBindingSlotPolicy at fromSlot
        split at fromSlot
        · obtain ⟨slot, _, drawn⟩ := (PMF.mem_support_bind_iff ..).mp fromSlot
          rw [PMF.pure_map] at drawn
          exact ⟨slot, (PMF.mem_support_pure_iff ..).mp drawn⟩
        · exact (sending ((PMF.mem_support_pure_iff ..).mp fromSlot)).elim
      · exact ⟨serial, (PMF.mem_support_pure_iff ..).mp canonical⟩

/-- At a real transmitting slot channel, the silence atom is exactly the
original omission atom and does not depend on the latent typed result. -/
theorem phaseBindingWordResponse_silence
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : PMF Bool) (serial : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (result : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (nonempty : (phaseBindingSlots runtime leaks bounds who event payload past view).Nonempty) :
    phaseBindingWordResponse runtime leaks bounds who event payload missing serial slotWeight
      slotNonnegative slotBounded result past view ⟨none⟩ = missing true := by
  classical
  have different (slot : Nat) : (⟨none⟩ : (phaseApplication runtime leaks).Action) ≠
      phaseBindingResponse runtime leaks who event payload result slot := by
    intro equal
    have sent := congrArg (fun action : (phaseApplication runtime leaks).Action =>
      action.transmission.isNone) equal
    cases sent
  have slotZero : phaseBindingSlotPolicy runtime leaks bounds who event payload
      (fun _ _ => PMF.pure result) past view ⟨none⟩ = 0 := by
    rw [phaseBindingSlotPolicy, dite_eq_left nonempty, PMF.bind_apply]
    apply ENNReal.tsum_eq_zero.mpr
    intro slot
    rw [PMF.pure_map, PMF.pure_apply, ite_eq_right (different slot), mul_zero]
  rw [phaseBindingWordResponse, PMF.bind_apply, tsum_bool]
  simp only [Bool.false_eq_true, ↓reduceIte, mix_apply, slotZero, PMF.pure_apply,
    ite_eq_right (different serial), mul_zero, zero_add, mul_one]

open Classical in
/-- A concrete latent-word policy using existing physical encoders. Its menu
guard is independent of the word, and it is legal at every input. -/
def phaseBindingWordPolicy {Word : Type} (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF Bool)
    (serial : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (read : Word → PublicationResult (L.Val payload)) (word : Word) :
    (phaseApplication runtime leaks).Policy := fun past view =>
  if ∀ result, phaseBindingResponse runtime leaks who event payload result (serial past view) ∈
      onePacketActions runtime leaks bounds who past view then
    phaseBindingWordResponse runtime leaks bounds who event payload (missing past view)
      (serial past view) slotWeight slotNonnegative slotBounded (read word) past view
  else PMF.pure ⟨none⟩

/-- Each latent member is a genuine globally menu-legal response policy. -/
theorem phaseBindingWordPolicy_covered {Word : Type} (who : Player) (event : graph.EventId)
    (payload : L.Ty)
    (missing : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF Bool)
    (serial : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (read : Word → PublicationResult (L.Val payload)) (word : Word)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (supported : response ∈ (phaseBindingWordPolicy runtime leaks bounds who event payload
      missing serial slotWeight slotNonnegative slotBounded read word past view).support) :
    response ∈ onePacketActions runtime leaks bounds who past view := by
  classical
  unfold phaseBindingWordPolicy at supported
  split at supported
  · rename_i covered
    obtain ⟨omitted, _, member⟩ := (PMF.mem_support_bind_iff ..).mp supported
    cases omitted with
    | true =>
        cases (PMF.mem_support_pure_iff ..).mp member
        exact silence_onePacket runtime leaks bounds who past view
    | false =>
        change response ∈ (mix slotWeight slotNonnegative slotBounded _ _).support at member
        rcases support_mix_subset _ _ _ _ _ member with slot | canonical
        · exact phaseBindingSlotPolicy_covered runtime leaks bounds who event payload
            (fun _ _ => PMF.pure (read word)) past view response slot
        · cases (PMF.mem_support_pure_iff ..).mp canonical
          exact covered (read word)
  · cases (PMF.mem_support_pure_iff ..).mp supported
    exact silence_onePacket runtime leaks bounds who past view

/-- A positive original omission draw leaves the complete-word posterior
unchanged after an actual silence record. No raw-noise atom is included. -/
theorem phaseBindingWordPolicy_posterior_wait {Word : Type} (prior : PMF Word)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF Bool)
    (serial : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (read : Word → PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (entry : (phaseApplication runtime leaks).PlayerEntry) (silent : entry.action = ⟨none⟩)
    (covered : ∀ result, phaseBindingResponse runtime leaks who event payload result
      (serial past entry.beforeView) ∈ onePacketActions runtime leaks bounds who past
        entry.beforeView)
    (nonempty : (phaseBindingSlots runtime leaks bounds who event payload past
      entry.beforeView).Nonempty)
    (positive : missing past entry.beforeView true ≠ 0) :
    let family := phaseBindingWordPolicy runtime leaks bounds who event payload missing serial
      slotWeight slotNonnegative slotBounded read
    ((phaseApplication runtime leaks).policyMixture prior family).posterior (past ++ [entry]) =
      ((phaseApplication runtime leaks).policyMixture prior family).posterior past := by
  intro family
  apply (phaseApplication runtime leaks).policyMixture_posterior_snoc_of_likelihood prior family
    past entry (missing past entry.beforeView true) ?_ positive
  intro word _supported
  change phaseBindingWordPolicy runtime leaks bounds who event payload missing serial
    slotWeight slotNonnegative slotBounded read word past entry.beforeView entry.action = _
  rw [phaseBindingWordPolicy, ite_eq_left covered, silent]
  exact phaseBindingWordResponse_silence runtime leaks bounds who event payload _ _ slotWeight
    slotNonnegative slotBounded (read word) past entry.beforeView nonempty

/-- An actual encoded send conditions the complete latent word only on its
addressed typed result. The physical slot and original omission probabilities
are ancillary on that fiber. -/
theorem phaseBindingWordResponse_posterior_send {Word : Type}
    (payload : L.Ty) (prior : PMF Word) (read : Word → PublicationResult (L.Val payload))
    (who : Player) (event : graph.EventId)
    (missing : PMF Bool) (serial : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (result : PublicationResult (L.Val payload)) (slot : Nat)
    (present : ∃ word ∈ prior.support, read word = result ∧
      phaseBindingResponse runtime leaks who event payload result slot ∈
        (phaseBindingWordResponse runtime leaks bounds who event payload missing serial
          slotWeight slotNonnegative slotBounded result past view).support) :
    let response := phaseBindingResponse runtime leaks who event payload result slot
    let joint := prior.bind fun word =>
      (phaseBindingWordResponse runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded (read word) past view).map fun action => (word, action)
    (fiberPosterior joint Prod.snd response).map Prod.fst =
      fiberPosterior prior read result := by
  apply conditional_observation_kernel_recovered prior read
    (fun value => phaseBindingWordResponse runtime leaks bounds who event payload missing serial
      slotWeight slotNonnegative slotBounded value past view) result
    (phaseBindingResponse runtime leaks who event payload result slot) present
  intro word _supported produced
  have sending : phaseBindingResponse runtime leaks who event payload result slot ≠
      (⟨none⟩ : (phaseApplication runtime leaks).Action) := by
    intro equal
    have sent := congrArg (fun action : (phaseApplication runtime leaks).Action =>
      action.transmission.isNone) equal
    cases sent
  obtain ⟨other, encoded⟩ := phaseBindingWordResponse_nonsilent runtime leaks bounds who event
    payload missing serial slotWeight slotNonnegative slotBounded (read word) past view _
      produced sending
  exact ((phaseBindingResponse_eq_iff runtime leaks who event payload result (read word)
    slot other).mp encoded).2.symm

/-- At an encoded sending record, behavioral implementation conditioning is
exactly conditioning the previous complete-word posterior on its typed result. -/
theorem phaseBindingWordPolicy_posterior_send {Word : Type} (prior : PMF Word)
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF Bool)
    (serial : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (read : Word → PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (entry : (phaseApplication runtime leaks).PlayerEntry)
    (result : PublicationResult (L.Val payload)) (slot : Nat)
    (sent : entry.action = phaseBindingResponse runtime leaks who event payload result slot)
    (covered : ∀ result, phaseBindingResponse runtime leaks who event payload result
      (serial past entry.beforeView) ∈ onePacketActions runtime leaks bounds who past
        entry.beforeView)
    (present : ∃ word ∈ (((phaseApplication runtime leaks).policyMixture prior
      (phaseBindingWordPolicy runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded read)).posterior past).support, read word = result ∧
      entry.action ∈ (phaseBindingWordResponse runtime leaks bounds who event payload
        (missing past entry.beforeView) (serial past entry.beforeView) slotWeight slotNonnegative
        slotBounded result past entry.beforeView).support) :
    let family := phaseBindingWordPolicy runtime leaks bounds who event payload missing serial
      slotWeight slotNonnegative slotBounded read
    let before := ((phaseApplication runtime leaks).policyMixture prior family).posterior past
    ((phaseApplication runtime leaks).policyMixture prior family).posterior (past ++ [entry]) =
      fiberPosterior before read result := by
  intro family before
  let kernel := fun value => phaseBindingWordResponse runtime leaks bounds who event payload
    (missing past entry.beforeView) (serial past entry.beforeView) slotWeight slotNonnegative
      slotBounded value past entry.beforeView
  let joint := before.bind fun word => (kernel (read word)).map fun action => (word, action)
  have raw := phaseBindingWordResponse_posterior_send runtime leaks bounds payload before read
    who event (missing past entry.beforeView) (serial past entry.beforeView) slotWeight
      slotNonnegative slotBounded past entry.beforeView result slot (by simpa only [sent] using
        present)
  change (fiberPosterior joint Prod.snd (phaseBindingResponse runtime leaks who event payload
    result slot)).map Prod.fst = _ at raw
  have signal : entry.action ∈ (joint.map Prod.snd).support := by
    obtain ⟨word, member, equal, produced⟩ := present
    apply (PMF.mem_support_map_iff ..).mpr
    refine ⟨(word, entry.action), ?_, rfl⟩
    apply (PMF.mem_support_bind_iff ..).mpr
    refine ⟨word, member, ?_⟩
    apply (PMF.mem_support_map_iff ..).mpr
    exact ⟨entry.action, equal.symm ▸ produced, rfl⟩
  have moved := map_fiberPosterior_readout joint Prod.swap Prod.fst entry.action signal
  have projected := congrArg (fun law => law.map Prod.snd) moved
  have swap : joint.map Prod.swap = before.bind fun word =>
      (family word past entry.beforeView).map fun action => (action, word) := by
    simp only [joint, PMF.map_bind, PMF.map_comp]
    apply congrArg (PMF.bind before)
    funext word
    change _ = (phaseBindingWordPolicy runtime leaks bounds who event payload missing serial
      slotWeight slotNonnegative slotBounded read word past entry.beforeView).map _
    rw [phaseBindingWordPolicy, ite_eq_left covered]
    rfl
  rw [swap] at projected
  rw [Interaction.ReactiveApplication.Implementation.posterior_snoc]
  change (fiberPosterior (before.bind fun word =>
    (family word past entry.beforeView).map fun action => (action, word)) Prod.fst entry.action).map
      Prod.snd = _
  rw [← projected]
  rw [PMF.map_comp]
  change (fiberPosterior joint Prod.snd entry.action).map Prod.fst = _
  rw [sent]
  exact raw


/-- The silent atom cannot distinguish latent typed results, even at an empty
slot menu. The original omission flag remains a separate source draw. -/
theorem phaseBindingWordResponse_silence_congr
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : PMF Bool) (serial : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (first second : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView) :
    phaseBindingWordResponse runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded first past view ⟨none⟩ =
      phaseBindingWordResponse runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded second past view ⟨none⟩ := by
  classical
  by_cases nonempty : (phaseBindingSlots runtime leaks bounds who event payload past view).Nonempty
  · rw [phaseBindingWordResponse_silence runtime leaks bounds who event payload missing serial
      slotWeight slotNonnegative slotBounded first past view nonempty,
      phaseBindingWordResponse_silence runtime leaks bounds who event payload missing serial
        slotWeight slotNonnegative slotBounded second past view nonempty]
  · have slot (result : PublicationResult (L.Val payload)) :
        phaseBindingSlotPolicy runtime leaks bounds who event payload (fun _ _ => PMF.pure result)
          past view = PMF.pure ⟨none⟩ := by
        rw [phaseBindingSlotPolicy, dite_eq_right nonempty]
    have different (result : PublicationResult (L.Val payload)) :
        (⟨none⟩ : (phaseApplication runtime leaks).Action) ≠
          phaseBindingResponse runtime leaks who event payload result serial := by
      intro same
      have sent := congrArg (fun response : (phaseApplication runtime leaks).Action =>
        response.transmission) same
      cases sent
    simp only [phaseBindingWordResponse, PMF.bind_apply, tsum_bool, Bool.false_eq_true,
      ↓reduceIte, mix_apply, slot, PMF.pure_apply, ite_eq_right (different first),
      ite_eq_right (different second)]

/-- On the common support of two latent results, a concrete raw reply has
identical mass. A send identifies its result; silence is ancillary. -/
theorem phaseBindingWordResponse_apply_eq_of_support
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : PMF Bool) (serial : Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (first second : PublicationResult (L.Val payload))
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (left : response ∈ (phaseBindingWordResponse runtime leaks bounds who event payload missing
      serial slotWeight slotNonnegative slotBounded first past view).support)
    (right : response ∈ (phaseBindingWordResponse runtime leaks bounds who event payload missing
      serial slotWeight slotNonnegative slotBounded second past view).support) :
    phaseBindingWordResponse runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded first past view response =
      phaseBindingWordResponse runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded second past view response := by
  by_cases silent : response = ⟨none⟩
  · rw [silent]
    exact phaseBindingWordResponse_silence_congr runtime leaks bounds who event payload missing
      serial slotWeight slotNonnegative slotBounded first second past view
  · obtain ⟨firstSlot, firstAt⟩ := phaseBindingWordResponse_nonsilent runtime leaks bounds who
      event payload missing serial slotWeight slotNonnegative slotBounded first past view response
        left silent
    obtain ⟨secondSlot, secondAt⟩ := phaseBindingWordResponse_nonsilent runtime leaks bounds who
      event payload missing serial slotWeight slotNonnegative slotBounded second past view response
        right silent
    have same := ((phaseBindingResponse_eq_iff runtime leaks who event payload first second
      firstSlot secondSlot).mp (firstAt.symm.trans secondAt)).2
    cases same
    rfl

/-- The global menu guard is word independent, so the same common-support
likelihood property holds at every input, including unrealized ones. -/
theorem phaseBindingWordPolicy_apply_eq_of_support {Word : Type}
    (who : Player) (event : graph.EventId) (payload : L.Ty)
    (missing : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → PMF Bool)
    (serial : List (phaseApplication runtime leaks).PlayerEntry →
      (phaseApplication runtime leaks).PlayerView → Nat)
    (slotWeight : ℝ) (slotNonnegative : 0 ≤ slotWeight) (slotBounded : slotWeight ≤ 1)
    (read : Word → PublicationResult (L.Val payload)) (first second : Word)
    (past : List (phaseApplication runtime leaks).PlayerEntry)
    (view : (phaseApplication runtime leaks).PlayerView)
    (response : (phaseApplication runtime leaks).Action)
    (left : response ∈ (phaseBindingWordPolicy runtime leaks bounds who event payload missing
      serial slotWeight slotNonnegative slotBounded read first past view).support)
    (right : response ∈ (phaseBindingWordPolicy runtime leaks bounds who event payload missing
      serial slotWeight slotNonnegative slotBounded read second past view).support) :
    phaseBindingWordPolicy runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded read first past view response =
      phaseBindingWordPolicy runtime leaks bounds who event payload missing serial slotWeight
        slotNonnegative slotBounded read second past view response := by
  unfold phaseBindingWordPolicy at left right ⊢
  split at left
  · rename_i guard
    simp only [ite_eq_left guard] at right ⊢
    exact phaseBindingWordResponse_apply_eq_of_support runtime leaks bounds who event payload
      (missing past view) (serial past view) slotWeight slotNonnegative slotBounded
        (read first) (read second) past view response left right
  · rename_i guard
    simp only [ite_eq_right guard]

end Vegas.EventGraphRuntime.PhaseCount
