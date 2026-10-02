/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceSilentChoicePosterior
import Vegas.Game.SourceServiceBindingRecallPosterior

/-! # Resolution timing after actual recalled silence

A positive first canonical silence likelihood retains timing index zero.
Later silence cannot decrease that index's posterior mass. Responses at
other events leave the family posterior unchanged, including when their
actions have zero likelihood under this single-event family.

The resulting response bound uses the first actual source likelihood, not
an assumed common source view. Closed later opportunity gates are allowed.
Source-likelihood convergence remains explicit; no belief transport or
sequential-equilibrium claim is made.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

open Classical in
/-- The timing atom posterior follows the actual supported recalled response. -/
theorem sourceServiceTurnFamily_posterior_point
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (timing : PMF (Fin (turns + 1)))
    (past : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (possible : entry.action ∈
      (((application setup leaks).policyMixture timing
        (sourceServiceTurnFamily setup leaks bound profile who event turns)).policy
          past entry.beforeView).support)
    (index : Fin (turns + 1)) :
    let app := application setup leaks
    let family := sourceServiceTurnFamily setup leaks bound profile who event turns
    let prior := (app.policyMixture timing family).posterior past
    (((app.policyMixture timing family).posterior (past ++ [entry])) index).toReal =
      (prior index).toReal * ((family index past entry.beforeView) entry.action).toReal /
        (((app.policyMixture timing family).policy past entry.beforeView) entry.action).toReal := by
  dsimp only
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let prior := (app.policyMixture timing family).posterior past
  let joint := prior.bind fun slot =>
    (family slot past entry.beforeView).map fun response => (response, slot)
  have marginal : joint.map Prod.fst = (app.policyMixture timing family).policy
      past entry.beforeView := by
    rw [app.policyMixture_policy]
    simp only [joint, PMF.map_bind, PMF.map_comp, Function.comp_def]
    exact bind_congr_on_support _ fun _ _ => PMF.map_id _
  have support : entry.action ∈ (joint.map Prod.fst).support := marginal.symm ▸ possible
  rw [ReactiveApplication.Implementation.posterior_snoc]
  change (((fiberPosterior joint Prod.fst entry.action).map Prod.snd) index).toReal = _
  rw [fiberPosterior_map_snd_apply joint entry.action support index, bind_map_tag_apply,
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_inv, marginal]
  rfl

private theorem turnFamily_silent_zero_mono
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (timing : PMF (Fin (turns + 1)))
    (past : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (silent : entry.action = ⟨none⟩)
    (later : sourceServiceTurn setup leaks who event past entry.beforeView ≠ some 0)
    (positive : 0 < (((application setup leaks).policyMixture timing
      (sourceServiceTurnFamily setup leaks bound profile who event turns)).posterior
        past 0).toReal) :
    (((application setup leaks).policyMixture timing
      (sourceServiceTurnFamily setup leaks bound profile who event turns)).posterior
        past 0).toReal ≤
      (((application setup leaks).policyMixture timing
        (sourceServiceTurnFamily setup leaks bound profile who event turns)).posterior
          (past ++ [entry]) 0).toReal := by
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let prior := (app.policyMixture timing family).posterior past
  let law := (app.policyMixture timing family).policy past entry.beforeView
  have waiting : family 0 past entry.beforeView = app.silentPolicy past entry.beforeView :=
    app.turnScheduledPolicy_unselected _ _ _ _ _ _ (fun slot same => by
      cases Option.some.inj same
      exact later)
  have possible : entry.action ∈ law.support := by
    apply app.policyMixture_action_support _ _ _ _ 0
    · exact pmf_toReal_pos_iff.mp positive
    · rw [waiting, silent]
      exact app.silentPolicy_support past entry.beforeView
  have massPositive := pmf_toReal_pos_iff.mpr possible
  have massBound := pmf_toReal_apply_le_one law entry.action
  have update := sourceServiceTurnFamily_posterior_point timing past entry possible 0
  dsimp only at update
  change (((app.policyMixture timing family).posterior (past ++ [entry])) 0).toReal =
    (prior 0).toReal * ((family 0 past entry.beforeView) entry.action).toReal /
      (law entry.action).toReal at update
  rw [waiting, silent] at update
  simp only [ReactiveApplication.silentPolicy, PMF.pure_apply, ↓reduceIte,
    ENNReal.toReal_one, mul_one] at update
  rw [update]
  rw [silent] at massPositive massBound
  apply (le_div_iff₀ massPositive).mpr
  exact mul_le_of_le_one_right positive.le massBound

private theorem turnFamily_after_first_zero_mono
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (timing : PMF (Fin (turns + 1)))
    (before : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (first : sourceServiceTurn setup leaks who event before entry.beforeView = some 0)
    (after : List (application setup leaks).PlayerEntry)
    (positive : 0 < (((application setup leaks).policyMixture timing
      (sourceServiceTurnFamily setup leaks bound profile who event turns)).posterior
        (before ++ [entry]) 0).toReal)
    (lawful : ∀ earlier current later, before ++ entry :: after = earlier ++ current :: later →
      current.beforeView.application.publicView.ownTurn? who = some event →
        current.action = ⟨none⟩) :
    (((application setup leaks).policyMixture timing
      (sourceServiceTurnFamily setup leaks bound profile who event turns)).posterior
        (before ++ [entry]) 0).toReal ≤
      (((application setup leaks).policyMixture timing
        (sourceServiceTurnFamily setup leaks bound profile who event turns)).posterior
          (before ++ entry :: after) 0).toReal := by
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  induction after using List.reverseRecOn with
  | nil => exact le_rfl
  | append_singleton after current ih =>
      have earlierLawful : ∀ earlier previous later,
          before ++ entry :: after = earlier ++ previous :: later →
          previous.beforeView.application.publicView.ownTurn? who = some event →
            previous.action = ⟨none⟩ := by
        intro earlier previous later split turn
        apply lawful earlier previous (later ++ [current]) _ turn
        simpa only [List.append_assoc, List.cons_append] using
          congrArg (fun entries => entries ++ [current]) split
      have old := ih earlierLawful
      let past := before ++ entry :: after
      have later : sourceServiceTurn setup leaks who event past current.beforeView ≠ some 0 := by
        intro firstNow
        exact (sourceServiceTurn_first firstNow).2 entry
          (List.mem_append_right _ List.mem_cons_self) (sourceServiceTurn_first first).1
      have currentSplit : before ++ entry :: (after ++ [current]) = past ++ current :: [] := by
        simp only [past, List.append_assoc, List.cons_append]
      by_cases turn : current.beforeView.application.publicView.ownTurn? who = some event
      · have silent := lawful past current [] currentSplit turn
        have next := turnFamily_silent_zero_mono timing past current silent later
          (lt_of_lt_of_le positive old)
        simpa only [past, List.append_assoc, List.cons_append, List.append_nil] using old.trans next
      · have unchanged := app.policyMixture_posterior_snoc timing family past current
          (app.silentPolicy past current.beforeView) (fun slot =>
            app.turnScheduledPolicy_of_none _ _ _ _ _ _
              (sourceServiceTurn_of_not_turn setup leaks who event past current.beforeView turn))
        rw [currentSplit]
        change _ ≤ (((app.policyMixture timing family).posterior (past ++ [current])) 0).toReal
        rw [unchanged]
        exact old

private theorem turnFamily_recalled_silence_error
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (before : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (after : List (application setup leaks).PlayerEntry)
    (first : sourceServiceTurn setup leaks who event before entry.beforeView = some 0)
    (silent : entry.action = ⟨none⟩)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      before entry.beforeView) ⟨none⟩).toReal)
    (lawful : ∀ earlier current later, before ++ entry :: after = earlier ++ current :: later →
      current.beforeView.application.publicView.ownTurn? who = some event →
        current.action = ⟨none⟩)
    (current : Fin (turns + 1)) (notFirst : current ≠ 0)
    (view : (application setup leaks).PlayerView)
    (atIndex : sourceServiceTurn setup leaks who event (before ++ entry :: after) view =
      some current.val)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (below : weight < 1)
    (response : (application setup leaks).Action) :
    let app := application setup leaks
    let timing := geometricTurnLaw weight nonnegative below.le turns
    let family := sourceServiceTurnFamily setup leaks bound profile who event turns
    |(((app.policyMixture timing family).policy (before ++ entry :: after) view) response).toReal -
      ((PMF.pure ⟨none⟩) response).toReal| ≤
        weight / ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
          before entry.beforeView) ⟨none⟩).toReal := by
  classical
  dsimp only
  let app := application setup leaks
  let timing := geometricTurnLaw weight nonnegative below.le turns
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let deciding := sourceServiceCanonicalOpportunity setup leaks bound profile who event
    before entry.beforeView
  let quiet := (deciding ⟨none⟩).toReal
  let denominator := (1 - weight) * quiet + weight
  let post := (app.policyMixture timing family).posterior (before ++ entry :: after)
  have more : 0 < turns := by
    have indexPositive : 0 < current.val := by
      by_contra absent
      exact notFirst (Fin.ext (by simp only [Fin.val_zero]; omega))
    omega
  have zeroMass : (timing 0).toReal = 1 - weight := by
    rw [geometricTurnLaw_apply_toReal]
    simp only [Fin.val_zero, more, ↓reduceIte, pow_zero, mul_one]
  have prior := sourceServiceTurnFamily_first_posterior (bound := bound) (profile := profile)
    timing before entry.beforeView first
  have mass : (((app.policyMixture timing family).policy before entry.beforeView)
      entry.action).toReal = denominator := by
    rw [silent, sourceServiceTurnFamily_response_probability timing 0 before entry.beforeView
      first ⟨none⟩]
    rw [prior, zeroMass]
    simp only [ReactiveApplication.silentPolicy, PMF.pure_apply, ↓reduceIte,
      ENNReal.toReal_one]
    change (1 - weight) * quiet + (1 - (1 - weight)) * 1 = denominator
    dsimp only [denominator]
    ring
  have quietBound : quiet ≤ 1 := pmf_toReal_apply_le_one deciding ⟨none⟩
  have lower : quiet ≤ denominator := by
    dsimp only [denominator]
    nlinarith [mul_nonneg (sub_nonneg.mpr quietBound) nonnegative]
  have denominatorPositive : 0 < denominator := lt_of_lt_of_le positive lower
  have possible : entry.action ∈
      ((app.policyMixture timing family).policy before entry.beforeView).support := by
    apply pmf_toReal_pos_iff.mp
    rw [mass]
    exact denominatorPositive
  have firstZero := sourceServiceTurnFamily_posterior_point timing before entry possible 0
  dsimp only at firstZero
  change (((app.policyMixture timing family).posterior (before ++ [entry])) 0).toReal =
    (((app.policyMixture timing family).posterior before) 0).toReal *
      ((family 0 before entry.beforeView) entry.action).toReal /
        (((app.policyMixture timing family).policy before entry.beforeView) entry.action).toReal
      at firstZero
  have selected : family 0 before entry.beforeView = deciding :=
    app.turnScheduledPolicy_selected _ _ _ _ _ _ first
  rw [prior, zeroMass, selected, mass, silent] at firstZero
  change (((app.policyMixture timing family).posterior (before ++ [entry])) 0).toReal =
    (1 - weight) * quiet / denominator at firstZero
  have firstPositive : 0 <
      (((app.policyMixture timing family).posterior (before ++ [entry])) 0).toReal := by
    rw [firstZero]
    exact div_pos (mul_pos (sub_pos.mpr below) positive) denominatorPositive
  have retained := turnFamily_after_first_zero_mono timing before entry first after firstPositive
    lawful
  have deficit : 1 - (((app.policyMixture timing family).posterior
      (before ++ [entry])) 0).toReal ≤ weight / quiet := by
    rw [firstZero]
    calc
      _ = weight / denominator := by
        apply (eq_div_iff (ne_of_gt denominatorPositive)).mpr
        rw [sub_mul, one_mul, div_mul_cancel₀ _ (ne_of_gt denominatorPositive)]
        dsimp only [denominator]
        ring
      _ ≤ _ := div_le_div_of_nonneg_left nonnegative positive lower
  have atoms : (post current).toReal + (post 0).toReal ≤ 1 := by
    rw [← pmf_sum_toReal_eq_one post]
    have two := Finset.sum_le_sum_of_subset_of_nonneg
      (show ({current, 0} : Finset (Fin (turns + 1))) ⊆ Finset.univ by simp)
      (fun index _ _ => show 0 ≤ (post index).toReal from ENNReal.toReal_nonneg)
    simpa only [Finset.sum_insert (show current ∉ ({0} : Finset (Fin (turns + 1))) by
      simpa only [Finset.mem_singleton] using notFirst), Finset.sum_singleton] using two
  have hazard : (post current).toReal ≤ weight / quiet := by
    change _ ≤ (post 0).toReal at retained
    linarith
  exact (sourceServiceTurnFamily_waiting_response_error timing current (before ++ entry :: after)
    view atIndex response).trans hazard

variable [Fintype Player]

/-- Every recalled own turn of an actually unrecorded event was silent at a
legal canonical history, independently of its source likelihood. -/
theorem sourceServiceCanonical_unrecorded_recalled_turn_silent {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (who : Player)
    (middle : (application setup leaks).Execution)
    (trace : ((bounds.canonicalMenu (runtime setup) leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, middle⟩))
    (event : (graph setup).EventId)
    (unrecorded : (runtime setup).eventRecorded leaks (middle.recall who) event = false)
    (before : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (after : List (application setup leaks).PlayerEntry)
    (recalled : middle.recall who = before ++ entry :: after)
    (turn : entry.beforeView.application.publicView.ownTurn? who = some event) :
    entry.action = ⟨none⟩ := by
  classical
  let app := application setup leaks
  let menu := bounds.canonicalMenu (runtime setup) leaks
  let history : (menu.protocol (initialLaw setup) horizon scheduler).History := ⟨_, trace⟩
  have observed : (menu.information (initialLaw setup) horizon scheduler).infoOf who trace =
      some (middle.recall who, middle.observe app who) := by
    change (menu.signals (initialLaw setup) horizon scheduler).infoOf who trace = _
    rw [menu.info]
    simp only [ReactiveApplication.observe, ↓reduceIte]
    rfl
  have indexed : (middle.recall who)[before.length]? = some entry := by rw [recalled]; simp
  have prefixRecall : (middle.recall who).take before.length = before := by rw [recalled]; simp
  have admitted := menu.recorded_response_mem (initialLaw setup) horizon scheduler who history
    _ _ observed before.length entry indexed
  rw [prefixRecall] at admitted
  have entryMember : entry ∈ middle.recall who := by
    rw [recalled]
    exact List.mem_append_right _ List.mem_cons_self
  have neverNamed : (runtime setup).submittedEvent? leaks entry.action ≠ some event := by
    intro named
    have recorded : (runtime setup).eventRecorded leaks (middle.recall who) event = true :=
      List.any_eq_true.mpr ⟨entry, entryMember, decide_eq_true named⟩
    rw [unrecorded] at recorded
    cases recorded
  rcases bounds.canonicalActions_cases (runtime setup) leaks who before entry.beforeView
      entry.action admitted with silent | ⟨other, action, served, _, _, _, _, _, decided⟩
  · exact silent
  · have same : other = event := Option.some.inj (served.symm.trans turn)
    subst other
    rcases (runtime setup).canonicalServiceDecision_cases leaks who before entry.beforeView event
        action with silent | named
    · exact decided.trans silent
    · exact (neverNamed (decided ▸ named)).elim

/-- Every later response at an actual clear unrecorded own event is within
`weight / firstSilent` of silence, using the first actual recalled input.
No protection or equality of source views is required at later turns. -/
theorem sourceServiceTurnPolicy_clear_recalled_silence_error {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (middle : (application setup leaks).Execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, middle⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (middle.recall player) (middle.observe (application setup leaks) player) = false)
    (event : (graph setup).EventId)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (middle.recall who) event = false)
    (before : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (after : List (application setup leaks).PlayerEntry)
    (recalled : middle.recall who = before ++ entry :: after)
    (first : sourceServiceTurn setup leaks who event before entry.beforeView = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
      before entry.beforeView) ⟨none⟩).toReal)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (below : weight < 1)
    (response : (application setup leaks).Action) :
    |((sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight nonnegative below.le) profile who (middle.recall who)
        (middle.observe (application setup leaks) who)) response).toReal -
      ((PMF.pure ⟨none⟩) response).toReal| ≤
        weight / ((sourceServiceCanonicalOpportunity setup leaks bound profile who event
          before entry.beforeView) ⟨none⟩).toReal := by
  classical
  let app := application setup leaks
  let past := middle.recall who
  let view := middle.observe app who
  let count := past.countP fun entry =>
    decide (entry.beforeView.application.publicView.ownTurn? who = some event)
  obtain ⟨canonical, _same⟩ := bounds.riskTrace_canonical_of_persistentClear (runtime setup) leaks
    bound (initialLaw setup) horizon scheduler trace (by
      intro control same player
      cases Option.some.inj same
      exact clear player)
  have lawful : ∀ earlier current later, before ++ entry :: after = earlier ++ current :: later →
      current.beforeView.application.publicView.ownTurn? who = some event →
        current.action = ⟨none⟩ := by
    intro earlier current later split serving
    exact sourceServiceCanonical_unrecorded_recalled_turn_silent bounds who middle canonical event
      unrecorded earlier current later (recalled.trans split) serving
  have silent := sourceServiceCanonical_unrecorded_recalled_turn_silent bounds who middle canonical
    event unrecorded before entry after recalled (sourceServiceTurn_first first).1
  have lengthBound := app.active_recall_lt_horizon (initialLaw setup) horizon scheduler
    ⟨remaining, some who, middle⟩
      ((bounds.riskMenu (runtime setup) leaks bound).toRawTrace _ _ _ trace) who rfl
  have early : count < horizon := lt_of_le_of_lt List.countP_le_length lengthBound
  let current : Fin (horizon + 1) := ⟨count, by omega⟩
  have serving : view.application.publicView.ownTurn? who = some event := turn
  have atIndex : sourceServiceTurn setup leaks who event past view = some current.val := by
    simp only [sourceServiceTurn, serving, ↓reduceIte]
    rfl
  have notFirst : current ≠ 0 := by
    intro equal
    have zero : sourceServiceTurn setup leaks who event past view = some 0 := by
      simpa only [equal, Fin.val_zero] using atIndex
    exact (sourceServiceTurn_first zero).2 entry
      (by
        change entry ∈ middle.recall who
        rw [recalled]
        exact List.mem_append_right _ List.mem_cons_self)
        (sourceServiceTurn_first first).1
  have owned := (PublicView.ownTurn?_spec middle.application.publicView who event turn).2
  rw [sourceServiceTurnPolicy_turn setup leaks bound horizon _ profile who _ _ event owned turn]
  have estimate := turnFamily_recalled_silence_error before entry after first silent positive lawful
    current
    notFirst view (by rw [← recalled]; exact atIndex) weight nonnegative below response
  dsimp only at estimate
  simpa only [geometricTiming, recalled] using estimate

/-- Positive limiting first silence likelihood suffices for every later
actual clear unrecorded response to converge to silence. The likelihood
convergence is explicit and is not inferred from source belief transport. -/
theorem sourceServiceTurnPolicy_clear_recalled_silence_converges {horizon remaining : Nat}
    {scheduler : (application setup leaks).Scheduler}
    (bounds : MessageBounds (graph setup)) (bound : (graph setup).EventId → Nat)
    (reference : BehavioralProfile setup.program)
    (profiles : ℕ → BehavioralProfile setup.program) (who : Player)
    (middle : (application setup leaks).Execution)
    (trace : ((bounds.riskMenu (runtime setup) leaks bound).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, some who, middle⟩))
    (clear : ∀ player, (runtime setup).persistentServiceRisk leaks bound player
      (middle.recall player) (middle.observe (application setup leaks) player) = false)
    (event : (graph setup).EventId)
    (turn : middle.application.publicView.ownTurn? who = some event)
    (unrecorded : (runtime setup).eventRecorded leaks (middle.recall who) event = false)
    (before : List (application setup leaks).PlayerEntry)
    (entry : (application setup leaks).PlayerEntry)
    (after : List (application setup leaks).PlayerEntry)
    (recalled : middle.recall who = before ++ entry :: after)
    (first : sourceServiceTurn setup leaks who event before entry.beforeView = some 0)
    (positive : 0 < ((sourceServiceCanonicalOpportunity setup leaks bound reference who event
      before entry.beforeView) ⟨none⟩).toReal)
    (likelihood : Tendsto (fun n =>
      ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n) who event before
        entry.beforeView) ⟨none⟩).toReal) atTop
          (nhds ((sourceServiceCanonicalOpportunity setup leaks bound reference who event before
            entry.beforeView) ⟨none⟩).toReal))
    (weight : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ weight n) (below : ∀ n, weight n < 1)
    (vanishes : Tendsto weight atTop (nhds 0)) :
    PMFConvergesPointwise (fun n => sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon (weight n) (nonnegative n) (below n).le) (profiles n) who
        (middle.recall who) (middle.observe (application setup leaks) who)) (PMF.pure ⟨none⟩) := by
  have eventuallyPositive := (tendsto_order.mp likelihood).1 0 positive
  have relative : Tendsto (fun n => weight n /
      ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n) who event before
        entry.beforeView) ⟨none⟩).toReal) atTop (nhds 0) := by
    convert vanishes.div likelihood (ne_of_gt positive) using 1
    rw [zero_div]
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro response
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [Real.norm_eq_abs]
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => abs_nonneg _) _ relative
  filter_upwards [eventuallyPositive] with n positiveNow
  exact sourceServiceTurnPolicy_clear_recalled_silence_error bounds bound (profiles n) who middle
    trace clear event turn unrecorded before entry after recalled first positiveNow (weight n)
      (nonnegative n) (below n) response

end Vegas
