/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceResolutionRecallPosterior

/-! # Opening timing when earlier selected silences are rare

Each timing index can be selected only once in actual own recall. At every
earlier named turn its canonical silence likelihood bounds the weight of
that index after the observed silence. Intervening turns for other events
leave the posterior unchanged. The response bound therefore compares rare
selected silences with the geometric mass of reaching the current turn.

The earlier likelihood bounds use the actual recalled inputs. No source-view
equality or downstream source belief transport is inferred.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

private theorem turnFamily_recalled_silence_domination
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (timing : PMF (Fin (turns + 1))) (current : Fin (turns + 1))
    (supported : 0 < (timing current).toReal)
    (quiet : ℝ) (nonnegative : 0 ≤ quiet)
    (past : List (application setup leaks).PlayerEntry)
    (inside : (past.countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event)) ≤ current.val)
    (lawful : ∀ before entry after, past = before ++ entry :: after →
      entry.beforeView.application.publicView.ownTurn? who = some event →
        entry.action = ⟨none⟩ ∧
          ((sourceServiceCanonicalOpportunity setup leaks bound profile who event before
            entry.beforeView) ⟨none⟩).toReal ≤ quiet) :
    let app := application setup leaks
    let family := sourceServiceTurnFamily setup leaks bound profile who event turns
    let post := (app.policyMixture timing family).posterior past
    0 < (post current).toReal ∧
      ∀ slot, (post slot).toReal * (timing current).toReal ≤
        (post current).toReal * (timing slot).toReal *
          (if slot.val < (past.countP fun entry =>
            decide (entry.beforeView.application.publicView.ownTurn? who = some event)) then
            quiet else 1) := by
  classical
  dsimp only
  let app := application setup leaks
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let count := fun entries : List app.PlayerEntry => entries.countP fun entry =>
    decide (entry.beforeView.application.publicView.ownTurn? who = some event)
  revert inside lawful
  induction past using List.reverseRecOn with
  | nil =>
      intro _ _
      refine ⟨supported, ?_⟩
      intro slot
      simp only [ReactiveApplication.policyMixture, ReactiveApplication.Implementation.posterior,
        List.countP_nil, Nat.not_lt_zero, ↓reduceIte, mul_one]
      exact le_of_eq (mul_comm _ _)
  | append_singleton past entry ih =>
      intro inside lawful
      change count (past ++ [entry]) ≤ current.val at inside
      have counted : count (past ++ [entry]) = count past +
          if entry.beforeView.application.publicView.ownTurn? who = some event then 1 else 0 := by
        simp only [count, List.countP_append, List.countP_cons, List.countP_nil,
          decide_eq_true_eq, zero_add]
      have earlier : count past ≤ current.val := by omega
      have earlierLawful : ∀ before earlier after, past = before ++ earlier :: after →
          earlier.beforeView.application.publicView.ownTurn? who = some event →
            earlier.action = ⟨none⟩ ∧
              ((sourceServiceCanonicalOpportunity setup leaks bound profile who event before
                earlier.beforeView) ⟨none⟩).toReal ≤ quiet := by
        intro before earlier after split serving
        apply lawful before earlier (after ++ [entry]) _ serving
        simpa only [List.append_assoc, List.cons_append] using
          congrArg (fun entries => entries ++ [entry]) split
      obtain ⟨priorPositive, priorBound⟩ := ih earlier earlierLawful
      let prior := (app.policyMixture timing family).posterior past
      by_cases turn : entry.beforeView.application.publicView.ownTurn? who = some event
      · obtain ⟨silent, likelihoodBound⟩ := lawful past entry [] (by simp) turn
        have added : count (past ++ [entry]) = count past + 1 := by
          simpa only [turn, ↓reduceIte] using counted
        have currentLater : count past < current.val := by omega
        have atCount : sourceServiceTurn setup leaks who event past entry.beforeView =
            some (count past) := by
          simp only [sourceServiceTurn, turn, ↓reduceIte]
          rfl
        have waiting : family current past entry.beforeView =
            app.silentPolicy past entry.beforeView := by
          apply app.turnScheduledPolicy_unselected
          intro slot same selected
          cases Option.some.inj same
          rw [atCount] at selected
          have equal := Option.some.inj selected
          omega
        have possible : entry.action ∈
            ((app.policyMixture timing family).policy past entry.beforeView).support := by
          apply app.policyMixture_action_support _ _ _ _ current
          · exact pmf_toReal_pos_iff.mp priorPositive
          · rw [waiting, silent]
            exact app.silentPolicy_support _ _
        let mass := (((app.policyMixture timing family).policy past entry.beforeView)
          entry.action).toReal
        have massPositive : 0 < mass := pmf_toReal_pos_iff.mpr possible
        have currentUpdate := sourceServiceTurnFamily_posterior_point timing past entry possible
          current
        dsimp only at currentUpdate
        change (((app.policyMixture timing family).posterior (past ++ [entry]))
          current).toReal = (prior current).toReal *
            ((family current past entry.beforeView) entry.action).toReal / mass at currentUpdate
        rw [waiting, silent] at currentUpdate
        simp only [ReactiveApplication.silentPolicy, PMF.pure_apply, ↓reduceIte,
          ENNReal.toReal_one, mul_one] at currentUpdate
        refine ⟨by rw [currentUpdate]; exact div_pos priorPositive massPositive, ?_⟩
        intro slot
        have update := sourceServiceTurnFamily_posterior_point timing past entry possible slot
        dsimp only at update
        change (((app.policyMixture timing family).posterior (past ++ [entry])) slot).toReal =
          (prior slot).toReal * ((family slot past entry.beforeView) entry.action).toReal / mass
            at update
        have numerator : (prior slot).toReal *
              ((family slot past entry.beforeView) entry.action).toReal *
                (timing current).toReal ≤
            (prior current).toReal * (timing slot).toReal *
              (if slot.val < count (past ++ [entry]) then quiet else 1) := by
          by_cases selected : slot.val = count past
          · have deciding : family slot past entry.beforeView =
                sourceServiceCanonicalOpportunity setup leaks bound profile who event past
                  entry.beforeView :=
              app.turnScheduledPolicy_selected _ _ _ _ _ _ (by rw [selected]; exact atCount)
            have previous := priorBound slot
            change (prior slot).toReal * (timing current).toReal ≤
              (prior current).toReal * (timing slot).toReal *
                (if slot.val < count past then quiet else 1) at previous
            simp only [selected, lt_self_iff_false, ↓reduceIte, mul_one] at previous
            rw [deciding, silent, ite_eq_left (by omega)]
            calc
              _ = ((sourceServiceCanonicalOpportunity setup leaks bound profile who event past
                  entry.beforeView) ⟨none⟩).toReal *
                    ((prior slot).toReal * (timing current).toReal) := by ring
              _ ≤ quiet * ((prior current).toReal * (timing slot).toReal) :=
                mul_le_mul likelihoodBound previous (mul_nonneg ENNReal.toReal_nonneg
                  ENNReal.toReal_nonneg) nonnegative
              _ = _ := by ring
          · have waitingSlot : family slot past entry.beforeView =
                app.silentPolicy past entry.beforeView := by
              apply app.turnScheduledPolicy_unselected
              intro other same chosen
              cases Option.some.inj same
              rw [atCount] at chosen
              exact selected (Option.some.inj chosen).symm
            have sameFactor : (slot.val < count (past ++ [entry])) ↔ slot.val < count past := by
              omega
            rw [waitingSlot, silent]
            simp only [ReactiveApplication.silentPolicy, PMF.pure_apply, ↓reduceIte,
              ENNReal.toReal_one, mul_one, sameFactor]
            exact priorBound slot
        rw [update, currentUpdate]
        calc
          _ = ((prior slot).toReal *
              ((family slot past entry.beforeView) entry.action).toReal *
                (timing current).toReal) / mass := by ring
          _ ≤ ((prior current).toReal * (timing slot).toReal *
              (if slot.val < count (past ++ [entry]) then quiet else 1)) / mass :=
            div_le_div_of_nonneg_right numerator massPositive.le
          _ = _ := by ring
      · have unchanged : count (past ++ [entry]) = count past := by
          simpa only [turn, ↓reduceIte, Nat.add_zero] using counted
        dsimp only [count] at unchanged
        have update := app.policyMixture_posterior_snoc timing family past entry
          (app.silentPolicy past entry.beforeView) (fun slot =>
            app.turnScheduledPolicy_of_none _ _ _ _ _ _
              (sourceServiceTurn_of_not_turn setup leaks who event past entry.beforeView turn))
        rw [update]
        refine ⟨priorPositive, ?_⟩
        intro slot
        change (prior slot).toReal * (timing current).toReal ≤
          (prior current).toReal * (timing slot).toReal *
            (if slot.val < count (past ++ [entry]) then quiet else 1)
        rw [show count (past ++ [entry]) = count past from unchanged]
        exact priorBound slot

private theorem turnFamily_recalled_decision_error
    {bound : (graph setup).EventId → Nat} {turns : Nat}
    {profile : BehavioralProfile setup.program} {who : Player}
    {event : (graph setup).EventId}
    (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView)
    (current : Fin (turns + 1)) (early : current.val < turns)
    (counted : (past.countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event)) = current.val)
    (atIndex : sourceServiceTurn setup leaks who event past view = some current.val)
    (quiet : ℝ) (nonnegative : 0 ≤ quiet)
    (lawful : ∀ before entry after, past = before ++ entry :: after →
      entry.beforeView.application.publicView.ownTurn? who = some event →
        entry.action = ⟨none⟩ ∧
          ((sourceServiceCanonicalOpportunity setup leaks bound profile who event before
            entry.beforeView) ⟨none⟩).toReal ≤ quiet)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (response : (application setup leaks).Action) :
    let app := application setup leaks
    let timing := geometricTurnLaw weight positive.le below.le turns
    let family := sourceServiceTurnFamily setup leaks bound profile who event turns
    |(((app.policyMixture timing family).policy past view) response).toReal -
      ((sourceServiceCanonicalOpportunity setup leaks bound profile who event past view)
        response).toReal| ≤ weight + quiet / weight ^ current.val := by
  classical
  dsimp only
  let app := application setup leaks
  let timing := geometricTurnLaw weight positive.le below.le turns
  let family := sourceServiceTurnFamily setup leaks bound profile who event turns
  let post := (app.policyMixture timing family).posterior past
  have currentMass : (timing current).toReal = (1 - weight) * weight ^ current.val := by
    rw [geometricTurnLaw_apply_toReal, ite_eq_left early]
  have massPositive : 0 < (timing current).toReal := by
    rw [currentMass]
    exact mul_pos (sub_pos.mpr below) (pow_pos positive _)
  obtain ⟨_postPositive, points⟩ := turnFamily_recalled_silence_domination timing current
    massPositive quiet nonnegative past counted.le lawful
  have tail : (∑ slot : Fin (turns + 1),
      if current.val ≤ slot.val then (timing slot).toReal else 0) = weight ^ current.val := by
    simpa only [Finset.sum_filter] using geometricTurnLaw_tail_toReal weight positive.le below.le
      turns current.val early.le
  have factors : (∑ slot : Fin (turns + 1),
      (timing slot).toReal * (if slot.val < current.val then quiet else 1)) ≤
        quiet + weight ^ current.val := by
    calc
      _ ≤ ∑ slot : Fin (turns + 1),
          ((timing slot).toReal * quiet +
            if current.val ≤ slot.val then (timing slot).toReal else 0) := by
        apply Finset.sum_le_sum
        intro slot _
        by_cases old : slot.val < current.val
        · simp only [old, Nat.not_le.mpr old, ↓reduceIte, add_zero]
          exact le_rfl
        · simp only [old, Nat.le_of_not_gt old, ↓reduceIte, mul_one]
          linarith [mul_nonneg (show 0 ≤ (timing slot).toReal from ENNReal.toReal_nonneg)
            nonnegative]
      _ = _ := by
        rw [Finset.sum_add_distrib, ← Finset.sum_mul, pmf_sum_toReal_eq_one, one_mul, tail]
  have total : (timing current).toReal ≤ (post current).toReal *
      (quiet + weight ^ current.val) := by
    calc
      _ = ∑ slot : Fin (turns + 1), (post slot).toReal * (timing current).toReal := by
        rw [← Finset.sum_mul, pmf_sum_toReal_eq_one, one_mul]
      _ ≤ ∑ slot : Fin (turns + 1), (post current).toReal * (timing slot).toReal *
          (if slot.val < current.val then quiet else 1) := by
        apply Finset.sum_le_sum
        intro slot _
        simpa only [counted] using points slot
      _ = (post current).toReal * ∑ slot : Fin (turns + 1),
          (timing slot).toReal * (if slot.val < current.val then quiet else 1) := by
        simp only [Finset.mul_sum, mul_assoc]
      _ ≤ _ := mul_le_mul_of_nonneg_left factors ENNReal.toReal_nonneg
  have deficit : 1 - (post current).toReal ≤ weight + quiet / weight ^ current.val := by
    rw [currentMass] at total
    have algebra : weight + quiet / weight ^ current.val =
        (weight * weight ^ current.val + quiet) / weight ^ current.val := by
      field_simp
    rw [algebra]
    apply (le_div_iff₀ (pow_pos positive current.val)).mpr
    have bound := pmf_toReal_apply_le_one post current
    have loss := mul_le_of_le_one_left nonnegative bound
    nlinarith
  exact (sourceServiceTurnFamily_response_error timing current past view atIndex response).trans
    deficit

variable [Fintype Player]

/-- An actual clear unsent turn is close to deciding now when every earlier
selected silence likelihood is bounded by `quiet`. The bound uses the actual
turn count: `weight + quiet / weight ^ count`. -/
theorem sourceServiceTurnPolicy_clear_recalled_decision_error {horizon remaining : Nat}
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
    (quiet : ℝ) (nonnegative : 0 ≤ quiet)
    (likelihoods : ∀ before entry after, middle.recall who = before ++ entry :: after →
      entry.beforeView.application.publicView.ownTurn? who = some event →
        ((sourceServiceCanonicalOpportunity setup leaks bound profile who event before
          entry.beforeView) ⟨none⟩).toReal ≤ quiet)
    (weight : ℝ) (positive : 0 < weight) (below : weight < 1)
    (response : (application setup leaks).Action) :
    |((sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon weight positive.le below.le) profile who (middle.recall who)
        (middle.observe (application setup leaks) who)) response).toReal -
      ((sourceServiceCanonicalOpportunity setup leaks bound profile who event (middle.recall who)
        (middle.observe (application setup leaks) who)) response).toReal| ≤
      weight + quiet / weight ^ ((middle.recall who).countP fun entry =>
        decide (entry.beforeView.application.publicView.ownTurn? who = some event)) := by
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
  have lawful : ∀ before entry after, past = before ++ entry :: after →
      entry.beforeView.application.publicView.ownTurn? who = some event →
        entry.action = ⟨none⟩ ∧
          ((sourceServiceCanonicalOpportunity setup leaks bound profile who event before
            entry.beforeView) ⟨none⟩).toReal ≤ quiet := by
    intro before entry after recalled serving
    exact ⟨sourceServiceCanonical_unrecorded_recalled_turn_silent bounds who middle canonical
      event unrecorded before entry after recalled serving,
        likelihoods before entry after recalled serving⟩
  have lengthBound := app.active_recall_lt_horizon (initialLaw setup) horizon scheduler
    ⟨remaining, some who, middle⟩
      ((bounds.riskMenu (runtime setup) leaks bound).toRawTrace _ _ _ trace) who rfl
  have early : count < horizon := lt_of_le_of_lt List.countP_le_length lengthBound
  let current : Fin (horizon + 1) := ⟨count, by omega⟩
  have atIndex : sourceServiceTurn setup leaks who event past view = some current.val := by
    simp only [sourceServiceTurn, show view.application.publicView.ownTurn? who = some event
      from turn, ↓reduceIte]
    rfl
  have owned := (PublicView.ownTurn?_spec middle.application.publicView who event turn).2
  rw [sourceServiceTurnPolicy_turn setup leaks bound horizon _ profile who _ _ event owned turn]
  exact turnFamily_recalled_decision_error past view current early rfl atIndex quiet nonnegative
    lawful weight positive below response

/-- Rare selected silence relative to the mass of reaching this actual turn
makes the physical policy converge to its reference canonical decision law.
Convergence of that law is explicit; no source-view transport is assumed. -/
theorem sourceServiceTurnPolicy_clear_recalled_decision_converges {horizon remaining : Nat}
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
    (quiet : ℕ → ℝ) (nonnegative : ∀ n, 0 ≤ quiet n)
    (likelihoods : ∀ n before entry after, middle.recall who = before ++ entry :: after →
      entry.beforeView.application.publicView.ownTurn? who = some event →
        ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n) who event before
          entry.beforeView) ⟨none⟩).toReal ≤ quiet n)
    (weight : ℕ → ℝ) (positive : ∀ n, 0 < weight n) (below : ∀ n, weight n < 1)
    (vanishes : Tendsto weight atTop (nhds 0))
    (relative : Tendsto (fun n => quiet n / weight n ^ ((middle.recall who).countP fun entry =>
      decide (entry.beforeView.application.publicView.ownTurn? who = some event))) atTop (nhds 0))
    (canonical : PMFConvergesPointwise (fun n => sourceServiceCanonicalOpportunity setup leaks
      bound (profiles n) who event (middle.recall who)
        (middle.observe (application setup leaks) who))
          (sourceServiceCanonicalOpportunity setup leaks bound reference who event
            (middle.recall who) (middle.observe (application setup leaks) who))) :
    PMFConvergesPointwise (fun n => sourceServiceTurnPolicy setup leaks bound horizon
      (geometricTiming setup horizon (weight n) (positive n).le (below n).le) (profiles n) who
        (middle.recall who) (middle.observe (application setup leaks) who))
      (sourceServiceCanonicalOpportunity setup leaks bound reference who event (middle.recall who)
        (middle.observe (application setup leaks) who)) := by
  apply pmfConvergesPointwise_iff_toReal.mpr
  intro response
  have error : Tendsto (fun n =>
      ((sourceServiceTurnPolicy setup leaks bound horizon
        (geometricTiming setup horizon (weight n) (positive n).le (below n).le) (profiles n) who
          (middle.recall who) (middle.observe (application setup leaks) who)) response).toReal -
        ((sourceServiceCanonicalOpportunity setup leaks bound (profiles n) who event
          (middle.recall who) (middle.observe (application setup leaks) who)) response).toReal)
            atTop (nhds 0) := by
    apply squeeze_zero_norm _ (by simpa only [zero_add] using vanishes.add relative)
    intro n
    rw [Real.norm_eq_abs]
    exact sourceServiceTurnPolicy_clear_recalled_decision_error bounds bound (profiles n) who
      middle trace clear event turn unrecorded (quiet n) (nonnegative n) (likelihoods n)
        (weight n) (positive n) (below n) response
  have current := (pmfConvergesPointwise_iff_toReal.mp canonical) response
  simpa only [sub_add_cancel, zero_add] using error.add current

end Vegas
