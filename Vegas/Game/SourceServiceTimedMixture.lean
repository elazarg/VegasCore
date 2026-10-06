/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedCompletion
import Vegas.Game.SourceServiceFirstTurnMixture

/-! # Timed canonical clients as mixtures over source actions

A timed canonical client acts at each of its own turns, with the probability
its timing gives the input, by following the compiled source decision, until
its recall has submitted for the event; otherwise it is silent
(`Vegas.timedCanonicalPolicy`). The timing may depend on everything the
client has seen.

At a completion boundary the source decision is one law over source actions,
because the configuration does not change before the event completes. When
every action in its support transmits (no disclosure of `false`), the timed
client runs, whatever the other players do, as the mixture under that law of
the policies that decide one fixed action with the same timing
(`Vegas.timedCanonical_runUntil_mixture`): a silent response at a turn has the
same probability under every action, so it does not update the latent action,
and after the submission the client is silent. This is where the timing may
not see the drawn action: a disclosure of `false` is silence, and a client that
redraws after it would bias the law of the action finally submitted.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- A timing: at each input, the law of acting now. -/
abbrev ResponseTiming : Type :=
  List (application setup leaks).PlayerEntry → (application setup leaks).PlayerView → PMF Bool

/-- Decide `action` at `event` with the given timing: at an own turn at `event`
with no submission for the event in the recall, act with the timing's law,
acting being the compiled decision of `action`; be silent otherwise. -/
def timedDecidedPolicy (timing : ResponseTiming setup leaks) (owner : Player)
    (event : (graph setup).EventId) (action : (graph setup).Action event) :
    (application setup leaks).Policy := fun past view =>
  if view.application.publicView.ownTurn? owner = some event ∧
      (runtime setup).eventRecorded leaks past event = false then
    (timing past view).bind fun act =>
      if act then PMF.pure ((runtime setup).canonicalServiceDecision leaks owner past view event
        action)
      else (application setup leaks).silentPolicy past view
  else (application setup leaks).silentPolicy past view

/-- **The timed canonical client.** At an own turn whose event its recall has
not submitted for, act with the timing's law by following the compiled source
decision of `profile`; be silent otherwise. -/
def timedCanonicalPolicy (timing : Player → ResponseTiming setup leaks)
    (profile : BehavioralProfile setup.program) (who : Player) :
    (application setup leaks).Policy := fun past view =>
  match view.application.publicView.ownTurn? who with
  | none => (application setup leaks).silentPolicy past view
  | some event =>
      if (runtime setup).eventRecorded leaks past event = false then
        (timing who past view).bind fun act =>
          if act then sourceServiceCanonicalPolicy setup leaks profile who past view
          else (application setup leaks).silentPolicy past view
      else (application setup leaks).silentPolicy past view

variable {setup leaks}

/-- Deciding a fixed action with a timing decides it with some timing. -/
theorem timedDecidedPolicy_decidesWithTiming (timing : ResponseTiming setup leaks)
    (owner : Player) (event : (graph setup).EventId) (action : (graph setup).Action event) :
    DecidesWithTiming (timedDecidedPolicy setup leaks timing owner event action) owner event
      action := by
  intro past view response chosen
  unfold timedDecidedPolicy at chosen
  split at chosen
  · rename_i turn
    obtain ⟨act, _, member⟩ := (PMF.mem_support_bind_iff _ _ _).mp chosen
    cases act with
    | false =>
        simp only [Bool.false_eq_true, ↓reduceIte] at member
        exact Or.inl ((application setup leaks).silentPolicy_cases past view response member)
    | true =>
        simp only [↓reduceIte, PMF.mem_support_pure_iff] at member
        exact Or.inr ⟨turn.1, turn.2, member⟩
  · exact Or.inl ((application setup leaks).silentPolicy_cases past view response chosen)

/-- An own turn during the phase of `event` is a turn at `event`. -/
private theorem ownTurn_eq_of_ready {state : EventGraphRuntime.State (graph setup)}
    {event : (graph setup).EventId} (ready : state.config.cut.Ready event) {who : Player}
    {other : (graph setup).EventId} (turn : state.publicView.ownTurn? who = some other) :
    other = event :=
  (soleReady_of_ready setup state ready).2 other (PublicView.ownTurn?_spec _ who other turn).1

/-- **Timed canonical clients as mixtures.** From a completion boundary of any
players, if the source decision at the boundary configuration is `law`
compiled to native responses and every action in its support is effective and
transmits, the owner's timed canonical client runs, whatever the other players
do, as the `law`-mixture of the policies deciding one fixed action with the
same timing. -/
theorem timedCanonical_runUntil_mixture {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler}
    {reachers : Player → (application setup leaks).Policy} (event : (graph setup).EventId)
    (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler reachers event.val start)
    (owner : Player) (owned : (graph setup).actor? event = some owner)
    (timing : Player → ResponseTiming setup leaks) (profile : BehavioralProfile setup.program)
    (law : PMF ((graph setup).Action event))
    (policy : ∀ current : (application setup leaks).Execution,
      current.application.config = start.application.config →
      sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
          (current.observe (application setup leaks) owner) =
        law.map fun action => (runtime setup).canonicalServiceDecision leaks owner
          (current.recall owner) (current.observe (application setup leaks) owner) event action)
    (loud : ∀ action ∈ law.support, ¬ SilentAction event action)
    (effective : ∀ action ∈ law.support,
      EffectiveAction start.application.config event action)
    (others : Player → (application setup leaks).Policy) :
    ∀ (count remaining : Nat),
      ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining + count, none, start⟩) →
      (application setup leaks).runUntil scheduler
          (Function.update others owner (timedCanonicalPolicy setup leaks timing profile owner))
          (fun final => event ∈ final.application.config.cut.completed) count start =
        law.bind fun action => (application setup leaks).runUntil scheduler
          (Function.update others owner
            (timedDecidedPolicy setup leaks (timing owner) owner event action))
          (fun final => event ∈ final.application.config.cut.completed) count start := by
  intro count remaining startTrace
  let app := application setup leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let member := fun action => timedDecidedPolicy setup leaks (timing owner) owner event action
  let mixture := app.policyMixture law member
  let client := timedCanonicalPolicy setup leaks timing profile owner
  obtain ⟨rank, ranked, seen⟩ := roundsFrom_ranked setup leaks scheduler reachers _ start
    boundary.supported
  have rankEq := isPrefix_unique ranked boundary.ordered
  subst rankEq
  have ready : start.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
  -- Every member is silent away from an unrecorded own turn at the event.
  have memberSilent (action : (graph setup).Action event)
      (past : List app.PlayerEntry) (view : app.PlayerView)
      (away : ¬ (view.application.publicView.ownTurn? owner = some event ∧
        (runtime setup).eventRecorded leaks past event = false)) :
      member action past view = app.silentPolicy past view := by
    simp only [member, timedDecidedPolicy]
    exact ite_eq_right away
  -- The compiled decision of every action of the law transmits at a phase input.
  have transmits {remaining' : Nat} {middle : app.Execution}
      (middleTrace : (app.protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining', some owner, middle⟩))
      (same : middle.application.config = start.application.config)
      (action : (graph setup).Action event) (chosen : action ∈ law.support) :
      (runtime setup).canonicalServiceDecision leaks owner (middle.recall owner)
        (middle.observe app owner) event action ≠ ⟨none⟩ := by
    have readyMiddle : middle.application.config.cut.Ready event := by rw [same]; exact ready
    obtain ⟨_, invariant⟩ := (roster_trace_facts setup leaks horizon scheduler middleTrace).1
    obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor event readyMiddle
      (by rw [owned]; rfl)
    obtain ⟨material, decision, _⟩ := canonicalServiceDecision_submits (bound := fun _ => 0)
      middleTrace event owned readyMiddle entered activated action
      (by rw [same]; exact effective action chosen) (loud action chosen)
    rw [decision]
    exact fun equal => by cases equal
  let PosteriorReady := fun current : app.Execution =>
    (runtime setup).eventRecorded leaks (current.recall owner) event = true ∨
      mixture.posterior (current.recall owner) = law
  let invariant := fun current : app.Execution =>
    ReadySeen setup leaks event.val current ∧
      (current.application.config = start.application.config ∨
        current.application.config.cut.IsPrefix (event.val + 1)) ∧
      (current.application.config = start.application.config → PosteriorReady current)
  have sameOf (current : app.Execution) (holds : invariant current) (running : ¬ stop current) :
      current.application.config = start.application.config := by
    rcases holds.2.1 with same | advanced
    · exact same
    · exact (running ((advanced.2 event).mpr (Nat.lt_succ_self _))).elim
  have prior : mixture.posterior (start.recall owner) = law := by
    apply app.policyMixture_posterior_of_agree _ _ app.silentPolicy
    intro before entry entryMember action
    apply memberSilent
    rintro ⟨turn, _⟩
    have inRecall : entry ∈ start.recall owner :=
      entryMember.subset (List.mem_append_right _ (List.mem_singleton_self _))
    exact boundary.untouched event rfl owner entry inRecall
      (PublicView.ownTurn?_spec _ owner event turn).1
  have congruent : app.runUntil scheduler (Function.update others owner client) stop count start =
      app.runUntil scheduler (Function.update others owner mixture.policy) stop count start := by
    refine app.runUntil_congr_of_agree_on_traces (initialLaw setup) horizon scheduler _ _ stop
      invariant ?_ ?_ count remaining start startTrace
      ⟨seen, Or.inl rfl, fun _ => Or.inr prior⟩
    · intro remaining' current currentTrace holds running command selected middle moved who
        active
      cases command with
      | «include» _ => cases active
      | application _ => cases active
      | wait => cases active
      | activate actor =>
          have actorEq : actor = who := Option.some.inj active
          subst actorEq
          by_cases isOwner : actor = owner
          swap
          · simp only [Function.update_of_ne isOwner]
          subst isOwner
          simp only [Function.update_self]
          have sameApp := activation_application setup leaks current middle actor moved
          have same : middle.application.config = start.application.config := by
            rw [sameApp]
            exact sameOf current holds running
          have readyMiddle : middle.application.config.cut.Ready event := by
            rw [same]; exact ready
          have recallEq := app.environmentStep_recall current middle _ moved
          rw [app.policyMixture_policy]
          cases turn : (middle.observe app actor).application.publicView.ownTurn? actor with
          | none =>
              have quiet : client (middle.recall actor) (middle.observe app actor) =
                  app.silentPolicy (middle.recall actor) (middle.observe app actor) := by
                simp only [client, timedCanonicalPolicy, turn]
                rfl
              rw [quiet]
              exact ((bind_congr_on_support _ fun index _ => memberSilent index _ _
                (fun both => by rw [turn] at both; cases both.1)).trans
                  (PMF.bind_const _ _)).symm
          | some other =>
              have otherEq : other = event := ownTurn_eq_of_ready readyMiddle turn
              subst otherEq
              by_cases recorded : (runtime setup).eventRecorded leaks (middle.recall actor)
                  other = true
              · have quiet : client (middle.recall actor) (middle.observe app actor) =
                    app.silentPolicy (middle.recall actor) (middle.observe app actor) := by
                  simp only [client, timedCanonicalPolicy, turn, recorded, Bool.true_eq_false,
                    ↓reduceIte]
                  rfl
                rw [quiet]
                exact ((bind_congr_on_support _ fun index _ => memberSilent index _ _
                  (fun both => by rw [recorded] at both; cases both.2)).trans
                    (PMF.bind_const _ _)).symm
              · have unrecorded : (runtime setup).eventRecorded leaks (middle.recall actor)
                    other = false := by simpa using recorded
                have posterior : mixture.posterior (middle.recall actor) = law := by
                  rcases holds.2.2 (sameOf current holds running) with done | atLaw
                  · rw [recallEq] at recorded
                    exact (recorded done).elim
                  · rw [recallEq]
                    exact atLaw
                rw [posterior]
                have acting : client (middle.recall actor) (middle.observe app actor) =
                    (timing actor (middle.recall actor) (middle.observe app actor)).bind
                      fun act => if act then law.map fun action =>
                          (runtime setup).canonicalServiceDecision leaks actor (middle.recall actor)
                            (middle.observe app actor) other action
                        else app.silentPolicy (middle.recall actor) (middle.observe app actor) := by
                  simp only [client, timedCanonicalPolicy, turn, unrecorded, ↓reduceIte]
                  rw [policy middle same]
                rw [acting]
                have members (action : (graph setup).Action other) :
                    member action (middle.recall actor) (middle.observe app actor) =
                      (timing actor (middle.recall actor) (middle.observe app actor)).bind
                        fun act => if act then PMF.pure
                          ((runtime setup).canonicalServiceDecision leaks actor
                            (middle.recall actor) (middle.observe app actor) other action)
                          else app.silentPolicy (middle.recall actor) (middle.observe app actor) :=
                  ite_eq_left_iff.mpr fun away => (away ⟨turn, unrecorded⟩).elim
                refine Eq.symm ((bind_congr_on_support _ fun action _ => members action).trans ?_)
                rw [PMF.bind_comm]
                refine bind_congr_on_support _ fun act _ => ?_
                cases act with
                | false => exact PMF.bind_const _ _
                | true => exact PMF.bind_pure_comp _ _
    · intro remaining' current currentTrace holds running next reached
      have same := sameOf current holds running
      obtain ⟨nextSeen, nextConfig⟩ := round_prefix setup leaks scheduler _ event.val current
        next (by rw [same]; exact boundary.ordered) holds.1 reached
      refine ⟨nextSeen, ?_, ?_⟩
      · rcases nextConfig with stays | advanced
        · exact Or.inl (stays.trans same)
        · exact Or.inr advanced
      intro _
      have before := holds.2.2 same
      obtain ⟨command, selected, middle, moved, cases⟩ := round_cases setup leaks reached
      have recallEq := app.environmentStep_recall current middle command moved
      rcases cases with ⟨_, rfl⟩ | ⟨who, active, response, chosen, rfl⟩
      · simp only [PosteriorReady]
        rw [recallEq]
        exact before
      by_cases isOwner : who = owner
      swap
      · have ownerRecall : (middle.respond app who response).recall owner =
            current.recall owner := by
          rw [app.respond_recall_other middle who owner (Ne.symm isOwner) response, recallEq]
        simp only [PosteriorReady]
        rw [ownerRecall]
        exact before
      subst isOwner
      have activate : command = .activate who := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst activate
      simp only [Function.update_self] at chosen
      obtain ⟨emitted, recalled, _⟩ := respond_recall_self setup leaks middle who response
      have sameApp := activation_application setup leaks current middle who moved
      have sameMiddle : middle.application.config = start.application.config := by
        rw [sameApp]; exact same
      have readyMiddle : middle.application.config.cut.Ready event := by
        rw [sameMiddle]; exact ready
      obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
        remaining' current middle (.activate who) currentTrace selected moved
      simp only [PosteriorReady]
      rw [recalled]
      rcases before with done | atLaw
      · left
        rw [← recallEq] at done
        simp only [EventGraphRuntime.eventRecorded, List.any_append, Bool.or_eq_true] at done ⊢
        exact Or.inl done
      by_cases recordedMiddle : (runtime setup).eventRecorded leaks (middle.recall who) event = true
      · left
        simp only [EventGraphRuntime.eventRecorded, List.any_append,
          Bool.or_eq_true] at recordedMiddle ⊢
        exact Or.inl recordedMiddle
      have unrecorded : (runtime setup).eventRecorded leaks (middle.recall who) event = false := by
        simpa using recordedMiddle
      -- The response is silence or a submission for the event.
      cases turn : (middle.observe app who).application.publicView.ownTurn? who with
      | none =>
          have quiet : client (middle.recall who) (middle.observe app who) =
              app.silentPolicy (middle.recall who) (middle.observe app who) := by
            simp only [client, timedCanonicalPolicy, turn]
            rfl
          rw [quiet] at chosen
          have silent := app.silentPolicy_cases _ _ _ chosen
          subst silent
          right
          rw [app.policyMixture_posterior_snoc_of_likelihood law member _ _ 1 (fun action _ => by
            change member action (middle.recall who) (middle.observe app who) ⟨none⟩ = 1
            rw [memberSilent _ _ _ (fun both => by rw [turn] at both; cases both.1)]
            exact PMF.pure_apply_self _) one_ne_zero, recallEq]
          exact atLaw
      | some other =>
          have otherEq : other = event := ownTurn_eq_of_ready readyMiddle turn
          subst otherEq
          have acting : client (middle.recall who) (middle.observe app who) =
              (timing who (middle.recall who) (middle.observe app who)).bind
                fun act => if act then law.map fun action =>
                    (runtime setup).canonicalServiceDecision leaks who (middle.recall who)
                      (middle.observe app who) other action
                  else app.silentPolicy (middle.recall who) (middle.observe app who) := by
            simp only [client, timedCanonicalPolicy, turn, unrecorded, ↓reduceIte]
            rw [policy middle sameMiddle]
          rw [acting] at chosen
          obtain ⟨act, actChosen, inBranch⟩ := (PMF.mem_support_bind_iff _ _ _).mp chosen
          cases act with
          | true =>
              simp only [↓reduceIte] at inBranch
              obtain ⟨action, actionChosen, decided⟩ := (PMF.mem_support_map_iff _ _ _).mp inBranch
              left
              simp only [EventGraphRuntime.eventRecorded, List.any_append, Bool.or_eq_true,
                List.any_cons, List.any_nil, Bool.or_false, decide_eq_true_eq]
              right
              rw [← decided]
              obtain ⟨_, invariant⟩ :=
                (roster_trace_facts setup leaks horizon scheduler middleTrace).1
              obtain ⟨entered, activated⟩ := invariant.activatedAt_eq_some_of_ready_actor other
                readyMiddle (by rw [owned]; rfl)
              obtain ⟨material, decision, _, realized⟩ := canonicalServiceDecision_submits
                (bound := fun _ => 0) middleTrace other owned readyMiddle entered activated action
                (by rw [sameMiddle]; exact effective action actionChosen)
                (loud action actionChosen)
              rw [decision]
              exact (issued_submittedEvent
                (entry := ⟨middle.observe app who, ⟨some material⟩, none⟩) rfl rfl).trans
                  realized.addressed
          | false =>
              simp only [Bool.false_eq_true, ↓reduceIte] at inBranch
              have silent := app.silentPolicy_cases _ _ _ inBranch
              subst silent
              right
              have falseMass : timing who (middle.recall who) (middle.observe app who) false ≠ 0 :=
                (PMF.mem_support_iff _ _).mp actChosen
              rw [app.policyMixture_posterior_snoc_of_likelihood law member _ _
                (timing who (middle.recall who) (middle.observe app who) false)
                (fun action actionChosen => by
                  rw [recallEq, atLaw] at actionChosen
                  have loudNow := transmits middleTrace sameMiddle action actionChosen
                  have memberEq : member action (middle.recall who) (middle.observe app who) =
                      (timing who (middle.recall who) (middle.observe app who)).bind fun act =>
                        if act then PMF.pure ((runtime setup).canonicalServiceDecision leaks who
                          (middle.recall who) (middle.observe app who) other action)
                        else app.silentPolicy (middle.recall who) (middle.observe app who) :=
                    ite_eq_left_iff.mpr fun away => (away ⟨turn, unrecorded⟩).elim
                  have zeroTrue : (PMF.pure ((runtime setup).canonicalServiceDecision leaks who
                      (middle.recall who) (middle.observe app who) other action) :
                        PMF app.Action) ⟨none⟩ = 0 := by
                    rw [PMF.pure_apply]
                    exact ite_eq_right (Ne.symm loudNow)
                  change member action (middle.recall who) (middle.observe app who) ⟨none⟩ = _
                  rw [memberEq, PMF.bind_apply, tsum_bool]
                  simp only [Bool.false_eq_true, ↓reduceIte]
                  rw [zeroTrue, mul_zero, add_zero]
                  exact (congrArg _ (PMF.pure_apply_self _)).trans (mul_one _)) falseMass, recallEq]
              exact atLaw
  change app.runUntil scheduler (Function.update others owner client) stop count start = _
  rw [congruent, ← app.runUntil_policyMixture scheduler law member owner _ stop count start]
  change (mixture.posterior (start.recall owner)).bind _ = _
  rw [prior]

end Vegas
