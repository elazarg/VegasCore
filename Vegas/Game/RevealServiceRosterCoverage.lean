/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterSupport

/-! # The prescribed roster policy uses exactly retained responses

The proof concerns every prefix produced by arbitrary retained policies.
Together with positivity of all retained responses, it permits finite-menu
restriction without changing or renormalizing the physical policy.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup))
  (rosters : (graph setup).EventId → List Player)

/-- A finite bound covers the actual raw canonical response, including its
matching certificate request, at every local input. -/
theorem roster_opening_raw_available
    (event : (graph setup).EventId) (candidate : Handle (graph setup)) (raw : Raw L)
    (handle : bounds.AllowsHandle candidate) (value : raw ∈ bounds.values)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) :
    (runtime setup).windowOpening leaks event candidate raw ∈
      (bounds.rawMenu (runtime setup) leaks).actions who past view := by
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  apply (bounds.submissions_mem _ _).mpr
  exact ⟨⟨⟨handle, value⟩, True.intro⟩, ⟨handle, value⟩⟩

theorem roster_owner_coverage
    (initial : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (granted : initial.application.serviceGrant = some event)
    (ownedEvent : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (owned : candidate.1 = owner)
    (valid : initial.application.candidates.lookup candidate = .openable raw)
    (offset : (initial.recall owner).length = rosterOffset setup rosters owner event)
    (serials : initial.network.SerialsBeforeNext)
    (published : initial.network.Satisfies fun message =>
      message.id ∈ initial.network.ledger.map Message.id)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who history view response, response ∈ (players who history view).support →
      response ∈ rosterActions setup leaks bounds rosters who history view)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (inside : visits.count owner < (rosters event).count owner)
    (current : (application setup leaks).Execution)
    (reached : current ∈ ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player) initial).support)
    (sample : Finset (MessageId Player))
    (choices : FinDist (Option (Fin ((rosters event).count owner)))) (full : choices.FullSupport)
    (available : (runtime setup).windowOpening leaks event candidate raw ∈
      (bounds.rawMenu (runtime setup) leaks).actions owner (current.recall owner)
        ((current.sampledActivation (application setup leaks) owner sample).observe
          (application setup leaks) owner))
    (action : (application setup leaks).Action)
    (supported : action ∈ (((application setup leaks).policyMixture choices (fun selected =>
      (application setup leaks).scheduledPolicy (rosterOffset setup rosters owner event) selected
        (fun _ _ => FinDist.pure ((runtime setup).windowOpening leaks event candidate raw))
        (application setup leaks).replayPolicy)).policy (current.recall owner)
      ((current.sampledActivation (application setup leaks) owner sample).observe
        (application setup leaks) owner)).support) :
    action ∈ rosterActions setup leaks bounds rosters owner (current.recall owner)
      ((current.sampledActivation (application setup leaks) owner sample).observe
        (application setup leaks) owner) := by
  classical
  let app := application setup leaks
  let activated := current.sampledActivation app owner sample
  let view := activated.observe app owner
  let packet := (runtime setup).windowOpening leaks event candidate raw
  obtain ⟨selected, frame, earlier, recorded, posterior⟩ :=
    roster_window_posterior setup leaks bounds rosters initial event owner granted ownedEvent
      candidate raw opening owned valid offset serials published players covered network visits
        inside.le current reached
  rw [app.policyMixture_policy] at supported
  obtain ⟨mode, modeSupported, selectedSupport⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  change action ∈ (app.scheduledPolicy (rosterOffset setup rosters owner event) mode
    (fun _ _ => FinDist.pure packet) app.replayPolicy (current.recall owner) view).support
      at selectedSupport
  unfold ReactiveApplication.scheduledPolicy at selectedSupport
  split at selectedSupport
  · rename_i now
    have actionEq : action = packet := FinDist.mem_support_pure.mp selectedSupport
    subst action
    have empty : selected = none := by
      cases selected with
      | none => rfl
      | some slot =>
          rw [posterior choices full] at modeSupported
          cases FinDist.mem_support_pure.mp modeSupported
          have same := Option.some.inj now
          change rosterOffset setup rosters owner event + slot.val =
            (current.recall owner).length at same
          have before := earlier slot rfl
          have count := frame.count
          omega
    have absent : ¬ ∃ entry ∈ (current.recall owner).drop
        (rosterOffset setup rosters owner event), entry.action = packet := by
      intro present
      have contrary := recorded.mpr present
      rw [empty] at contrary
      cases contrary
    have grant : view.application.publicView.serviceGrant = some event := by
      change current.application.serviceGrant = some event
      rw [frame.application, granted]
    have data : rosterOpening? setup leaks owner event view = some (candidate, raw) := by
      rw [rosterOpening?_application_eq setup leaks owner event activated initial frame.application]
      exact opening
    have fresh : rosterFresh? setup leaks rosters owner (current.recall owner) view =
        some packet := by
      unfold rosterFresh?
      apply Option.bind_eq_some_iff.mpr
      refine ⟨event, grant, ?_⟩
      rw [ite_eq_right (not_not_intro ownedEvent)]
      apply Option.bind_eq_some_iff.mpr
      refine ⟨(candidate, raw), data, ?_⟩
      dsimp only
      simp only [List.any_eq_true, decide_eq_true_eq]
      change (if ∃ entry ∈ (current.recall owner).drop
        (rosterOffset setup rosters owner event), entry.action = packet
        then none else some packet) = some packet
      rw [ite_eq_right absent]
    apply Finset.mem_inter.mpr
    refine ⟨Finset.mem_union_right _ ?_, available⟩
    change packet ∈
      (rosterFresh? setup leaks rosters owner (current.recall owner) view).toList.toFinset
    rw [fresh]
    simp
  · exact replay_roster setup leaks bounds rosters owner _ _ action selectedSupport

end Vegas.SourceProgram.RevealService
