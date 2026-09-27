/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceActions
import Vegas.Game.RevealServiceInformation
import Interaction.ReactiveMenuPolicy

/-! # Source policies in the restricted revelation service

The existing source-to-event compiler supplies each owner's disclosure law.
The service changes only its representation: opening is the certified local
submission, and withholding has silence and published replay aliases. The
splitting weight is a proof parameter for common fully mixed approximants,
not a language or service option. Weight zero selects the canonical response.

Coverage is established at every local input by construction. Source-law
correspondence additionally needs the operational checkpoint invariants and
coverage of initialized values; these definitions do not assert an equilibrium
transfer.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

/-- Reuse the compiled source policy at the granted event. The checked identity
only totalizes malformed local inputs; actual player observations carry it. -/
def sourceChoiceLaw (profile : BehavioralProfile setup.program) (who : Player)
    (view : (application setup leaks).PlayerView) : FinDist Bool :=
  if identity : view.application.who = who then
    match view.application.publicView.serviceGrant with
    | none => FinDist.pure false
    | some event =>
        if owned : (graph setup).actor? event = some who then
          match nodeView (graph setup) event with
          | .sample .. | .bind .. => FinDist.pure false
          | .resolve _ _ _ _ outputEq _ =>
              cast (congrArg FinDist (congrArg EventGraph.EventField.Action outputEq))
                ((compileEventProfile setup.program profile) who event owned
                  (setup.eventGraph.fromModeObservation .sequential who
                    (identity ▸ view.application.observation)))
        else FinDist.pure false
  else FinDist.pure false

theorem sourceChoiceLaw_at_reveal (profile : BehavioralProfile setup.program)
    (who : Player) (execution : (application setup leaks).Execution)
    (event : (graph setup).EventId)
    (granted : execution.application.serviceGrant = some event)
    (owned : (graph setup).actor? event = some who)
    (owner : Player) (payload : L.Ty)
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (node : nodeView (graph setup) event =
      .resolve owner payload binding checks outputEq codeEq) :
    sourceChoiceLaw setup leaks profile who (execution.observe (application setup leaks) who) =
      cast (congrArg FinDist (congrArg EventGraph.EventField.Action outputEq))
        ((compileEventProfile setup.program profile) who event owned
          (setup.eventGraph.fromModeObservation .sequential who
            ((graph setup).playerObserve who execution.application.config))) := by
  unfold sourceChoiceLaw
  rw [dite_eq_left (show (execution.observe (application setup leaks) who).application.who = who
    from rfl)]
  change (match execution.application.serviceGrant with
    | none => _
    | some selected => _) = _
  simp only [granted]
  rw [dite_eq_left owned, node]
  rfl

variable [Fintype Player] (bounds : MessageBounds (graph setup))

open Classical in
def ordinaryPolicy (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) : (application setup leaks).Policy := fun past view =>
  match selected : opening? setup leaks who past view with
  | none => FinDist.pure ⟨none⟩
  | some opening =>
      if covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view then
        (splitChoiceLaw setup leaks bounds who past view opening selected covered
          (sourceChoiceLaw setup leaks profile who view) weight nonnegative atMostOne).map
            Subtype.val
      else FinDist.pure ⟨none⟩

theorem ordinaryPolicy_covered (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (supported : response ∈
      (ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne
        who past view).support) :
    response ∈ ordinaryActions setup leaks bounds who past view := by
  unfold ordinaryPolicy at supported
  split at supported
  · rw [FinDist.mem_support_pure] at supported
    subst response
    exact silence_ordinary setup leaks bounds who past view
  · split at supported
    · rw [FinDist.support_map] at supported
      obtain ⟨chosen, _present, same⟩ := supported
      exact same ▸ chosen.2
    · rw [FinDist.mem_support_pure] at supported
      subst response
      exact silence_ordinary setup leaks bounds who past view

theorem ordinaryPolicy_projects (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (opening : (application setup leaks).Action)
    (selected : opening? setup leaks who past view = some opening)
    (covered : opening ∈ (bounds.menu (runtime setup) leaks).actions who past view) :
    (ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne who past view).map
        (sourceChoice setup leaks) = sourceChoiceLaw setup leaks profile who view := by
  unfold ordinaryPolicy
  split
  · rename_i absent
    rw [selected] at absent
    cases absent
  · rename_i chosen found
    have same : chosen = opening := Option.some.inj (found.symm.trans selected)
    subst chosen
    rw [dite_eq_left covered, FinDist.map_comp]
    exact splitChoiceLaw_project setup leaks bounds who past view opening selected covered
      (sourceChoiceLaw setup leaks profile who view) weight nonnegative atMostOne

def policy (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) : (application setup leaks).Policy :=
  if who = watcher then (application setup leaks).reportFirstUnpublished
    else ordinaryPolicy setup leaks bounds profile weight nonnegative atMostOne who

theorem policy_covered (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (who : Player) (past : List (application setup leaks).PlayerEntry)
    (view : (application setup leaks).PlayerView) (response : (application setup leaks).Action)
    (supported : response ∈
      (policy setup leaks bounds watcher profile weight nonnegative atMostOne
        who past view).support) :
    response ∈ (menu setup leaks bounds watcher).actions who past view := by
  unfold policy at supported
  change response ∈ (if who = watcher then _ else _)
  split at supported
  · rename_i same
    rw [ite_eq_left same]
    exact FinDist.mem_supportFinset.mpr supported
  · rename_i different
    rw [ite_eq_right different]
    exact ordinaryPolicy_covered setup leaks bounds profile weight nonnegative atMostOne
      who past view response supported

def compiledProfile (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    GameTheory.Profile (information setup leaks bounds watcher).behavioralSignature := fun who =>
  (menu setup leaks bounds watcher).restrictPolicy (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) who
    (policy setup leaks bounds watcher profile weight nonnegative atMostOne who)

/-- The finite C-game policy decodes to the prescribed physical policy at
every local input. This includes the inputs used by focal alias selectors. -/
theorem decoded_compiledProfile (watcher : Player) (profile : BehavioralProfile setup.program)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    (menu setup leaks bounds watcher).decodeProfile (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)
        (compiledProfile setup leaks bounds watcher profile weight nonnegative atMostOne) =
      policy setup leaks bounds watcher profile weight nonnegative atMostOne := by
  funext who
  exact (menu setup leaks bounds watcher).decode_restrictPolicy_of_covered (initialLaw setup)
    (horizon setup watcher) (scheduler setup leaks watcher) who _
    (policy_covered setup leaks bounds watcher profile weight nonnegative atMostOne who)

end Vegas.SourceProgram.RevealService
