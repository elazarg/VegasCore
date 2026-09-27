/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceRosterPolicy
import Vegas.Pending.ReactiveReplaySettlement

/-! # Actual waiting before the final source opportunity

Before the selected owner's final visit, the full source policy executes the
existing replay law. The equality retains the entire execution, including
all passive samples and private response recall. Its application and public
allocation data are therefore unchanged even when the initial pool is empty.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every earlier response is a real replay-policy response. The bound counts
only owner visits, so arbitrary foreign visits may intervene. -/
theorem sourceServiceLastPolicy_waiting_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (initial : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (before : (initial.recall owner).length + visits.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner) :
    (runtime setup).runInteractionPlan leaks
        (sourceServiceLastPolicy setup leaks rosters profile) network
        (visits.map ServiceInstruction.player) initial =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).replayPolicy)
        network (visits.map ServiceInstruction.player) initial := by
  classical
  let app := application setup leaks
  induction visits generalizing initial with
  | nil => rfl
  | cons who rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, FinDist.bind_map, FinDist.bind_bind]
      apply FinDist.bind_congr
      intro sample _
      let activated := initial.sampledActivation app who sample
      have wait := sourceServiceLastPolicy_wait setup leaks rosters profile who
        (activated.recall who) (activated.observe app who) event granted
      have law : sourceServiceLastPolicy setup leaks rosters profile who
          (activated.recall who) (activated.observe app who) =
          app.replayPolicy (activated.recall who) (activated.observe app who) := by
        apply wait
        by_cases same : who = owner
        · subst who
          apply Or.inr (Or.inr ?_)
          change (initial.recall owner).length + 1 ≠ _
          simp only [List.count_cons_self] at before
          omega
        · exact Or.inl (fun equal => same (Option.some.inj (equal.symm.trans owned)))
      change (sourceServiceLastPolicy setup leaks rosters profile who
        (activated.recall who) (activated.observe app who)).bind _ =
        (app.replayPolicy (activated.recall who) (activated.observe app who)).bind _
      rw [law]
      apply FinDist.bind_congr
      intro response supported
      have unchanged : (activated.respond app who response).application = initial.application := by
        rcases app.replayPolicy_cases _ _ response supported with rfl | ⟨id, rfl⟩ <;> rfl
      apply ih _ (by rw [unchanged]; exact granted)
      rw [app.respond_recall_length]
      change (initial.recall owner).length + (if who = owner then 1 else 0) + rest.count owner < _
      by_cases same : who = owner
      · subst who
        simp only [List.count_cons_self] at before
        simp only [↓reduceIte]
        omega
      · simp only [same, ↓reduceIte, Nat.add_zero]
        simpa only [List.count_cons_of_ne same] using before

/-- The actual waiting prefix preserves the complete application and public
settlement data. Its replay copies and observed samples remain in the state. -/
theorem sourceServiceLastPolicy_waiting_data
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (visits : List Player) (initial final : (application setup leaks).Execution)
    (granted : initial.application.serviceGrant = some event)
    (before : (initial.recall owner).length + visits.count owner <
      rosterOffset setup rosters owner event + (rosters event).count owner)
    (safe : Message Player (WitnessedPacket (graph setup)) → Prop)
    (packets : initial.network.Satisfies safe)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (sourceServiceLastPolicy setup leaks rosters profile) network
        (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application ∧ final.network.ledger = initial.network.ledger ∧
      final.receipts = initial.receipts ∧ final.network.nextSerial = initial.network.nextSerial ∧
      final.network.Satisfies safe ∧ initial.network.pending ⊆ final.network.pending := by
  rw [sourceServiceLastPolicy_waiting_law setup leaks rosters profile network event owner owned
    visits initial granted before] at reached
  exact (runtime setup).replay_window_preserves leaks (fun _ =>
    (application setup leaks).replayPolicy) network owner initial
      (fun current who response _ _ supported => (application setup leaks).replayPolicy_cases
        (current.recall who) (current.observe (application setup leaks) who) response supported)
      safe packets visits final reached

end Vegas.SourceProgram.RevealService
