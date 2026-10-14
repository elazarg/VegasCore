/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketLateCertificate

/-! # The owner shape after a response at a first activation

At a first activation of `who` for its pending event, the response `who` makes
there is recorded by an entry whose view has the event as `who`'s turn
(`Vegas.respondEntry_activatedAt`). So every later decision of `who` whose recall
extends the site's recall by that entry is a late delivery of the event: from
it, a profile assembled from the certificate's components with any law
installed at the site plays the late owner shape, the late component of the
key's weights while `who` has sent nothing for the event
(`Vegas.certificate_firstActivation_lateOwnerShape`). The site itself is not
covered: there the installed law is played, and other first activations with
the site's recall are not late deliveries.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup leaks).Scheduler)
  [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

local notation "onePacketN" =>
  onePacketModel setup leaks bounds (initialLaw setup) horizon scheduler

omit [Fintype Player] [(application setup leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)] in
/-- The entry recording a response at a view whose turn is `event` activates
`event`. -/
theorem respondEntry_activatedAt {who : Player} {execution : (application setup leaks).Execution}
    {event : (graph setup).EventId}
    (turn : execution.application.publicView.ownTurn? who = some event)
    (response : (application setup leaks).Action) :
    ActivatedAt setup leaks who event (respondEntry setup leaks execution who response) :=
  turn

/-- **The owner shape after a response at a first activation.** At a forced
history of a site of `who` with `event` pending, a profile assembled from the
certificate's components with any law installed at the site plays the late
owner shape from the site's recall extended by the entry of a response there:
every later decision of `who` with that recall and nothing sent for the event
plays the late component of the key's weights. -/
theorem certificate_firstActivation_lateOwnerShape
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (onePacketN).BehavioralAssessment)
    (assembled : OnePacketAssembled setup leaks bounds horizon scheduler sequence scale scale_pos
      scale_le_one weights targetSequence) (n : ℕ) {who : Player}
    (site : (onePacketN).InformationSite who) {event : (graph setup).EventId}
    (pending : pendingEvent setup leaks who site.1 = some event)
    (law : PMF ((onePacketN).Choice who site.1))
    (history : (onePacketN).InformationHistory who site.1)
    {remaining : Nat} {execution : (application setup leaks).Execution}
    (current : history.1.state = some ⟨remaining, some who, execution⟩)
    (atSite : site.1 = some (execution.recall who,
      execution.observe (application setup leaks) who))
    (forced : ForcedState setup leaks who history.1.state)
    (response : (application setup leaks).Action) :
    LateOwnerShape setup leaks bounds horizon scheduler (sequence n) (scale_pos n).le
      (scale_le_one n) slots
      (Profile.update (sig := (onePacketN).behavioralSignature) (targetSequence n).strategy who
        (((targetSequence n).strategy who).withLaw site.1 law)) who event
      execution.application.config
      (execution.recall who ++ [respondEntry setup leaks execution who response]) := by
  intro later laterRemaining reached state holds
  obtain ⟨atSent, extends_, unrecordedHere⟩ := (by simpa only [state] using holds :
    LateUnsent setup leaks who event execution.application.config
      (execution.recall who ++ [respondEntry setup leaks execution who response])
      (some ⟨laterRemaining, some who, reached⟩))
  rw [Profile.update_same]
  -- The later recall is longer than the site's, so the decision is not the site's.
  have notSite : (some (reached.recall who, reached.observe (application setup leaks) who) :
      (application setup leaks).Info) ≠ site.1 := by
    intro same
    rw [atSite, Option.some.injEq, Prod.mk.injEq] at same
    have longer := extends_.length_le
    rw [same.1, List.length_append, List.length_singleton] at longer
    omega
  rw [BehavioralPolicy.withLaw_of_ne _ _ _ notSite]
  left
  have forcedHere : ForcedState setup leaks who later.state := by
    rw [current] at forced
    obtain ⟨forcedRank, forcedPoint, forcedOrdered, forcedDecoded, forcedHolds⟩ := forced
    rw [state]
    exact ⟨forcedRank, forcedPoint, by rw [atSent]; exact forcedOrdered,
      by rw [atSent]; exact forcedDecoded, forcedHolds⟩
  rw [atSite] at pending
  obtain ⟨turn, readyView, _, _⟩ := pendingEvent_spec pending
  have ready : reached.application.config.cut.Ready event := by
    rw [atSent]
    exact (execution.application.publicView_eventReady event).mp readyView
  have activated : ∃ entry ∈ reached.recall who, ActivatedAt setup leaks who event entry :=
    ⟨respondEntry setup leaks execution who response,
      extends_.subset (List.mem_append_right _ (List.mem_singleton_self _)),
      respondEntry_activatedAt setup leaks turn response⟩
  exact ⟨_, (certificate_strategyShape setup leaks bounds horizon scheduler sequence scale
    scale_pos scale_le_one weights targetSequence assembled n who later laterRemaining reached
    event state forcedHere ready activated).1 unrecordedHere⟩

end Vegas
