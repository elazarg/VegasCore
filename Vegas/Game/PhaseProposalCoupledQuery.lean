/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseObservableDomainWord
import Vegas.Game.PhaseProposalReference

/-! # Enriched proposal queries from actual saved-prefix frames

The owning masked-store comparison already removes opaque foreign completion
order from the base source getter. Complete packet observation supplies the
proposal archive at each actual decision. Neither comparison equates the two
owners' full native observations or their private syntax menus.
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks

/-- Add the actual reconstructed archive to the owning masked-prefix getter.
Raw private actions and foreign completion order need not coincide. -/
theorem phaseProposalQuery?_eq_of_masked_prefix
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (firstPast secondPast : List (app).PlayerEntry) (first second : (app).PlayerView)
    (firstOwner : first.application.1.who = who)
    (secondOwner : second.application.1.who = who)
    (stores : first.application.1.observation.store = second.application.1.observation.store)
    (attempt : first.application.2.attempt = second.application.2.attempt)
    (archives : first.application.2.retired = second.application.2.retired)
    (same : ∀ rank ≤ first.application.2.attempt.phase,
      first.application.2.native.sourceFailureFootprint.1 rank =
        second.application.2.native.sourceFailureFootprint.1 rank)
    (proposals : PhaseProposal.observedSourceArchive runtime leaks firstPast first =
      PhaseProposal.observedSourceArchive runtime leaks secondPast second) :
    phaseProposalQuery? setup mode runtime leaks plan who event firstPast first =
      phaseProposalQuery? setup mode runtime leaks plan who event secondPast second := by
  unfold phaseProposalQuery?
  rw [phaseVirtualSourceQuery?_eq_of_masked_prefix setup mode runtime leaks plan who event
    first second firstOwner secondOwner stores attempt archives same, proposals]

/-- At two genuine callbacks in a paired opaque commitment attempt, the
operational saved-entry frame and submitted archive determine the SAME
enriched query. Complete observation derives the archive readout here. -/
theorem phaseProposalQuery?_eq_of_ready_saved
    (complete : leaks = MessageNetwork.completePendingObservation)
    (initial : PMF (app).State) (horizon : Nat)
    (leftScheduler rightScheduler : (app).Scheduler)
    (leftRemaining rightRemaining : Nat) (who : Player)
    (left right : (app).Execution)
    (leftTrace : ((app).protocol initial horizon leftScheduler).Trace
      (some ⟨leftRemaining, some who, left⟩))
    (rightTrace : ((app).protocol initial horizon rightScheduler).Trace
      (some ⟨rightRemaining, some who, right⟩))
    (phase : RuntimePhase (serviceGraph setup mode)) (commitment : phase.kind = .commitment)
    (leftInstalled : phase ∈ left.application.phases.head?)
    (rightInstalled : phase ∈ right.application.phases.head?)
    (leftFrontier : left.application.Frontier) (rightFrontier : right.application.Frontier)
    (leftStored : left.application.StoredCheckpoint)
    (rightStored : right.application.StoredCheckpoint)
    (leftFailures : left.application.PublicFailureCheckpoint)
    (rightFailures : right.application.PublicFailureCheckpoint)
    (entry : left.application.entry = right.application.entry)
    (attempt : left.application.attempt = right.application.attempt)
    (archives : left.application.retired = right.application.retired)
    (event : (serviceGraph setup mode).EventId) (inside : event ∈ phase.events)
    (leftRequest : left.application.SeedRequest who ⟨left.application.attempt, event⟩)
    (rightRequest : right.application.SeedRequest who ⟨right.application.attempt, event⟩)
    (ownEarlier : ∀ prior ∈ phase.events, prior.val < event.val →
      (serviceGraph setup mode).actor? prior = some who →
        left.application.current.native.config.store (.inr prior) =
          right.application.current.native.config.store (.inr prior))
    (proposals : PhaseProposal.sourceArchive left.network.inputs =
      PhaseProposal.sourceArchive right.network.inputs) :
    phaseProposalQuery? setup mode runtime leaks plan who event
        (left.recall who) (left.observe app who) =
      phaseProposalQuery? setup mode runtime leaks plan who event
        (right.recall who) (right.observe app who) := by
  have base := phaseVirtualSourceQuery?_eq_of_ready_saved setup mode runtime leaks plan
    left right phase commitment leftInstalled rightInstalled leftFrontier rightFrontier
    leftStored rightStored leftFailures rightFailures entry attempt archives who event inside
    leftRequest rightRequest ownEarlier
  have leftArchive := PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete
    initial horizon leftScheduler ⟨leftRemaining, some who, left⟩ leftTrace who rfl
  have rightArchive := PhaseProposal.observedSourceArchive_eq_submitted runtime leaks complete
    initial horizon rightScheduler ⟨rightRemaining, some who, right⟩ rightTrace who rfl
  unfold phaseProposalQuery?
  rw [base, leftArchive, rightArchive, proposals]

/-- An equality of the actual getter transports the literal ordinary domain
table, including accepted unusable perturbations and guard-rejecting values.
This is an effective result law, not equality of private response aliases. -/
theorem phaseProposalBindingResults_eq_of_query
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (rates : PhaseProposalRates) (who : Player) (event : (serviceGraph setup mode).EventId)
    (payload : L.Ty) (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (firstPast secondPast : List (app).PlayerEntry) (first second : (app).PlayerView)
    (queried : phaseProposalQuery? setup mode runtime leaks plan who event firstPast first =
      phaseProposalQuery? setup mode runtime leaks plan who event secondPast second) :
    phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
        binding firstPast first =
      phaseProposalBindingResults setup mode runtime leaks plan values rates who event payload
        binding secondPast second := by
  unfold phaseProposalBindingResults
  rw [queried]

end Vegas
