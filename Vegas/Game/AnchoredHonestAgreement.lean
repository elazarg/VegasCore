/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AnchoredOpeningClients
import Vegas.Game.OwnedCompletionCause
import Vegas.Game.OnePacketHonestAgreement

/-! # As-if-honest play agrees with the anchored clients from reached boundaries

From a reached boundary decoding to a point of the intended game, along the
runs of the anchored first-turn clients of the intended effective opening, an
owned event completes only through an accepted packet of its actor
(`Vegas.reachedBoundary_completion_accepted`): an expiry would leave the
intended game. So an owner that had a turn at its event has submitted for it
(`Vegas.reachedBoundary_recorded_of_seen`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

variable (setup leaks) in
/-- The configuration has not completed `event`, or an included packet naming it,
sent by its actor, was accepted. -/
def CompletedByActor (event : (graph setup).EventId)
    (execution : (application setup leaks).Execution) : Prop :=
  event ∉ execution.application.config.cut.completed ∨
    ∃ message ∈ execution.network.ledger, (message.id, true) ∈ execution.receipts ∧
      message.payload.call.event? (graph setup) = some event ∧
      (graph setup).actor? event = some message.sender

/-- **Completions by the actor.** From a reached boundary decoding to a point
of the intended game, along runs of the anchored first-turn clients of the
intended effective opening within the horizon, an owned event that has not
completed, or has completed through an accepted packet of its actor, keeps
that property. -/
theorem reachedBoundary_completion_accepted [Finite Player] {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point)
    (event : (graph setup).EventId) {owner : Player}
    (owned : (graph setup).actor? event = some owner) :
    ∀ more (execution : (application setup leaks).Execution),
      execution ∈ ((application setup leaks).runRounds scheduler
          (ReactiveApplication.anchoredPolicy anchor
            (firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile intended)))
          more anchor).support →
      ∀ later, anchor.environmentRecall.length + more + later ≤ horizon →
      CompletedByActor setup leaks event execution →
      ∀ final ∈ ((application setup leaks).runRounds scheduler
          (ReactiveApplication.anchoredPolicy anchor
            (firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile intended)))
          later execution).support,
        CompletedByActor setup leaks event final := by
  let app := application setup leaks
  let players := ReactiveApplication.anchoredPolicy anchor
    (firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile intended))
  intro more execution supported later
  induction later generalizing more execution with
  | zero =>
      intro _ holds final reachedFinal
      cases (PMF.mem_support_pure_iff _ _).mp reachedFinal
      exact holds
  | succ later ih =>
      intro within holds final reachedFinal
      obtain ⟨next, nextMem, rest⟩ := (PMF.mem_support_bind_iff _ _ _).mp reachedFinal
      have nextSupported : next ∈ (app.runRounds scheduler players (more + 1) anchor).support := by
        rw [ReactiveApplication.runRounds_add]
        refine (PMF.mem_support_bind_iff _ _ _).mpr ⟨execution, supported, ?_⟩
        exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨next, nextMem,
          (PMF.mem_support_pure_iff _ _).mpr rfl⟩
      refine ih (more + 1) next nextSupported (by omega) ?_ final rest
      obtain ⟨command, _, middle, stepped, cases⟩ := round_cases setup leaks nextMem
      have grows := environment_ledger_receipts_grow execution middle command stepped
      -- The step keeps the property through the environment step.
      have middleHolds : CompletedByActor setup leaks event middle := by
        rcases holds with open_ | ⟨message, present, receipt, named, sender⟩
        · rcases environmentStep_configStep setup leaks execution middle command stepped with
            same | ⟨completed, ready, action, member⟩
          · left
            rw [same]
            exact open_
          · by_cases finished : event ∈ middle.application.config.cut.completed
            · have completedEq : completed = event := by
                rw [execution.application.config.step_cut completed ready action _ member]
                  at finished
                rcases (EventOrder.Cut.mem_complete _ _ _ _).mp finished with same | earlier
                · exact same.symm
                · exact (open_ earlier).elim
              subst completedEq
              rcases owned_completion_cause execution middle command stepped owned ready action
                  member with accepted | expiring
              · exact Or.inr accepted
              · exfalso
                obtain ⟨rankBefore, ⟨residual⟩, _⟩ := reachedBoundary_intended contract timely
                  turns intended reached point decoded intendedPoint more (by omega) execution
                  supported
                obtain ⟨rankNext, ⟨nextResidual⟩, nextIntended⟩ := reachedBoundary_intended
                  contract timely turns intended reached point decoded intendedPoint (more + 1)
                  (by omega) next nextSupported
                have configEq : next.application.config = middle.application.config := by
                  rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
                  · rfl
                  · exact ((runtime setup).reactive_respond_application leaks middle responder
                      response).1
                have advanced : middle.application.config.cut.IsPrefix (rankBefore + 1) := by
                  rw [execution.application.config.step_cut completed ready action _ member]
                  exact residual.checkpoint.ordered.complete_at completed ready
                    ((ready_iff_rank setup _ rankBefore residual.checkpoint.ordered completed).mp
                      ready)
                have sameRank := isPrefix_unique nextResidual.checkpoint.ordered
                  (configEq ▸ advanced)
                subst sameRank
                have decodedNext := nextResidual.decode
                have pointIntended := nextIntended _ decodedNext
                generalize nextResidual.lift (ProtocolState.entry nextResidual.program
                  nextResidual.source) = nextPoint at decodedNext pointIntended
                rw [configEq] at decodedNext
                exact residual.expiry_not_intended completed ready action expiring member _
                  decodedNext pointIntended
            · exact Or.inl finished
        · exact Or.inr ⟨message, grows.1 message present, grows.2 _ receipt, named, sender⟩
      rcases cases with ⟨_, rfl⟩ | ⟨responder, _, response, _, rfl⟩
      · exact middleHolds
      · have configEq := ((runtime setup).reactive_respond_application leaks middle responder
          response).1
        unfold CompletedByActor at middleHolds ⊢
        rw [configEq, app.respond_ledger, app.respond_receipts]
        exact middleHolds

/-- **Earlier turns are answered from a reached boundary.** For a well-formed
setup, under the asynchronous contract with timely delays, from a reached
boundary decoding to a point of the intended game, at every execution the
anchored first-turn clients of the intended effective opening reach within the
horizon, an owner that had a turn at its ready event has submitted for it. -/
theorem reachedBoundary_recorded_of_seen [Finite Player] {horizon : Nat}
    {scheduler : (application setup leaks).Scheduler} {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) {more : Nat}
    (within : anchor.environmentRecall.length + more ≤ horizon)
    {execution : (application setup leaks).Execution}
    (supported : execution ∈ ((application setup leaks).runRounds scheduler
      (ReactiveApplication.anchoredPolicy anchor
        (firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile intended)))
      more anchor).support)
    (who : Player) (event : (graph setup).EventId) (owned : (graph setup).actor? event = some who)
    (ready : execution.application.config.cut.Ready event)
    (seen : SeenTurn who event (execution.recall who)) :
    (runtime setup).eventRecorded leaks (execution.recall who) event = true := by
  have := Fintype.ofFinite Player
  let app := application setup leaks
  let clients := firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile intended)
  let players := ReactiveApplication.anchoredPolicy anchor clients
  let count := anchor.environmentRecall.length
  let rest := horizon - (count + more)
  apply Bool.eq_true_of_not_eq_false
  intro unrecorded
  have extends_ := (ContinuesAnchor.runRounds (bound := bound) (turns := turns)
    (profile := setup.intendedOpeningProfile intended) (scheduler := scheduler) more anchor
    ⟨fun _ => List.prefix_refl _, reached.turns⟩ execution supported).1
  obtain ⟨final, finalMem⟩ := (app.runRounds scheduler clients rest execution).support_nonempty
  have kept := (openingClients_keeps_unrecorded scheduler bound turns intended who event rest
    execution unrecorded seen final finalMem).1
  have finalAnchored : final ∈ (app.runRounds scheduler players rest execution).support := by
    rw [ReactiveApplication.runRounds_anchoredPolicy_of_extends scheduler anchor clients rest
      execution extends_]
    exact finalMem
  have accepted := reachedBoundary_completion_accepted contract timely turns intended reached
    point decoded intendedPoint event owned more execution supported rest (by omega)
    (Or.inl ready.1) final finalAnchored
  have boundary := reachedBoundary_completionBoundary reached clients
  have finalSupported : final ∈ (app.roundsFrom (initialLaw setup) scheduler players
      horizon).support := by
    have composed := mem_roundsFrom_of_runRounds (app := app)
      (mem_roundsFrom_of_runRounds (app := app) boundary.supported supported) finalAnchored
    rwa [show count + more + rest = horizon by omega] at composed
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players
    horizon le_rfl final finalSupported
  rw [Nat.sub_self] at trace
  have terminalCut := contract.completes ⟨0, none, final⟩ trace ⟨rfl, rfl⟩
  have completed : event ∈ final.application.config.cut.completed := by
    change final.application.config.cut.completed = Finset.univ at terminalCut
    rw [terminalCut]
    exact Finset.mem_univ _
  rcases accepted with open_ | ⟨message, present, _, named, sender⟩
  · exact open_ completed
  · have senderEq : message.sender = who := Option.some.inj (sender.symm.trans owned)
    have input := app.ledger_subset_inputs_history (initialLaw setup) horizon scheduler
      ⟨0, none, final⟩ trace present
    have output : message ∈ app.outputs (final.recall who) := by
      rw [← app.history_inputRecall (initialLaw setup) horizon scheduler trace who]
      exact List.mem_filter.mpr ⟨input, by simp [senderEq]⟩
    exact output_event trace who event kept message output named

variable (setup leaks) in
/-- **Retention of the opening's canonical packets.** At every activation of a
legal raw history, at the owner's turn at an event its recall has not submitted
for, while a fresh call still fits the deadline, every transmitting response of
the canonical source decision of the intended effective opening is retained by
the canonical menu. -/
def RetainsOpeningCanonical [Fintype Player] (bounds : MessageBounds (graph setup))
    (bound : (graph setup).EventId → Nat) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler)
    (intended : ∀ who, setup.intendedModel.BehavioralPolicy who) : Prop :=
  ∀ remaining who (execution : (application setup leaks).Execution),
    ((application setup leaks).protocol (initialLaw setup) horizon scheduler).Trace
      (some ⟨remaining, some who, execution⟩) →
    ∀ event, (execution.observe (application setup leaks) who).application.publicView.ownTurn?
        who = some event →
      (runtime setup).eventRecorded leaks (execution.recall who) event = false →
      (execution.observe (application setup leaks) who).application.publicView.InclusionFitsDeadline
        (runtime setup) bound event →
      ∀ response ∈ (sourceServiceCanonicalPolicy setup leaks
          (setup.intendedOpeningProfile intended) who (execution.recall who)
          (execution.observe (application setup leaks) who)).support,
        response.transmission ≠ none →
        response ∈ bounds.canonicalActions (runtime setup) leaks who (execution.recall who)
          (execution.observe (application setup leaks) who)

/-- **As-if-honest play agrees with the anchored clients.** For a well-formed
setup, under the asynchronous contract with timely delays and retention of the
opening's canonical packets, from a reached boundary decoding to a point of the
intended game, at every input the scheduler queries within the horizon along a
run of the anchored first-turn clients of the intended effective opening,
as-if-honest play read as native policies responds exactly as those clients
do. -/
theorem honestPolicy_eq_anchoredClients [Fintype Player] (bounds : MessageBounds (graph setup))
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler delay
      bound)
    (timely : AsyncTimely (runtime setup) delay bound) (turns : Nat)
    (assessment : setup.intendedModel.BehavioralAssessment)
    (retains : RetainsOpeningCanonical setup leaks bounds bound horizon scheduler
      assessment.strategy) {rank : Nat}
    {anchor : (application setup leaks).Execution}
    (reached : ReachedBoundary setup leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intendedPoint : ProtocolState.Intended setup.program point) {more : Nat}
    (within : anchor.environmentRecall.length + more < horizon)
    {execution : (application setup leaks).Execution}
    (supported : execution ∈ ((application setup leaks).runRounds scheduler
      (ReactiveApplication.anchoredPolicy anchor
        (firstTurnClients setup leaks bound turns (setup.intendedOpeningProfile
          assessment.strategy)))
      more anchor).support)
    {command : (application setup leaks).Command}
    (selected : command ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment (application setup leaks))).support)
    {middle : (application setup leaks).Execution}
    (moved : middle ∈ (execution.environmentStep (application setup leaks) command).support)
    {who : Player} (active : command.actor? (application setup leaks) = some who) :
    (bounds.onePacketMenu (runtime setup) leaks).decodeProfile (initialLaw setup) horizon scheduler
        (honestProfile setup leaks bounds (initialLaw setup) horizon scheduler assessment) who
        (middle.recall who) (middle.observe (application setup leaks) who) =
      openingClients setup leaks bound turns assessment.strategy who (middle.recall who)
        (middle.observe (application setup leaks) who) := by
  classical
  let app := application setup leaks
  let opening := setup.intendedOpeningProfile assessment.strategy
  let clients := firstTurnClients setup leaks bound turns opening
  let players := ReactiveApplication.anchoredPolicy anchor clients
  let count := anchor.environmentRecall.length + more
  have commandEq : command = .activate who := by
    cases command with
    | activate actor =>
        exact congrArg ReactiveApplication.Command.activate (Option.some.inj active)
    | wait | «include» _ | application _ => cases active
  subst commandEq
  have appEq := activation_application setup leaks execution middle who moved
  have recallEq := app.environmentStep_recall execution middle (.activate who) moved
  have boundary := reachedBoundary_completionBoundary reached clients
  have rounds : execution ∈ (app.roundsFrom (initialLaw setup) scheduler players count).support :=
    mem_roundsFrom_of_runRounds (app := app) boundary.supported supported
  obtain ⟨trace⟩ := app.raw_trace_roundsFrom (initialLaw setup) horizon scheduler players count
    within.le execution rounds
  rw [show horizon - count = (horizon - count - 1) + 1 by omega] at trace
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
    (horizon - count - 1) execution middle (.activate who) trace selected moved
  change app.protocol (initialLaw setup) horizon scheduler |>.Trace
    (some ⟨horizon - count - 1, some who, middle⟩) at middleTrace
  have answered := roundsFrom_activationsAnswered count execution rounds
  have continues := ContinuesAnchor.runRounds (bound := bound) (turns := turns) (profile := opening)
    (scheduler := scheduler) more anchor ⟨fun _ => List.prefix_refl _, reached.turns⟩ execution
    supported
  have atTurn : OwnSubmissionsAtTurn setup leaks middle who := by
    unfold OwnSubmissionsAtTurn
    rw [recallEq]
    exact continues.2 who
  rw [decodeProfile_honestProfile]
  have silenceKept : onePacketFilter bounds who (middle.recall who) (middle.observe app who)
      ⟨none⟩ = ⟨none⟩ := by
    unfold onePacketFilter
    split <;> rfl
  cases turnCase : middle.application.publicView.ownTurn? who with
  | none =>
      have view : (middle.observe app who).application.publicView.ownTurn? who = none := turnCase
      rw [honestResponse_of_no_turn setup leaks assessment who _ _ view, PMF.pure_map,
        silenceKept]
      unfold openingClients serviceTurnPolicy
      rw [view]
      rfl
  | some event =>
      have view : (middle.observe app who).application.publicView.ownTurn? who = some event :=
        turnCase
      have owned := (PublicView.ownTurn?_spec _ who event turnCase).2
      have ready : execution.application.config.cut.Ready event := by
        rw [← appEq]
        exact (middle.application.publicView_eventReady event).mp
          (PublicView.ownTurn?_spec _ who event turnCase).1
      by_cases seen : SeenTurn who event (middle.recall who)
      · rw [openingClients_later_silent bound turns assessment.strategy who _ _ event view seen]
        have recorded : (runtime setup).eventRecorded leaks (middle.recall who) event = true := by
          rw [recallEq]
          exact reachedBoundary_recorded_of_seen contract timely turns assessment.strategy
            reached point decoded intendedPoint within.le supported who event owned ready
            (by rw [← recallEq]; exact seen)
        refine (map_congr_on_support _ (g := fun _ => (⟨none⟩ : app.Action)) ?_).trans
          (PMF.map_const _ _)
        intro response chosen
        rcases mem_support_honestResponse setup leaks assessment who _ _ event view response
            chosen with rfl | ⟨action, graphAction, _, _, rfl⟩
        · exact silenceKept
        · unfold onePacketFilter
          split
          · rename_i member
            cases transmits : ((runtime setup).canonicalServiceDecision leaks who
                (middle.recall who) (middle.observe app who) event graphAction).transmission with
            | none =>
                generalize (runtime setup).canonicalServiceDecision leaks who (middle.recall who)
                  (middle.observe app who) event graphAction = response at transmits ⊢
                rcases response with ⟨transmission⟩
                change transmission = none at transmits
                rw [transmits]
            | some material =>
                exact (canonical_not_onePacket_of_recorded bounds middleTrace who event recorded
                  graphAction material transmits member).elim
          · rfl
      · have first : serviceTurn setup .sequential (rankDeadline setup .sequential) leaks who event
            (middle.recall who) (middle.observe app who) = some 0 := by
          change (if (middle.observe app who).application.publicView.ownTurn? who = some event
            then some ((middle.recall who).countP fun entry =>
              decide (entry.beforeView.application.publicView.ownTurn? who = some event))
            else none) = some 0
          rw [ite_eq_left view ..]
          apply congrArg some
          exact List.countP_eq_zero.mpr fun entry member earlier =>
            seen ⟨entry, member, of_decide_eq_true earlier⟩
        have unrecorded := sourceServiceFirstTurn_unrecorded atTurn first
        have firstBefore : serviceTurn setup .sequential (rankDeadline setup .sequential) leaks who
            event (execution.recall who) (middle.observe app who) = some 0 := by
          rw [← recallEq]
          exact first
        have fits := firstTurn_inclusionFits contract timely trace answered owned ready firstBefore
        have fitsMiddle : (middle.observe app who).application.publicView.InclusionFitsDeadline
            (runtime setup) bound event := by
          change middle.application.publicView.InclusionFitsDeadline (runtime setup) bound event
          rw [appEq]
          exact fits
        have opportunity : openingClients setup leaks bound turns assessment.strategy who
            (middle.recall who) (middle.observe app who) =
            (serviceCanonicalPolicy setup .sequential (rankDeadline setup .sequential) leaks
              opening who (middle.recall who) (middle.observe app who)).bind fun response =>
                if response.transmission = none then app.silentPolicy (middle.recall who)
                  (middle.observe app who)
                else PMF.pure response := by
          rw [openingClients, sourceServiceTurnPolicy_firstTurn owned first]
          unfold serviceCanonicalOpportunity
          simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fitsMiddle]
          rfl
        rw [opportunity]
        obtain ⟨rankNow, ⟨residual⟩, intendedHolds⟩ := reachedBoundary_intended contract timely
          turns assessment.strategy reached point decoded intendedPoint more within.le execution
          supported
        obtain ⟨staticRank, ⟨staticResidual⟩, staticHolds⟩ :=
          roundsFrom_static scheduler players opening count execution rounds
        have sameRank := isPrefix_unique staticResidual.checkpoint.ordered
          residual.checkpoint.ordered
        subst sameRank
        have decodedMiddle : sourceServicePrefix? setup staticRank middle.application.config =
            some (residual.lift (ProtocolState.entry residual.program residual.source)) := by
          rw [appEq]
          exact residual.decode
        have orderedMiddle : middle.application.config.cut.IsPrefix staticRank := by
          rw [appEq]
          exact residual.checkpoint.ordered
        rw [honestResponse_eq_openingCanonical assessment middle staticRank orderedMiddle _
          decodedMiddle (staticHolds _ residual.decode) (intendedHolds _ residual.decode) who event
          turnCase]
        rw [show sourceServiceCanonicalPolicy setup leaks opening = serviceCanonicalPolicy setup
          .sequential (rankDeadline setup .sequential) leaks opening from rfl,
          ← PMF.bind_pure_comp]
        apply bind_congr_on_support _
        intro response chosen
        have chosenCanonical := chosen
        rw [sourceServiceCanonicalPolicy_at_event setup leaks opening who middle event turnCase
          owned, PMF.mem_support_map_iff] at chosen
        obtain ⟨graphAction, _, rfl⟩ := chosen
        cases transmits : ((runtime setup).canonicalServiceDecision leaks who (middle.recall who)
            (middle.observe app who) event graphAction).transmission with
        | none =>
            simp only [↓reduceIte]
            generalize (runtime setup).canonicalServiceDecision leaks who (middle.recall who)
              (middle.observe app who) event graphAction = response at transmits ⊢
            rcases response with ⟨transmission⟩
            change transmission = none at transmits
            subst transmits
            exact congrArg PMF.pure silenceKept
        | some material =>
            simp only [reduceCtorEq, ↓reduceIte]
            have member := canonical_mem_onePacket setup leaks bounds who (middle.recall who)
              (middle.observe app who) _
              (retains _ who middle middleTrace event view unrecorded fitsMiddle _
                chosenCanonical (by rw [transmits]; exact Option.some_ne_none material))
              (fun chosenMaterial sends => canonicalServiceDecision_countPermits middleTrace who
                event turnCase unrecorded graphAction chosenMaterial sends)
            simp only [Function.comp_apply, onePacketFilter]
            split
            · rfl
            · rename_i absent
              exact (absent member).elim

end Vegas
