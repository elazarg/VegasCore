module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.RevealBlockCoupling
public import Vegas.Game.RevealTurnRecall

@[expose] public section

/-! # The traffic of a run of reveals from any point inside it

Inside a run of concurrent reveals, honest clients open a reveal at their first
turn exactly when the opening is accepted. Whether an owner has had its turn at
an event is read from the environment's recall, which is part of the deviator's
traffic. So two executions inside the run with equal deviator traffic, whose
ready reveals keep being accepted alike, give equal laws of the traffic when run
until any stop determined by focal traffic that holds once the run is done.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies} {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- The recall facts kept by every round: responses and activations answer each
other, and every honest owner submits at its turns with canonical slots. -/
def RunTurnFacts (who : Player)
    (execution : (serviceApplication setup deps duration leaks).Execution) : Prop :=
  ActivationsAnswered setup leaks execution ∧ ResponsesActivated setup leaks execution ∧
    ∀ owner, owner ≠ who → OwnSubmissionsAtTurn setup leaks execution owner ∧
      CanonicalSlotsUsed setup leaks execution owner

/-- The recall facts hold on the support of rounds from initialization. -/
theorem runTurnFacts_roundsFrom
    (serial : (serviceGraph setup deps).ActorSerial)
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy) (count : Nat)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (supported : execution ∈ ((serviceApplication setup deps duration leaks).roundsFrom
      (serviceInitialLaw setup deps) scheduler (Function.update (serviceReferenceTurnPolicy
        setup deps duration leaks bound turns (firstTurnTiming setup turns deps) reference)
        who deviation) count).support) :
    RunTurnFacts who execution :=
  ⟨roundsFrom_activationsAnswered count execution supported,
    roundsFrom_responsesActivated count execution supported,
    fun owner different => canonicalSlots_roundsFrom_reference serial scheduler _ owner
      (firstTurnTiming setup turns deps) reference (Function.update_of_ne different _ _) count
      execution supported⟩

/-- Every round keeps the recall facts. -/
theorem RunTurnFacts.round
    (serial : (serviceGraph setup deps).ActorSerial) {horizon remaining : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile) (who : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    {execution next : (serviceApplication setup deps duration leaks).Execution}
    (trace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (facts : RunTurnFacts who execution)
    (reached : next ∈ ((serviceApplication setup deps duration leaks).round scheduler
      (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) reference) who deviation) execution).support) :
    RunTurnFacts who next := by
  obtain ⟨answered, activated, honest⟩ := facts
  refine ⟨round_activationsAnswered setup leaks answered reached,
    round_responsesActivated setup leaks activated reached, fun owner different => ?_⟩
  have follows : Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound
      turns (firstTurnTiming setup turns deps) reference) who deviation owner =
      serviceReferenceTurnPolicy setup deps duration leaks bound turns
        (firstTurnTiming setup turns deps) reference owner := Function.update_of_ne different _ _
  obtain ⟨atTurn, valid⟩ := honest owner different
  exact canonicalSlots_round serial
    (follows ▸ serviceTurnPolicy_submitsCanonically_reference bound turns
      (firstTurnTiming setup turns deps) reference owner)
    (follows ▸ sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
      (firstTurnTiming setup turns deps) reference owner) trace atTurn valid reached

/-- An owner that submits only at its turns has not submitted for an event at
which it has had no turn. -/
theorem eventRecorded_eq_false_of_ownerTurns
    {execution : (serviceApplication setup deps duration leaks).Execution} {owner : Player}
    (atTurn : OwnSubmissionsAtTurn setup leaks execution owner)
    {event : (serviceGraph setup deps).EventId} (none : ownerTurns owner event execution = 0) :
    (eventRecorded (serviceTimeouts setup deps duration)) leaks (execution.logs owner) event =
      false := by
  unfold EventGraphRuntime.eventRecorded
  rw [List.any_eq_false]
  intro entry member submitted
  unfold ownerTurns at none
  rw [List.countP_eq_zero] at none
  exact none entry member (decide_eq_true
    (atTurn entry member event (of_decide_eq_true submitted)))

/-- The existing public-round opacity proof permits any stop read from focal traffic. -/
theorem run_stopped_traffic_congr
    (serial : (serviceGraph setup deps).ActorSerial) {horizon : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup deps).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup deps).Config)
      (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
      (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
        ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup deps) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup deps).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup deps).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup deps).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store))) (who : Player)
    (deviation : (serviceApplication setup deps duration leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup deps) start finish)
    (publications : ∀ event : (serviceGraph setup deps).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup deps).outputLayout event).IsPublication)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop) [DecidablePred stop]
    (stopDone : ∀ execution : (serviceApplication setup deps duration leaks).Execution,
      BlockDone finish execution.application.config → stop execution)
    (observedStop : ∀ left right : (serviceApplication setup deps duration leaks).Execution,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks who left =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks who right →
      (stop left ↔ stop right))
    (leftGood rightGood : Nat → (serviceApplication setup deps duration leaks).Execution → Prop)
    (leftRound : ∀ n current, leftGood (n + 1) current → ¬ stop current →
      ∀ next ∈ ((serviceApplication setup deps duration leaks).round scheduler
        (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) reference) who deviation) current).support,
        leftGood n next)
    (rightRound : ∀ n current, rightGood (n + 1) current → ¬ stop current →
      ∀ next ∈ ((serviceApplication setup deps duration leaks).round scheduler
        (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) reference) who deviation) current).support,
        rightGood n next) :
    ∀ (count leftRemaining rightRemaining : Nat)
      (left right : (serviceApplication setup deps duration leaks).Execution),
      ((serviceApplication setup deps duration leaks).protocol
        (serviceInitialLaw setup deps) horizon scheduler).Trace
          (some ⟨leftRemaining + count, none, left⟩) →
      ((serviceApplication setup deps duration leaks).protocol
        (serviceInitialLaw setup deps) horizon scheduler).Trace
          (some ⟨rightRemaining + count, none, right⟩) →
      (¬ BlockDone finish left.application.config →
        InBlock start finish left.application.config) →
      (¬ BlockDone finish right.application.config →
        InBlock start finish right.application.config) →
      HonestBlockSubmissions who start finish left →
      HonestBlockSubmissions who start finish right →
      RunTurnFacts who left → RunTurnFacts who right →
      leftGood count left → rightGood count right →
      (∀ (n : Nat) (currentRun otherRun : (serviceApplication setup deps duration leaks).Execution),
        leftGood (n + 1) currentRun → rightGood (n + 1) otherRun →
        currentRun.application.config.cut = otherRun.application.config.cut →
        ¬ stop currentRun → ¬ stop otherRun →
        let current := currentRun.application.config
        let other := otherRun.application.config
        ∀ (event : (serviceGraph setup deps).EventId) (owner : Player) (payload : L.Ty)
          (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
          (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
          (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
          (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
            ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
        nodeView (serviceGraph setup deps) event =
          .resolve owner payload binding checks outputEq codeEq →
        current.cut.Ready event → owner ∉ current.defaulted → owner ∉ other.defaulted →
        (owner ≠ who → openingAccepted event current.store = openingAccepted event other.store) ∧
        (openingAccepted event current.store = true ∨ owner = who →
          binding.get? current.store = binding.get? other.store)) →
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks who left =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks who right →
      ((serviceApplication setup deps duration leaks).runUntil scheduler
        (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) reference) who deviation)
        stop count left).map
          ((bindingTraffic (serviceTimeouts setup deps duration)) leaks who) =
      ((serviceApplication setup deps duration leaks).runUntil scheduler
        (Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound turns
          (firstTurnTiming setup turns deps) reference) who deviation)
        stop count right).map
          ((bindingTraffic (serviceTimeouts setup deps duration)) leaks who) := by
  intro count leftRemaining rightRemaining left right leftTrace rightTrace leftInside
    rightInside leftValid rightValid leftFacts rightFacts leftStart rightStart agreeAt same
  let app := serviceApplication setup deps duration leaks
  let players := Function.update (serviceReferenceTurnPolicy setup deps duration leaks bound
    turns (firstTurnTiming setup turns deps) reference) who deviation
  let window : (serviceGraph setup deps).EventId → Bool := fun _ => false
  have readoutOf (execution : app.Execution) : blockReadoutOn who window execution =
      ((bindingTraffic (serviceTimeouts setup deps duration)) leaks who execution,
        fun _ _ => (0, false)) := rfl
  have notDone (execution : app.Execution) (running : ¬ stop execution) :
      ¬ BlockDone finish execution.application.config :=
    fun done => running (stopDone execution done)
  let invariant := fun (good : Nat → app.Execution → Prop) (count : Nat)
      (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    good count current ∧
    HonestBlockSubmissions who start finish current ∧ RunTurnFacts who current
  have advance (good : Nat → app.Execution → Prop)
      (goodRound : ∀ n current, good (n + 1) current → ¬ stop current →
        ∀ next ∈ (app.round scheduler players current).support, good n next)
      (n : Nat) (current : app.Execution)
      (valid : invariant good (n + 1) current)
      (running : ¬ stop current)
      (next : app.Execution) (reached : next ∈ (app.round scheduler players current).support) :
      invariant good n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, inside, goodNow, submitted, facts⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup deps) horizon scheduler
      players (remaining + n) current next before reached
    have path := reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
      players current next reached
    have unfinished : ¬ BlockDone finish current.application.config :=
      notDone _ running
    exact ⟨⟨remaining, ⟨nextTrace⟩⟩, fun later => (inside unfinished).path shaped path
      later, goodRound n current goodNow running next reached,
      honestBlockSubmissions_round scheduler bound turns reference
      decides who deviation start finish shaped publications current next before
      (inside unfinished) unfinished submitted reached,
      RunTurnFacts.round serial bound turns reference who deviation before facts reached⟩
  have coupled := ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    stop (blockReadoutOn who window)
    (invariant leftGood) (invariant rightGood)
    (by
      intro _ current other _ _ equal
      exact observedStop current other (congrArg Prod.fst equal))
    (by
      intro n current other currentValid otherValid equal running
      obtain ⟨⟨currentRest, ⟨currentTrace⟩⟩, currentInside, currentGood, currentSubmitted,
        currentFacts⟩ := currentValid
      obtain ⟨⟨otherRest, ⟨otherTrace⟩⟩, _, otherGood, _, otherFacts⟩ := otherValid
      have currentBefore : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
          (some ⟨(currentRest + n) + 1, none, current⟩) := by
        simpa only [Nat.add_assoc] using currentTrace
      have otherBefore : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
          (some ⟨(otherRest + n) + 1, none, other⟩) := by
        simpa only [Nat.add_assoc] using otherTrace
      have unfinished : ¬ BlockDone finish current.application.config := notDone _ running
      have inside := currentInside unfinished
      have currentLegal := legalFacts setup leaks horizon scheduler _ currentBefore
      have otherLegal := legalFacts setup leaks horizon scheduler _ otherBefore
      have signed := signedCommitments_history (serviceTimeouts setup deps duration) leaks
        (serviceInitialLaw setup deps) (fun state supported => by
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact ⟨_, rfl⟩) horizon scheduler currentBefore
      have sameTraffic : (bindingTraffic (serviceTimeouts setup deps duration)) leaks who current =
          (bindingTraffic (serviceTimeouts setup deps duration)) leaks who other :=
        congrArg Prod.fst equal
      have publics : current.application.publicView = other.application.publicView :=
        congrArg (fun value => value.2.2.2.2.2) sameTraffic
      have cuts := cut_eq_of_publicView_eq publics
      have recalls : current.environmentRecall = other.environmentRecall :=
        congrArg (fun value => value.2.2.1) sameTraffic
      have views : current.application.playerView who = other.application.playerView who :=
        congrArg (fun value => value.2.2.2.2.1) sameTraffic
      have inWindow (event : (serviceGraph setup deps).EventId)
          (ready : current.application.config.cut.Ready event) :
          start ≤ event.val ∧ event.val < finish :=
        shaped _ inside unfinished event ready
      have otherRunning : ¬ stop other := fun stopped =>
        running ((observedStop current other sameTraffic).mpr stopped)
      have agreeAtNow := agreeAt n current other currentGood otherGood cuts running otherRunning
      have agreeNow : ∀ (event : (serviceGraph setup deps).EventId) (owner : Player)
          (payload : L.Ty)
          (binding : FieldRef (serviceGraph setup deps).layout (.binding owner payload))
          (checks : List (GuardCheck (serviceGraph setup deps).layout payload))
          (outputEq : (serviceGraph setup deps).outputLayout event = .publication payload)
          (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
            ((serviceGraph setup deps).nodes event) = .resolve owner payload binding checks),
          nodeView (serviceGraph setup deps) event =
            .resolve owner payload binding checks outputEq codeEq →
          current.application.config.cut.Ready event →
          (owner ≠ who → openingAccepted event current.application.config.store =
            openingAccepted event other.application.config.store) ∧
          (openingAccepted event current.application.config.store = true ∨ owner = who →
            binding.get? current.application.config.store =
              binding.get? other.application.config.store) := by
        intro event owner payload binding checks outputEq codeEq node ready
        have owned := nodeView_resolve_actor outputEq codeEq
        have otherReady : other.application.config.cut.Ready event := by
          rw [← cuts]
          exact ready
        exact agreeAtNow event owner payload binding checks outputEq codeEq node ready
          (current.application.active_of_ready_owned currentLegal.quiescent ready owned)
          (other.application.active_of_ready_owned otherLegal.quiescent otherReady owned)
      apply blockRoundOn_readout_congr scheduler who window players equal
      · intro actor other' selected sample sampled
        exact honest_block_matched_of_turns bound turns reference decides who deviation
          sameTraffic currentBefore otherBefore
          (fun event ready => publications event (inWindow event ready).1
            (inWindow event ready).2)
          (fun event owner payload binding checks outputEq codeEq node honest ready =>
            have facts := agreeNow event owner payload binding checks outputEq codeEq node ready
            ⟨facts.1 honest, fun accepted => facts.2 (Or.inl accepted)⟩)
          actor other'
          (fun event _ =>
            have turnsIff := ownerTurns_eq_zero_congr currentFacts.1 currentFacts.2.1
              otherFacts.1 otherFacts.2.1 recalls actor event
            ⟨turnsIff, fun first =>
              (eventRecorded_eq_false_of_ownerTurns (currentFacts.2.2 actor other').1
                first).trans (eventRecorded_eq_false_of_ownerTurns
                  (otherFacts.2.2 actor other').1 (turnsIff.mp first)).symm⟩)
          selected sample sampled
      · intro id message found
        have pending := List.mem_of_find?_eq_some found
        apply block_handle_playerView_congr_of current.application other.application who views
          currentLegal.binding otherLegal.binding
        intro named candidate raw call owner payload binding checks outputEq codeEq node ready
          sent
        have bounds := inWindow named ready
        have stored := (agreeNow named owner payload binding checks outputEq codeEq node
          ready).2
        by_cases isWho : owner = who
        · exact stored (Or.inr isWho)
        apply stored
        left
        have called : message.payload.call = .opening named candidate raw := call
        have senderOwner : message.sender = owner := sent
        obtain ⟨entry, entryMember, _, _, emitted, _⟩ :=
          currentLegal.provenance.pending message pending
        obtain ⟨_, _, transmitted, packet⟩ :=
          signed.emissions message.sender entry entryMember message emitted
        have submitted : (submittedEvent? (serviceTimeouts setup deps duration)) leaks
            entry.action = some named := by
          simp only [EventGraphRuntime.submittedEvent?, transmitted]
          rw [← packet, called]
          rfl
        rw [senderOwner] at entryMember
        exact (currentSubmitted owner isWho entry entryMember named bounds.1 bounds.2
          submitted).2)
    (advance leftGood leftRound) (advance rightGood rightRound) count left right
    ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, leftInside, leftStart, leftValid, leftFacts⟩
    ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, rightInside, rightStart, rightValid, rightFacts⟩
    (by rw [readoutOf, readoutOf, same])
  have projected := congrArg (PMF.map Prod.fst) coupled
  simpa only [PMF.map_comp, Function.comp_def, readoutOf] using projected


end Vegas
