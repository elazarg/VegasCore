/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.RevealBlockRecords

/-! # Coupling a block of concurrent reveals

Two block runs give the deviator the same traffic law when they start from
equal deviator traffic and equal counters at the block's events, and agree on
which honest reveals open and on the stored values those openings publish.
Reveals whose opening is rejected may store different values: an honest
effective-opening client never opens them, and an opening sent by anyone else is
rejected.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {mode : EventGraph.ExecutionMode} {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

/-- The window of the events of ranks in `[start, finish)`. -/
def blockWindow (start finish : Nat) : (serviceGraph setup mode).EventId → Bool :=
  fun event => decide (start ≤ event.val ∧ event.val < finish)

/-- Two configurations agree on the block's reveals pending in the first: their
footprints are stored, an honest one is accepted alike, and an accepted reveal,
or one of the deviator, stores the same binding. -/
def AcceptedAgree (who : Player) (start finish : Nat)
    (left right : (serviceGraph setup mode).Config) : Prop :=
  ∀ (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
    nodeView (serviceGraph setup mode) event =
      .resolve owner payload binding checks outputEq codeEq →
    start ≤ event.val → event.val < finish → event ∉ left.cut.completed →
    (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (left.store field).isSome) ∧
    (∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (right.store field).isSome) ∧
    (owner ≠ who → openingAccepted event left.store = openingAccepted event right.store) ∧
    (openingAccepted event left.store = true ∨ owner = who →
      binding.get? left.store = binding.get? right.store)

/-- Acceptance with a stored footprint persists along graph paths. -/
theorem openingAccepted_path_eq {before after : (serviceGraph setup mode).Config}
    (path : Relation.ReflTransGen Config.Step before after)
    {event : (serviceGraph setup mode).EventId}
    (available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
      (before.store field).isSome) :
    openingAccepted event after.store = openingAccepted event before.store := by
  apply openingAccepted_congr event
  intro field read
  obtain ⟨value, stored⟩ := Option.isSome_iff_exists.mp (available field read)
  rw [Config.Step.path_store_of_some path field value stored, stored]

/-- Agreement on the block's reveals persists along graph paths. -/
theorem AcceptedAgree.path {who : Player} {start finish : Nat}
    {left right left' right' : (serviceGraph setup mode).Config}
    (agree : AcceptedAgree who start finish left right)
    (leftPath : Relation.ReflTransGen Config.Step left left')
    (rightPath : Relation.ReflTransGen Config.Step right right') :
    AcceptedAgree who start finish left' right' := by
  intro event owner payload binding checks outputEq codeEq node early late pending
  obtain ⟨leftAvailable, rightAvailable, accepted, stored⟩ :=
    agree event owner payload binding checks outputEq codeEq node early late
      (fun done => pending (Config.Step.path_completed_mono leftPath done))
  have footprint := EventCode.readFields_cast outputEq ((serviceGraph setup mode).nodes event)
  rw [codeEq] at footprint
  have read : binding.field ∈ ((serviceGraph setup mode).nodes event).readFields := by
    rw [← footprint]
    exact Finset.mem_insert_self _ _
  have keep {small large : (serviceGraph setup mode).Config}
      (path : Relation.ReflTransGen Config.Step small large)
      (available : ∀ field ∈ ((serviceGraph setup mode).nodes event).readFields,
        (small.store field).isSome) (field : (serviceGraph setup mode).Field)
      (member : field ∈ ((serviceGraph setup mode).nodes event).readFields) :
      large.store field = small.store field := by
    obtain ⟨value, kept⟩ := Option.isSome_iff_exists.mp (available field member)
    rw [Config.Step.path_store_of_some path field value kept, kept]
  refine ⟨fun field member => ?_, fun field member => ?_, ?_, fun opened => ?_⟩
  · rw [keep leftPath leftAvailable field member]
    exact leftAvailable field member
  · rw [keep rightPath rightAvailable field member]
    exact rightAvailable field member
  · intro honest
    rw [openingAccepted_path_eq leftPath leftAvailable,
      openingAccepted_path_eq rightPath rightAvailable, accepted honest]
  · rw [openingAccepted_path_eq leftPath leftAvailable] at opened
    rw [FieldRef.get?_congr binding left'.store left.store
        (keep leftPath leftAvailable _ read),
      FieldRef.get?_congr binding right'.store right.store
        (keep rightPath rightAvailable _ read)]
    exact stored opened

/-- **The traffic of a block.** Two executions inside the block whose honest
submissions are accepted, which agree on the block's reveals, and which have
equal deviator traffic and equal counters at the block's events give equal laws
of that readout when run to the end of the block, when honest clients open a
reveal exactly when its opening is accepted. -/
theorem block_stopped_readoutOn_congr {horizon : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (reference : (serviceGraph setup mode).BehavioralProfile)
    (decides : ∀ (config : (serviceGraph setup mode).Config)
      (event : (serviceGraph setup mode).EventId) (owner : Player) (payload : L.Ty)
      (binding : FieldRef (serviceGraph setup mode).layout (.binding owner payload))
      (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
      (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
      (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
        ((serviceGraph setup mode).nodes event) = .resolve owner payload binding checks),
      nodeView (serviceGraph setup mode) event =
        .resolve owner payload binding checks outputEq codeEq →
      ∀ (actor : (serviceGraph setup mode).actor? event = some owner)
        (active : owner ∉ ((serviceGraph setup mode).playerObserve owner config).defaulted),
        reference owner event actor ((serviceGraph setup mode).playerObserve owner config)
          active = PMF.pure (cast (congrArg EventField.Action outputEq.symm)
            (openingAccepted event config.store))) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (start finish : Nat) (shaped : BlockShaped (graph := serviceGraph setup mode) start finish)
    (publications : ∀ event : (serviceGraph setup mode).EventId, start ≤ event.val →
      event.val < finish → ((serviceGraph setup mode).outputLayout event).IsPublication) :
    ∀ (count leftRemaining rightRemaining : Nat)
      (left right : (serviceApplication setup mode deadline leaks).Execution),
      ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨leftRemaining + count, none, left⟩) →
      ((serviceApplication setup mode deadline leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
          (some ⟨rightRemaining + count, none, right⟩) →
      (¬ BlockDone finish left.application.config →
        InBlock start finish left.application.config) →
      (¬ BlockDone finish right.application.config →
        InBlock start finish right.application.config) →
      HonestBlockSubmissions who start finish left →
      HonestBlockSubmissions who start finish right →
      AcceptedAgree who start finish left.application.config right.application.config →
      blockReadoutOn who (blockWindow start finish) left =
        blockReadoutOn who (blockWindow start finish) right →
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference) who deviation)
        (fun final => BlockDone finish final.application.config) count left).map
          (blockReadoutOn who (blockWindow start finish)) =
      ((serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound turns
          (firstTurnTiming setup turns mode) reference) who deviation)
        (fun final => BlockDone finish final.application.config) count right).map
          (blockReadoutOn who (blockWindow start finish)) := by
  intro count leftRemaining rightRemaining left right leftTrace rightTrace leftInside
    rightInside leftValid rightValid agree same
  let app := serviceApplication setup mode deadline leaks
  let players := Function.update (serviceReferenceTurnPolicy setup mode deadline leaks bound
    turns (firstTurnTiming setup turns mode) reference) who deviation
  let window := blockWindow (setup := setup) (mode := mode) start finish
  let invariant := fun (origin : app.Execution) (count : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    Relation.ReflTransGen Config.Step origin.application.config current.application.config ∧
    HonestBlockSubmissions who start finish current
  have advance (origin : app.Execution) (n : Nat) (current : app.Execution)
      (valid : invariant origin (n + 1) current)
      (running : ¬ BlockDone finish current.application.config)
      (next : app.Execution) (reached : next ∈ (app.round scheduler players current).support) :
      invariant origin n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, inside, walked, submitted⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon scheduler
      players (remaining + n) current next before reached
    have path := reactive_round_graph_steps (serviceRuntime setup mode deadline) leaks scheduler
      players current next reached
    exact ⟨⟨remaining, ⟨nextTrace⟩⟩, fun unfinished => (inside running).path shaped path
      unfinished, walked.trans path, honestBlockSubmissions_round scheduler bound turns reference
      decides who deviation start finish shaped publications current next before
      (inside running) running submitted reached⟩
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    (fun final => BlockDone finish final.application.config) (blockReadoutOn who window)
    (invariant left) (invariant right)
  · intro n current other _ _ equal
    have publics : current.application.publicView = other.application.publicView :=
      congrArg (fun value => value.1.2.2.2.2.2) equal
    have cuts := cut_eq_of_publicView_eq publics
    simp only [BlockDone, cuts]
  · intro n current other currentValid otherValid equal running
    obtain ⟨⟨currentRest, ⟨currentTrace⟩⟩, currentInside, currentPath, currentSubmitted⟩ :=
      currentValid
    obtain ⟨⟨otherRest, ⟨otherTrace⟩⟩, _, otherPath, _⟩ := otherValid
    have currentBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(currentRest + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using currentTrace
    have otherBefore : (app.protocol (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨(otherRest + n) + 1, none, other⟩) := by
      simpa only [Nat.add_assoc] using otherTrace
    have inside := currentInside running
    have agreeNow := agree.path currentPath otherPath
    have currentFacts := legalFacts setup leaks horizon scheduler _ currentBefore
    have otherFacts := legalFacts setup leaks horizon scheduler _ otherBefore
    have signed := signedCommitments_history (serviceRuntime setup mode deadline) leaks
      (serviceInitialLaw setup mode) (fun state supported => by
        obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
        exact ⟨_, rfl⟩) horizon scheduler currentBefore
    have sameTraffic : (serviceRuntime setup mode deadline).bindingTraffic leaks who current =
        (serviceRuntime setup mode deadline).bindingTraffic leaks who other :=
      congrArg Prod.fst equal
    have views : current.application.playerView who = other.application.playerView who :=
      congrArg (fun value => value.1.2.2.2.2.1) equal
    have inWindow (event : (serviceGraph setup mode).EventId)
        (ready : current.application.config.cut.Ready event) :
        start ≤ event.val ∧ event.val < finish :=
      shaped _ inside running event ready
    apply blockRoundOn_readout_congr scheduler who window players equal
    · intro actor other' selected sample sampled
      exact honest_block_matched_of bound turns reference decides who deviation sameTraffic
        currentBefore otherBefore
        (fun event ready => publications event (inWindow event ready).1
          (inWindow event ready).2)
        (fun event owner payload binding checks outputEq codeEq node honest ready =>
          have facts := agreeNow event owner payload binding checks outputEq codeEq node
            (inWindow event ready).1 (inWindow event ready).2 ready.1
          ⟨facts.2.2.1 honest, fun accepted => facts.2.2.2 (Or.inl accepted)⟩)
        actor other' (fun event ready => by
          have counted := congrFun (congrFun (congrArg Prod.snd equal) actor) event
          have admitted : window event = true := by
            simp only [window, blockWindow, decide_eq_true_eq]
            exact inWindow event ready
          simpa only [blockReadoutOn, blockCountersOn, admitted, ite_true] using counted)
        selected sample sampled
    · intro id message found
      have pending := List.mem_of_find?_eq_some found
      apply block_handle_playerView_congr_of current.application other.application who views
        currentFacts.binding otherFacts.binding
      intro named candidate raw call owner payload binding checks outputEq codeEq node ready sent
      have bounds := inWindow named ready
      obtain ⟨_, _, _, stored⟩ := agreeNow named owner payload binding checks outputEq codeEq
        node bounds.1 bounds.2 ready.1
      by_cases isWho : owner = who
      · exact stored (Or.inr isWho)
      apply stored
      left
      have called : message.payload.call = .opening named candidate raw := call
      have senderOwner : message.sender = owner := sent
      obtain ⟨entry, entryMember, _, _, emitted, _⟩ :=
        currentFacts.provenance.pending message pending
      obtain ⟨_, _, transmitted, packet⟩ :=
        signed.emissions message.sender entry entryMember message emitted
      have submitted : (serviceRuntime setup mode deadline).submittedEvent? leaks entry.action =
          some named := by
        simp only [EventGraphRuntime.submittedEvent?, transmitted]
        rw [← packet, called]
        rfl
      rw [senderOwner] at entryMember
      exact (currentSubmitted owner isWho entry entryMember named bounds.1 bounds.2
        submitted).2
  · exact advance left
  · exact advance right
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, leftInside, .refl, leftValid⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, rightInside, .refl, rightValid⟩
  · exact same

end Vegas
