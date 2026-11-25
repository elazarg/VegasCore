module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Pending.ForeignBindingTraffic
public import Vegas.Pending.EventBindingInvariant
public import Vegas.Pending.ReactiveGuardedResponse

@[expose] public section

/-! # Native traffic at a fixed foreign publication -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {inputs : PMF graph.Inputs}

local notation "app" => reactiveApplication timeouts leaks

/-- An authentic opening of the same stored value has the same public and
focal private effect, including public default control. -/
theorem handle_opening_playerView_congr
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks}
    (node : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : EventGraphRuntime.State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (leftInvariant : left.BindingInvariant) (rightInvariant : right.BindingInvariant)
    (value : L.Val payload)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value))
    (id : MessageId Player) (candidate : Handle graph) (raw : Raw L) :
    (handle timeouts left ⟨id, .opening event candidate raw⟩).map
        (fun state => state.playerView focal) =
      (handle timeouts right ⟨id, .opening event candidate raw⟩).map
        (fun state => state.playerView focal) := by
  classical
  have publics := congrArg PlayerView.publicView views
  have accepted : left.accepted = right.accepted := congrArg PublicView.accepted publics
  have status : left.config.defaulted = right.config.defaulted :=
    congrArg (fun view : PublicView graph => view.observation.defaulted) publics
  have clocks : left.clock = right.clock := congrArg PublicView.clock publics
  have activations : left.activatedAt = right.activatedAt := congrArg PublicView.activatedAt publics
  by_cases inactive : id.1 ∈ left.config.defaulted
  · simp only [handle, Message.sender, inactive, ← status, ite_true, Option.map_none]
  have rightActive : id.1 ∉ right.config.defaulted := by rwa [← status]
  by_cases timely : left.WithinDeadline timeouts event
  · have rightTimely : right.WithinDeadline timeouts event := by
      unfold State.WithinDeadline at timely ⊢
      rw [← activations, ← clocks]
      exact timely
    by_cases sender : id.1 = owner
    · by_cases handleOwner : candidate.1 = owner
      · by_cases associated : left.accepted binding.field = some candidate
        · have rightAssociated : right.accepted binding.field = some candidate := by
            rwa [← accepted]
          obtain ⟨leftHandle, leftAccepted, _leftOwner, leftLookup⟩ :=
            leftInvariant.success_provenance binding value leftStored
          have leftHandleEq : leftHandle = candidate :=
            Option.some.inj (leftAccepted.symm.trans associated)
          subst leftHandle
          obtain ⟨rightHandle, rightAccepted, _rightOwner, rightLookup⟩ :=
            rightInvariant.success_provenance binding value rightStored
          have rightHandleEq : rightHandle = candidate :=
            Option.some.inj (rightAccepted.symm.trans rightAssociated)
          subst rightHandle
          by_cases sameRaw : raw = ⟨payload, value⟩
          · subst raw
            have stores : graph.publicStore left.config.store =
                graph.publicStore right.config.store :=
              congrArg (fun view : PublicView graph =>
                view.observation.store) publics
            have resolved : EventCode.resolveOutput? binding checks true left.config.store =
                EventCode.resolveOutput? binding checks true right.config.store := by
              unfold EventCode.resolveOutput?
              rw [leftStored, rightStored]
              simp only [Option.bind_eq_bind, Option.bind_some, ↓reduceIte]
              rw [← GuardCheck.allAccepted?_publicStore checks left.config.store,
                ← GuardCheck.allAccepted?_publicStore checks right.config.store, stores]
            have available : (EventCode.resolveOutput? binding checks true
                left.config.store).isSome = true := by
              apply EventCode.resolveOutput?_isSome
              intro field read
              apply left.config.read_available leftReady
              rw [← EventCode.readFields_cast outputEq
                (graph.nodes event), codeEq]
              exact read
            obtain ⟨result, evaluated⟩ := Option.isSome_iff_exists.mp available
            rw [handle_opening_eq timeouts left id event candidate
                owner payload binding checks outputEq codeEq node leftReady timely inactive
                sender handleOwner associated value leftLookup leftStored result evaluated,
              handle_opening_eq timeouts right id event candidate
                owner payload binding checks outputEq codeEq node rightReady rightTimely
                rightActive sender handleOwner rightAssociated value rightLookup rightStored
                result (resolved ▸ evaluated)]
            simp only [Option.map_some]
            apply congrArg some
            apply State.complete_playerView_congr left right focal publics
              (left.playerView_observation_eq right focal views)
              (congrArg PlayerView.candidates views)
              event leftReady rightReady _ _ _ _ (fun _ => rfl) (fun _ => rfl)
            rw [left.config.completion_defaultEvent_of_code event outputEq
              (.resolve owner payload binding checks) codeEq,
              right.config.completion_defaultEvent_of_code event outputEq
                (.resolve owner payload binding checks) codeEq, status]
          · have leftFalse : left.candidates.verify candidate raw = false := by
              apply Bool.eq_false_of_not_eq_true
              intro valid
              have lookup := (CommitmentCandidates.verify_eq_true_iff _ _ _).mp valid
              rw [leftLookup] at lookup
              exact sameRaw (CommitmentCandidate.openable.inj lookup).symm
            have rightFalse : right.candidates.verify candidate raw = false := by
              apply Bool.eq_false_of_not_eq_true
              intro valid
              have lookup := (CommitmentCandidates.verify_eq_true_iff _ _ _).mp valid
              rw [rightLookup] at lookup
              exact sameRaw (CommitmentCandidate.openable.inj lookup).symm
            simp [handle, Message.sender, leftReady, rightReady, timely, rightTimely, node,
              sender, handleOwner, associated, rightAssociated, leftFalse, rightFalse]
        · have rightUnassociated : right.accepted binding.field ≠ some candidate := by
            rwa [← accepted]
          simp [handle, Message.sender, leftReady, rightReady, timely, rightTimely, node,
            sender, handleOwner, associated, rightUnassociated]
      · simp [handle, Message.sender, leftReady, rightReady, timely, rightTimely, node,
          sender, handleOwner]
    · simp [handle, Message.sender, inactive, rightActive, leftReady, rightReady,
        timely, rightTimely, node, sender]
  · have rightLate : ¬ right.WithinDeadline timeouts event := by
      unfold State.WithinDeadline at timely ⊢
      rw [← activations, ← clocks]
      exact timely
    simp [handle, Message.sender, inactive, rightActive, leftReady, rightReady, timely, rightLate]


/-- The canonical opening of a stored successful binding is exactly its opening
submission. -/
theorem canonical_opening_exact
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (execution : (app).Execution)
    (recalled : execution.InputRecall (app))
    (candidate : Handle graph) (value : L.Val payload)
    (accepted : execution.application.accepted binding.field = some candidate)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable ⟨payload, value⟩)
    (active : owner ∉ execution.application.config.defaulted)
    (stored : binding.get? execution.application.config.store = some (.success value)) :
    (canonicalServiceDecision timeouts) leaks owner
      (execution.logs owner) (execution.observe
        (app) owner) event
      (cast (congrArg EventField.Action outputEq.symm) true) =
      ⟨some ((disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
        owner ((app).observePlayer
          execution.application owner) (execution.network.known owner))⟩ := by
  rw [(canonicalServiceDecision_eq_of_not_bind timeouts) leaks owner
    (execution.logs owner) (execution.observe
      (app) owner) event _ (by
        intro other otherPayload otherEq otherCode same
        rw [node] at same
        cases same)]
  exact (serviceDecision_authentic_opening timeouts) leaks execution
    recalled owner event payload binding checks outputEq codeEq node candidate value
    accepted owned fixed active stored

/-- The packet of a normalized opening submission names its event, candidate and raw
value. -/
theorem opening_normal_packet
    (execution : (app).Execution)
    (owner : Player) (event : graph.EventId)
    (candidate : Handle graph) (raw : Raw L)
    (owned : candidate.1 = owner)
    (fixed : execution.application.candidates.lookup candidate = .openable raw) :
    let material := (disclosureSubmission (.opening event candidate raw)).normalizeReactive
      owner ((app).observePlayer execution.application owner) (execution.network.known owner)
    (app).packet ((app).submit execution.application owner material) owner
      (execution.network.known owner) material =
      ⟨.opening event candidate raw, some ⟨candidate, raw⟩,
        execution.application.publicView.tokenFor (.opening event candidate raw)⟩ := by
  intro material
  let original := disclosureSubmission (.opening event candidate raw)
  let normal := (reactiveNormalization timeouts) leaks
  change (app).packet ((app).submit execution.application owner
      (normal.normalize owner ((app).observePlayer execution.application owner)
        (execution.network.known owner) original)) owner (execution.network.known owner)
      (normal.normalize owner ((app).observePlayer execution.application owner)
        (execution.network.known owner) original) = _
  rw [normal.submit, normal.packet]
  change WitnessedPacket.mk _ _ _ = WitnessedPacket.mk _ _ _
  congr 1
  exact WitnessedSubmission.emit_owned original.call
    ((app).submit execution.application owner original) owner (execution.network.known owner)
    ⟨candidate, raw⟩ owned (by
      change execution.application.candidates.lookup candidate = .openable raw
      exact fixed)

private theorem opening_response_matched
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (app).Scheduler}
    {bound : graph.EventId → Nat}
    {event : graph.EventId} {owner focal : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (ownerSolitary : graph.OwnerSolitary event)
    (foreign : owner ≠ focal)
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    {left right : (app).Execution}
    (same : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right)
    (leftTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (value : L.Val payload)
    (leftStored : binding.get? left.application.config.store = some (.success value))
    (rightStored : binding.get? right.application.config.store = some (.success value))
    (selected : (.activate owner : (app).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (app))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((app).observePending owner
      left.network.pending).support) :
    let leftActive := left.sampledActivation (app)
      owner sample
    let rightActive := right.sampledActivation (app)
      owner sample
    ∃ leftResponse rightResponse,
      decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) true)
        (leftActive.logs owner) (leftActive.observe
          (app) owner) = PMF.pure leftResponse ∧
      decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) true)
        (rightActive.logs owner) (rightActive.observe
          (app) owner) = PMF.pure rightResponse ∧
      (submittedEvent? timeouts) leaks leftResponse =
        (submittedEvent? timeouts) leaks rightResponse ∧
      (bindingTraffic timeouts) leaks focal
        (leftActive.respond (app) owner leftResponse) =
      (bindingTraffic timeouts) leaks focal
        (rightActive.respond (app) owner
          rightResponse) := by
  intro leftActive rightActive
  let action := cast (congrArg EventField.Action outputEq.symm) true
  have sameTraffic : (bindingTraffic timeouts) leaks focal left =
      (bindingTraffic timeouts) leaks focal right := congrArg Prod.fst same
  have sameTurns : ownerTurns owner event left = ownerTurns owner event right :=
    congrArg (fun value => value.2.1) same
  have sameRecorded : (eventRecorded timeouts) leaks (left.logs owner) event =
      (eventRecorded timeouts) leaks (right.logs owner) event :=
    congrArg (fun value => value.2.2) same
  have publics : left.application.publicView = right.application.publicView :=
    congrArg (fun value => value.2.2.2.2.2) sameTraffic
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun value => value.2.2.1) sameTraffic
  have networks : left.network = right.network := congrArg Prod.fst sameTraffic
  have activated := bindingTraffic_activation timeouts leaks left right focal owner
    sameTraffic sample
  have owned : graph.actor? event = some owner :=
    nodeView_resolve_actor outputEq codeEq
  by_cases opened : ownerTurns owner event left = 0 ∧
      (eventRecorded timeouts) leaks (left.logs owner) event = false ∧
      left.application.publicView.InclusionFitsDeadline timeouts bound event
  · obtain ⟨first, unrecorded, fits⟩ := opened
    have rightFirst : ownerTurns owner event right = 0 := sameTurns ▸ first
    have rightUnrecorded : (eventRecorded timeouts) leaks (right.logs owner) event = false :=
      sameRecorded ▸ unrecorded
    have rightFits : right.application.publicView.InclusionFitsDeadline timeouts bound event :=
      publics ▸ fits
    have leftMoved : leftActive ∈ (left.environmentStep app (.activate owner)).support := by
      rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
      exact ⟨sample, sampled, rfl⟩
    have rightMoved : rightActive ∈ (right.environmentStep app (.activate owner)).support := by
      rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
      exact ⟨sample, by rw [← networks]; exact sampled, rfl⟩
    obtain ⟨leftActiveTrace⟩ := (app).raw_trace_environment (inputs.map State.initial) horizon
      scheduler leftRemaining left leftActive (.activate owner) leftTrace selected leftMoved
    obtain ⟨rightActiveTrace⟩ := (app).raw_trace_environment (inputs.map State.initial) horizon
      scheduler rightRemaining right rightActive (.activate owner) rightTrace (by
        rw [← environments, ← observeEnvironment_eq_of_bindingTraffic focal sameTraffic]
        exact selected) rightMoved
    have leftFacts := legalFacts timeouts leaks inputs horizon scheduler _ leftActiveTrace
    have rightFacts := legalFacts timeouts leaks inputs horizon scheduler _ rightActiveTrace
    obtain ⟨candidate, leftAccepted, candidateOwner, leftFixed⟩ :=
      leftFacts.binding.success_provenance binding value leftStored
    have rightAccepted : rightActive.application.accepted binding.field = some candidate := by
      change right.application.accepted binding.field = _
      exact (congrFun (congrArg PublicView.accepted publics) binding.field).symm.trans
        leftAccepted
    obtain ⟨rightCandidate, acceptedOther, _, rightFixed⟩ :=
      rightFacts.binding.success_provenance binding value rightStored
    have candidateEq : rightCandidate = candidate :=
      Option.some.inj (acceptedOther.symm.trans rightAccepted)
    subst rightCandidate
    have leftActiveOwner : owner ∉ leftActive.application.config.defaulted :=
      leftActive.application.active_of_ready_owned leftFacts.quiescent leftReady owned
    have rightActiveOwner : owner ∉ rightActive.application.config.defaulted :=
      rightActive.application.active_of_ready_owned rightFacts.quiescent rightReady owned
    let leftMaterial :=
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
      owner ((app).observePlayer leftActive.application owner) (leftActive.network.known owner)
    let rightMaterial :=
      (disclosureSubmission (.opening event candidate ⟨payload, value⟩)).normalizeReactive
      owner ((app).observePlayer rightActive.application owner) (rightActive.network.known owner)
    have leftDecision : (canonicalServiceDecision timeouts) leaks owner (leftActive.logs owner)
        (leftActive.observe app owner) event action = ⟨some leftMaterial⟩ :=
      canonical_opening_exact outputEq codeEq node leftActive leftFacts.inputs candidate value
        leftAccepted candidateOwner leftFixed leftActiveOwner leftStored
    have rightDecision : (canonicalServiceDecision timeouts) leaks owner (rightActive.logs owner)
        (rightActive.observe app owner) event action = ⟨some rightMaterial⟩ :=
      canonical_opening_exact outputEq codeEq node rightActive rightFacts.inputs candidate value
        rightAccepted candidateOwner rightFixed rightActiveOwner rightStored
    refine ⟨⟨some leftMaterial⟩, ⟨some rightMaterial⟩, ?_, ?_, ?_, ?_⟩
    · rw [decidedTurnPolicy_open action leftActive
        (leftActive.application.ownTurn?_of_ready ownerSolitary leftReady owned) first,
        decidedOpportunity_transmits action leftActive unrecorded fits _ leftDecision]
    · rw [decidedTurnPolicy_open action rightActive
        (rightActive.application.ownTurn?_of_ready ownerSolitary rightReady owned) rightFirst,
        decidedOpportunity_transmits action rightActive rightUnrecorded rightFits _ rightDecision]
    · rfl
    · apply bindingTraffic_respond_other foreign.symm activated
      refine Or.inr ⟨_, _, rfl, rfl, ?_⟩
      rw [opening_normal_packet leftActive owner event candidate ⟨payload, value⟩ candidateOwner
        leftFixed, opening_normal_packet rightActive owner event candidate ⟨payload, value⟩
        candidateOwner rightFixed]
      have activePublics : leftActive.application.publicView =
          rightActive.application.publicView := publics
      rw [activePublics]
  · have rightClosed : ¬ (ownerTurns owner event right = 0 ∧
        (eventRecorded timeouts) leaks (right.logs owner) event = false ∧
        right.application.publicView.InclusionFitsDeadline timeouts bound event) := by
      rw [← sameTurns, ← sameRecorded, ← publics]
      exact opened
    exact ⟨⟨none⟩, ⟨none⟩, decidedTurnPolicy_closed action leftActive
        (leftActive.application.ownTurn?_of_ready ownerSolitary leftReady owned) opened,
      decidedTurnPolicy_closed action rightActive
        (rightActive.application.ownTurn?_of_ready ownerSolitary rightReady owned) rightClosed, rfl,
      bindingTraffic_respond_other foreign.symm activated _ _ (Or.inl ⟨rfl, rfl⟩)⟩


private theorem opening_ready_handler
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    {outputEq : graph.outputLayout event = .publication payload}
    {codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks}
    (node : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : EventGraphRuntime.State graph) (focal : Player)
    (views : left.playerView focal = right.playerView focal)
    (leftReady : left.config.cut.Ready event) (rightReady : right.config.cut.Ready event)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftInvariant : left.BindingInvariant) (rightInvariant : right.BindingInvariant)
    (value : L.Val payload)
    (leftStored : binding.get? left.config.store = some (.success value))
    (rightStored : binding.get? right.config.store = some (.success value))
    (message : Message Player (Payload graph)) :
    (handle timeouts left message).map
        (fun state => state.playerView focal) =
      (handle timeouts right message).map
        (fun state => state.playerView focal) := by
  classical
  obtain ⟨id, packet⟩ := message
  cases packet with
  | malformed raw => simp [handle]
  | commitment named candidate =>
      exact handle_commitment_playerView_congr timeouts left right focal id named candidate views
  | opening named candidate raw =>
      by_cases namedReady : left.config.cut.Ready named
      · have namedEq := alone _ named leftReady namedReady
        subst named
        exact handle_opening_playerView_congr node left right focal views leftReady rightReady
          leftInvariant rightInvariant value leftStored rightStored id candidate raw
      · have cuts := cut_eq_of_publicView_eq (congrArg PlayerView.publicView views)
        have rightNot : ¬right.config.cut.Ready named := by simpa only [← cuts] using namedReady
        simp [handle, namedReady, rightNot]

private theorem opening_stopped_readout_congr
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (app).Scheduler)
    (focal : Player) (deviation : (app).Policy)
    (bound : graph.EventId → Nat)
    {event : graph.EventId} {owner : Player} {payload : L.Ty}
    {binding : FieldRef graph.layout (.binding owner payload)}
    {checks : List (GuardCheck graph.layout payload)}
    (foreign : owner ≠ focal)
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event =
      .resolve owner payload binding checks outputEq codeEq)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (app).Execution)
    (leftTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (value : L.Val payload)
    (leftStored : binding.get? leftStart.application.config.store = some (.success value))
    (rightStored : binding.get? rightStart.application.config.store = some (.success value))
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    ((app).runUntil scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy timeouts leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        (foreignReadout (leaks := leaks) focal owner event) =
    ((app).runUntil scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy timeouts leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        (foreignReadout (leaks := leaks) focal owner event) := by
  have ownerSolitary : graph.OwnerSolitary event :=
    (show graph.Solitary event from
      fun cut _ otherReady ready => alone cut _ ready otherReady).ownerSolitary
  let players := Function.update
    (focalPlayers timeouts leaks focal deviation) owner
    (decidedTurnPolicy timeouts leaks bound owner event
      (cast (congrArg EventField.Action outputEq.symm) true))
  let invariant := fun (start : (app).Execution) (count : Nat) (current : (app).Execution) =>
    (∃ remaining, Nonempty (((app).protocol (inputs.map State.initial) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config = start.application.config)
  have owned : graph.actor? event = some owner :=
    nodeView_resolve_actor outputEq codeEq
  have advance (start : (app).Execution) (startReady : start.application.config.cut.Ready event)
      (n : Nat) (current : (app).Execution) (valid : invariant start (n + 1) current)
      (running : event ∉ current.application.config.cut.completed) (next : (app).Execution)
      (reached : next ∈ ((app).round scheduler players current).support) :
      invariant start n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, framed⟩ := valid
    have before : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := (app).raw_trace_round (inputs.map State.initial) horizon scheduler
      players (remaining + n) current next before reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_⟩
    intro unfinished
    have currentReady : current.application.config.cut.Ready event :=
      (framed running).symm ▸ startReady
    exact (reactive_round_config_eq_of_pending timeouts leaks
      scheduler players event current next
      (fun query queryReady => alone _ query currentReady queryReady) unfinished reached).trans
        (framed running)
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    (fun final => event ∈ final.application.config.cut.completed)
    (foreignReadout (leaks := leaks) focal owner event)
    (invariant leftStart) (invariant rightStart)
  · intro n left right _leftValid _rightValid equal
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, leftFrame⟩ := leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, rightFrame⟩ := rightValid
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have currentLeftReady : left.application.config.cut.Ready event :=
      (leftFrame running).symm ▸ leftReady
    have currentRightReady : right.application.config.cut.Ready event :=
      (rightFrame rightRunning).symm ▸ rightReady
    have leftBefore : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(leftRest + n) + 1, none, left⟩) := by
      simpa only [Nat.add_assoc] using leftCurrentTrace
    have rightBefore : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(rightRest + n) + 1, none, right⟩) := by
      simpa only [Nat.add_assoc] using rightCurrentTrace
    have currentLeftStored : binding.get? left.application.config.store =
        some (.success value) := by rw [leftFrame running]; exact leftStored
    have currentRightStored : binding.get? right.application.config.store =
        some (.success value) := by rw [rightFrame rightRunning]; exact rightStored
    apply foreignRound_readout_congr scheduler focal deviation owned foreign alone _ _
      currentLeftReady currentRightReady equal
    · intro selected sample sampled
      exact opening_response_matched ownerSolitary foreign outputEq codeEq node equal leftBefore
        rightBefore
        currentLeftReady currentRightReady value currentLeftStored currentRightStored
        selected sample sampled
    · intro id message _found _sender
      exact opening_ready_handler node left.application right.application focal
        (congrArg (fun value => value.2.2.2.2.1) traffic) currentLeftReady currentRightReady alone
        (legalFacts timeouts leaks inputs horizon scheduler _ leftBefore).binding
        (legalFacts timeouts leaks inputs horizon scheduler _ rightBefore).binding
        value currentLeftStored currentRightStored ⟨message.id, message.payload.call⟩
  · exact advance leftStart leftReady
  · exact advance rightStart rightReady
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => rfl⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rfl⟩
  · exact same


private theorem recorded_false_round
    {scheduler : (app).Scheduler}
    {players : Player → (app).Policy}
    {owner : Player} (quiet : players owner =
      (app).silentPolicy)
    {event : graph.EventId}
    {before after : (app).Execution}
    (unrecorded : (eventRecorded timeouts) leaks
      (before.logs owner) event = false)
    (reached : after ∈ ((app).round scheduler players
      before).support) :
    (eventRecorded timeouts) leaks (after.logs owner) event =
      false := by
  obtain ⟨command, _, middle, moved, cases⟩ := round_cases timeouts leaks reached
  have recallEq := (app).environmentStep_recall before middle command moved
  have kept : (eventRecorded timeouts) leaks
      (middle.logs owner) event = false := by rw [recallEq]; exact unrecorded
  rcases cases with ⟨_, rfl⟩ | ⟨actor, _, response, chosen, rfl⟩
  · exact kept
  · by_cases same : actor = owner
    · subst actor
      rw [quiet, ReactiveApplication.silentPolicy, PMF.mem_support_pure_iff] at chosen
      subst response
      simpa only [ReactiveApplication.Execution.respond, ↓reduceIte, eventRecorded,
        List.any_append, List.any_cons, List.any_nil, submittedEvent?, reduceCtorEq,
        decide_false, Bool.false_or, Bool.or_false] using kept
    · rw [(app).respond_recall_other middle actor owner (fun equal => same equal.symm) response]
      exact kept

private theorem unrecorded_ready_handler
    {horizon remaining : Nat}
    {scheduler : (app).Scheduler}
    {owner : Player} {event : graph.EventId}
    {left right : (app).Execution}
    (trace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace (some ⟨remaining, none, left⟩))
    (unrecorded : (eventRecorded timeouts) leaks
      (left.logs owner) event = false)
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (id : MessageId Player) (message : Message Player (WitnessedPacket graph))
    (found : left.network.lookup id = some message) (sender : message.sender = owner) :
    (handle timeouts left.application ⟨message.id,
        message.payload.call⟩).map (fun state => state.playerView owner) = none ∧
    (handle timeouts right.application ⟨message.id,
        message.payload.call⟩).map (fun state => state.playerView owner) = none := by
  have notNamed : message.payload.call.event? graph ≠ some event := by
    intro named
    obtain ⟨entry, present, material, transmitted, _emitted, state, known, packet⟩ :=
      (legalFacts timeouts leaks inputs horizon scheduler _ trace).provenance.lookup
        id message found
    have old : entry ∈ left.logs owner := sender ▸ present
    have call : material.call.packet = message.payload.call :=
      congrArg (fun value => value.call) packet
    have submitted : (submittedEvent? timeouts) leaks entry.action =
        some event := by
      simp only [EventGraphRuntime.submittedEvent?, transmitted]
      rw [call]
      exact named
    have recorded := ((eventRecorded_iff timeouts) leaks _ event).mpr
      ⟨entry, old, submitted⟩
    rw [unrecorded] at recorded
    cases recorded
  have rejected (state : EventGraphRuntime.State graph)
      (ready : state.config.cut.Ready event) :
      handle timeouts state
        ⟨message.id, message.payload.call⟩ = none := by
    cases handled : handle timeouts state
        ⟨message.id, message.payload.call⟩ with
    | none => rfl
    | some next =>
        obtain ⟨query, named, queryReady, _action, _moved⟩ :=
          handle_config_mem_step timeouts state next _ handled
        have same := alone _ query ready queryReady
        subst query
        exact (notNamed named).elim
  exact ⟨by rw [rejected left.application leftReady]; rfl,
    by rw [rejected right.application rightReady]; rfl⟩

private theorem silent_foreign_stopped_readout_congr
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (app).Scheduler)
    (focal : Player) (deviation : (app).Policy)
    {event : graph.EventId} {owner : Player}
    (owned : graph.actor? event = some owner) (foreign : owner ≠ focal)
    (alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (app).Execution)
    (leftTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((app).protocol
      (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftUnrecorded : (eventRecorded timeouts) leaks
      (leftStart.logs owner) event = false)
    (rightUnrecorded : (eventRecorded timeouts) leaks
      (rightStart.logs owner) event = false)
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    let players := Function.update
      (focalPlayers timeouts leaks focal deviation) owner
      (app).silentPolicy
    ((app).runUntil scheduler players (fun final => event ∈ final.application.config.cut.completed)
      count leftStart).map (foreignReadout (leaks := leaks) focal owner event) =
    ((app).runUntil scheduler players (fun final => event ∈ final.application.config.cut.completed)
      count rightStart).map (foreignReadout (leaks := leaks) focal owner event) := by
  intro players
  let invariant := fun (start : (app).Execution) (count : Nat) (current : (app).Execution) =>
    (∃ remaining, Nonempty (((app).protocol (inputs.map State.initial) horizon scheduler).Trace
      (some ⟨remaining + count, none, current⟩))) ∧
    (event ∉ current.application.config.cut.completed →
      current.application.config = start.application.config) ∧
    (eventRecorded timeouts) leaks (current.logs owner) event = false
  have advance (start : (app).Execution) (startReady : start.application.config.cut.Ready event)
      (n : Nat) (current : (app).Execution) (valid : invariant start (n + 1) current)
      (running : event ∉ current.application.config.cut.completed) (next : (app).Execution)
      (reached : next ∈ ((app).round scheduler players current).support) :
      invariant start n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, framed, unrecorded⟩ := valid
    have before : ((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := (app).raw_trace_round (inputs.map State.initial) horizon scheduler
      players (remaining + n) current next before reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_,
      recorded_false_round (by simp only [players, Function.update_self])
        unrecorded reached⟩
    intro unfinished
    have currentReady : current.application.config.cut.Ready event :=
      (framed running).symm ▸ startReady
    exact (reactive_round_config_eq_of_pending timeouts leaks
      scheduler players event current next
      (fun query queryReady => alone _ query currentReady queryReady) unfinished reached).trans
        (framed running)
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler players players
    (fun final => event ∈ final.application.config.cut.completed)
    (foreignReadout (leaks := leaks) focal owner event)
    (invariant leftStart) (invariant rightStart)
  · intro n left right _leftValid _rightValid equal
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    rw [cut_eq_of_publicView_eq publics]
  · intro n left right leftValid rightValid equal running
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, leftFrame, unrecorded⟩ := leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, rightFrame, _⟩ := rightValid
    have traffic := congrArg Prod.fst equal
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) traffic
    have rightRunning : event ∉ right.application.config.cut.completed := by
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have currentLeftReady : left.application.config.cut.Ready event :=
      (leftFrame running).symm ▸ leftReady
    have currentRightReady : right.application.config.cut.Ready event :=
      (rightFrame rightRunning).symm ▸ rightReady
    apply foreignRound_readout_congr scheduler focal deviation owned foreign alone _ _
      currentLeftReady currentRightReady equal
    · intro _selected sample _sampled
      refine ⟨⟨none⟩, ⟨none⟩, rfl, rfl, rfl, ?_⟩
      exact bindingTraffic_respond_other foreign.symm
        (bindingTraffic_activation timeouts leaks left right
          focal owner traffic sample) _ _ (Or.inl ⟨rfl, rfl⟩)
    · intro id message found sender
      have rejected := unrecorded_ready_handler leftCurrentTrace unrecorded currentLeftReady
        currentRightReady alone id message found sender
      have leftNone : handle timeouts left.application
          ⟨message.id, message.payload.call⟩ = none := by
        cases handled : handle timeouts left.application
            ⟨message.id, message.payload.call⟩ with
        | none => rfl
        | some after => rw [handled] at rejected; cases rejected.1
      have rightNone : handle timeouts right.application
          ⟨message.id, message.payload.call⟩ = none := by
        cases handled : handle timeouts right.application
            ⟨message.id, message.payload.call⟩ with
        | none => rfl
        | some after => rw [handled] at rejected; cases rejected.2
      rw [leftNone, rightNone]
  · exact advance leftStart leftReady
  · exact advance rightStart rightReady
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => rfl, leftUnrecorded⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rfl, rightUnrecorded⟩
  · exact same


/-- Equal fixed public choices at a solitary foreign publication have equal
stopped focal traffic. For a disclosure, the raw value must also agree. -/
theorem foreign_publication_fixed_traffic_congr
    (serial : graph.ActorSerial)
    {horizon : Nat} (scheduler : (app).Scheduler)
    (bound : graph.EventId → Nat) (turns : Nat)
    (timing : EventGraphRuntime.TurnTiming graph turns)
    (reference : graph.BehavioralProfile)
    (focal owner : Player) (deviation : (app).Policy) (foreign : owner ≠ focal)
    (event : graph.EventId) (solitary : graph.Solitary event) {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq)
      (graph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (choice : Bool) (left right : (app).Execution)
    (stored : choice = true → ∃ value,
      binding.get? left.application.config.store = some (.success value) ∧
      binding.get? right.application.config.store = some (.success value)) :
    let players := Function.update (turnPolicy timeouts leaks bound turns timing reference)
      focal deviation
    PrefixBoundary (inputs.map State.initial) scheduler players event.val left →
    PrefixBoundary (inputs.map State.initial) scheduler players event.val right →
    left.environmentRecall.length ≤ horizon →
    right.environmentRecall.length ≤ horizon →
    bindingTraffic timeouts leaks focal left = bindingTraffic timeouts leaks focal right →
    let fixed := Function.update (focalPlayers timeouts leaks focal deviation) owner
      (decidedTurnPolicy timeouts leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) choice))
    let stop := fun final : (app).Execution => event ∈ final.application.config.cut.completed
    ((app).runUntilHorizon scheduler fixed stop horizon left).map
        (bindingTraffic timeouts leaks focal) =
      ((app).runUntilHorizon scheduler fixed stop horizon right).map
        (bindingTraffic timeouts leaks focal) := by
  intro players leftBoundary rightBoundary leftBounded rightBounded same fixed stop
  have follows : players owner = turnPolicy timeouts leaks bound turns timing reference owner :=
    Function.update_of_ne foreign _ _
  have facts (current : (app).Execution)
      (boundary : PrefixBoundary (inputs.map State.initial) scheduler players event.val current)
      (bounded : current.environmentRecall.length ≤ horizon) :
      Nonempty (((app).protocol (inputs.map State.initial) horizon scheduler).Trace
        (some ⟨horizon - current.environmentRecall.length, none, current⟩)) ∧
      ownerTurns owner event current = 0 ∧
      eventRecorded timeouts leaks (current.logs owner) event = false := by
    obtain ⟨own, _⟩ := canonicalSlots_roundsFrom timeouts leaks inputs serial scheduler
      players owner timing reference follows current.environmentRecall.length current
      boundary.supported
    have never : ∀ entry ∈ current.logs owner,
        entry.beforeView.application.publicView.ownTurn? owner ≠ some event := by
      intro entry member turn
      exact boundary.untouched event le_rfl owner entry member
        (entry.beforeView.application.publicView.ownTurn?_spec owner event turn).1
    refine ⟨(app).raw_trace_roundsFrom (inputs.map State.initial) horizon scheduler players
      current.environmentRecall.length bounded current boundary.supported, ?_, ?_⟩
    · apply List.countP_eq_zero.mpr
      intro entry member
      exact fun equal => never entry member (of_decide_eq_true equal)
    · apply Bool.eq_false_iff.mpr
      intro recorded
      obtain ⟨entry, member, submitted⟩ := (eventRecorded_iff timeouts leaks _ event).mp recorded
      exact never entry member (own entry member event submitted)
  obtain ⟨⟨leftTrace⟩, leftTurns, leftRecorded⟩ := facts left leftBoundary leftBounded
  obtain ⟨⟨rightTrace⟩, rightTurns, rightRecorded⟩ := facts right rightBoundary rightBounded
  have equal : foreignReadout focal owner event left = foreignReadout focal owner event right :=
    Prod.ext same (Prod.ext (leftTurns.trans rightTurns.symm)
      (leftRecorded.trans rightRecorded.symm))
  have environments : left.environmentRecall = right.environmentRecall :=
    congrArg (fun traffic => traffic.2.2.1) same
  have alone : ∀ (cut : graph.order.Cut) other, cut.Ready event →
      cut.Ready other → other = event := fun cut _ ready otherReady =>
    solitary cut otherReady ready
  rw [environments] at leftTrace
  cases choice with
  | false =>
      let action := cast (congrArg EventField.Action outputEq.symm) false
      have silent : SilentAction event action := by
        unfold SilentAction
        rw [node]
        simp only [action, cast_cast, cast_eq]
      have quiet : decidedTurnPolicy timeouts leaks bound owner event action =
          (app).silentPolicy := by
        funext past view
        exact decidedTurnPolicy_silent action silent past view
      have coupled := silent_foreign_stopped_readout_congr scheduler focal deviation
        (nodeView_resolve_actor outputEq codeEq) foreign alone left right
        (leftRemaining := 0) (rightRemaining := 0)
        (by simpa only [Nat.zero_add] using leftTrace)
        (by simpa only [Nat.zero_add] using rightTrace)
        (leftBoundary.ordered.ready event.isLt) (rightBoundary.ordered.ready event.isLt)
        leftRecorded rightRecorded equal
      have projected := congrArg (PMF.map Prod.fst) coupled
      simpa only [ReactiveApplication.runUntilHorizon, fixed, ← quiet, action, environments,
        PMF.map_comp, foreignReadout, Function.comp_def] using projected
  | true =>
      obtain ⟨value, leftStored, rightStored⟩ := stored rfl
      have coupled := opening_stopped_readout_congr scheduler focal deviation bound foreign outputEq
        codeEq node alone left right (leftRemaining := 0) (rightRemaining := 0)
        (by simpa only [Nat.zero_add] using leftTrace)
        (by simpa only [Nat.zero_add] using rightTrace)
        (leftBoundary.ordered.ready event.isLt) (rightBoundary.ordered.ready event.isLt)
        value leftStored rightStored equal
      have projected := congrArg (PMF.map Prod.fst) coupled
      simpa only [ReactiveApplication.runUntilHorizon, environments, PMF.map_comp,
        foreignReadout, Function.comp_def] using projected

end Vegas.EventGraphRuntime
