/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseOpeningMenuShape
import Vegas.Pending.PhaseBindingOpeningResponse
import Vegas.Pending.PhaseSwapInformation
import Interaction.ReactiveUniformMenu

/-! # Exact counted opening menus under directed hidden binding repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseBindingRepair

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

omit [Fintype Player] in
private theorem emit_eq_of_successful_certificate (material : WitnessedSubmission graph)
    (first second : State graph) (owner : Player)
    (known : List (Message Player (WitnessedPacket graph)))
    (publicEq : first.publicView = second.publicView) (fact : OpeningFact graph)
    (firstFixed : fact.Holds first)
    (secondFixed : fact.Holds second)
    (certified : (material.emit second owner known).evidence = some fact) :
    material.emit first owner known = material.emit second owner known := by
  rcases material with ⟨call, request⟩
  cases request with
  | none => simp only [WitnessedSubmission.emit, publicEq]
  | forward id => simp only [WitnessedSubmission.emit, publicEq]
  | owned other =>
      change (if other.handle.1 = owner ∧ second.candidates.verify other.handle other.raw then
        some other else none) = some fact at certified
      split_ifs at certified with verified
      · have same : other = fact := Option.some.inj certified
        subst other
        have left := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr firstFixed
        have right := (CommitmentCandidates.verify_eq_true_iff _ _ _).mpr secondFixed
        simp only [WitnessedSubmission.emit, verified.1, left, right, and_self,
          ↓reduceIte, publicEq]

private theorem opening_response_replay
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (owner : Player) (original repaired : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, original⟩))
    (right : PhaseCount.CountRecall runtime leaks repaired)
    (network : original.network = repaired.network)
    (publicBefore : original.application.publicView = repaired.application.publicView)
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : original.application.SeedRequest owner ⟨original.application.attempt, event⟩)
    (candidates : ∀ candidate,
      original.application.current.native.accepted binding.field = some candidate →
      original.application.current.native.candidates.lookup candidate =
        repaired.application.current.native.candidates.lookup candidate)
    (material : WitnessedSubmission graph)
    (member : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner)) :
    (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) := by
  let app := phaseApplication runtime leaks
  have raw := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace
  have left := PhaseCount.countRecall_history runtime leaks raw
  obtain ⟨candidate, value, call, _stored, accepted, originalFixed⟩ :=
    PhaseCount.onePacket_opening_shape runtime leaks bounds plan ordered inputs horizon scheduler
      remaining owner original trace event payload binding checks outputEq codeEq node request
        material member
  have repairedFixed : repaired.application.current.native.candidates.lookup candidate =
      .openable ⟨payload, value⟩ := (candidates candidate accepted).symm.trans originalFixed
  let message := PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
    (original.observe app owner) material
  have permitted : PhaseCount.permits (app.outputs (original.recall owner)) message = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
      with impossible | ⟨other, transmitted, allowed⟩
    · cases impossible
    · cases Option.some.inj transmitted
      exact allowed
  have named : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ :=
    (PhaseCount.maskPacket_call _ _).trans call
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  unfold CountCallCorrect at correct
  dsimp only [PhaseCount.nativeMessage] at correct
  rw [named] at correct
  have certificate : message.payload.packet.evidence = some ⟨candidate, ⟨payload, value⟩⟩ := by
    cases found : message.payload.packet.evidence with
    | none =>
        simp only [certifiedOpening, named, found, Bool.false_eq_true] at correct
        exact correct.1.elim
    | some fact =>
        have same : decide (fact = ⟨candidate, ⟨payload, value⟩⟩) = true := by
          simpa only [certifiedOpening, named, found] using correct.1
        exact congrArg some (of_decide_eq_true same)
  have inert (execution : app.Execution) :
      (execution.respond app owner ⟨some material⟩).application = execution.application := by
    rcases material with ⟨⟨packet, preparation⟩, evidence⟩
    change packet = .opening event candidate ⟨payload, value⟩ at call
    subst packet
    rfl
  have envelope := PhaseCount.localEnvelope_eq_of_recall runtime leaks original left.1
    left.2.1 owner material
  have emittedCertificate :
      (material.emit original.application.current.native owner
        ((repaired.network.known owner).map PhaseCount.nativeMessage)).evidence =
          some ⟨candidate, ⟨payload, value⟩⟩ := by
    have same := congrArg (fun packet : Message Player (CommitAttemptPacket graph) =>
      packet.payload.packet.evidence) envelope
    change message.payload.packet.evidence =
      ((original.respond app owner ⟨some material⟩).application.emit owner
        (original.network.known owner) material).packet.evidence at same
    rw [inert, phase_emit_evidence, network] at same
    exact same.symm.trans certificate
  have nativePacket : material.emit original.application.current.native owner
        ((original.network.known owner).map PhaseCount.nativeMessage) =
      material.emit repaired.application.current.native owner
        ((repaired.network.known owner).map PhaseCount.nativeMessage) := by
    rw [network]
    exact (emit_eq_of_successful_certificate material _ _ owner _
      (congrArg PhasePublicView.native publicBefore).symm ⟨candidate, ⟨payload, value⟩⟩
        repairedFixed originalFixed emittedCertificate).symm
  have packets : app.packet (app.submit original.application owner material) owner
        (original.network.known owner) material =
      app.packet (app.submit repaired.application owner material) owner
        (repaired.network.known owner) material := by
    change (original.respond app owner ⟨some material⟩).application.emit owner
      (original.network.known owner) material =
        (repaired.respond app owner ⟨some material⟩).application.emit owner
          (repaired.network.known owner) material
    rw [inert, inert, emit_mask, emit_mask, nativePacket, publicBefore]
    have attempts : original.application.attempt = repaired.application.attempt :=
      congrArg PhasePublicView.attempt publicBefore
    rw [attempts]
  have envelopes : PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
        (original.observe app owner) material =
      PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
        (repaired.observe app owner) material := by
    rw [PhaseCount.localEnvelope_eq_of_recall runtime leaks original left.1 left.2.1,
      PhaseCount.localEnvelope_eq_of_recall runtime leaks repaired right.1 right.2.1, packets]
    exact congrArg (fun serial => (⟨(owner, serial), app.packet
      (app.submit repaired.application owner material) owner
        (repaired.network.known owner) material⟩ : Message Player (CommitAttemptPacket graph)))
      (congrArg (fun pool : MessageNetwork Player (CommitAttemptPacket graph) =>
        pool.nextSerial owner) network)
  exact (inert_response_menu_iff network bounds left right material envelopes).mp member

namespace Frame

variable {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

/-- When the original current binding is already successful, every admitted
opening alias on either side emits the same certificate. Thus the entire
counted raw menu agrees, not just its unfiltered submission syntax. -/
theorem opening_menu_eq (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, original⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, repaired⟩))
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (leftRequest : original.application.SeedRequest owner ⟨original.application.attempt, event⟩)
    (rightRequest : repaired.application.SeedRequest owner ⟨repaired.application.attempt, event⟩)
    (value : L.Val payload)
    (successful : binding.get? original.application.current.native.config.store =
      some (.success value)) :
    PhaseCount.onePacketActions runtime leaks bounds owner (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner) =
      PhaseCount.onePacketActions runtime leaks bounds owner (repaired.recall owner)
        (repaired.observe (phaseApplication runtime leaks) owner) := by
  classical
  let app := phaseApplication runtime leaks
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  have rawLeft := menu.toRawTrace initial horizon scheduler leftTrace
  have rawRight := menu.toRawTrace initial horizon scheduler rightTrace
  have left := PhaseCount.countRecall_history runtime leaks rawLeft
  have right := PhaseCount.countRecall_history runtime leaks rawRight
  have leftBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawLeft
  have rightBinding := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler
      rawRight
  obtain ⟨imageStored, candidate, leftAccepted, rightAccepted, _owned, leftFixed, rightFixed⟩ :=
    frame.live.successful_opening leftBinding.active rightBinding.active binding value successful
  apply Finset.ext
  intro response
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      exact iff_of_true (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
        (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
  | some material =>
    constructor
    · intro member
      obtain ⟨other, otherValue, call, _stored, _accepted, _fixed⟩ :=
        PhaseCount.onePacket_opening_shape runtime leaks bounds plan ordered inputs horizon
          scheduler remaining owner original leftTrace event payload binding checks outputEq
            codeEq node leftRequest material member
      rcases material with ⟨⟨packet, preparation⟩, evidence⟩
      change packet = .opening event other ⟨payload, otherValue⟩ at call
      subst packet
      exact (frame.opening_response bounds plan inputs horizon scheduler remaining leftTrace
        rightTrace event other ⟨payload, otherValue⟩ preparation evidence member leftRequest
          payload binding checks outputEq codeEq node).1
    · intro member
      obtain ⟨other, otherValue, call, stored, accepted, _fixed⟩ :=
        PhaseCount.onePacket_opening_shape runtime leaks bounds plan ordered inputs horizon
          scheduler remaining owner repaired rightTrace event payload binding checks outputEq
            codeEq node rightRequest material member
      have handles : other = candidate := Option.some.inj (accepted.symm.trans rightAccepted)
      have values : otherValue = value :=
        PublicationResult.success.inj (Option.some.inj (stored.symm.trans imageStored))
      subst other
      subst otherValue
      have permitted : PhaseCount.permits ((app).outputs (repaired.recall owner))
          (PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
            (repaired.observe app owner) material) = true := by
        rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
          with impossible | ⟨other, transmitted, allowed⟩
        · cases impossible
        · cases Option.some.inj transmitted
          exact allowed
      let message := PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
        (repaired.observe app owner) material
      have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
      have named : message.payload.packet.call = .opening event candidate ⟨payload, value⟩ :=
        (PhaseCount.maskPacket_call _ _).trans call
      unfold CountCallCorrect at correct
      dsimp only [PhaseCount.nativeMessage] at correct
      rw [named] at correct
      have certificate : message.payload.packet.evidence = some ⟨candidate, ⟨payload, value⟩⟩ := by
        have certified : certifiedOpening message.payload.packet = true := correct.1
        cases found : message.payload.packet.evidence with
        | none =>
            have impossible : (false : Bool) = true := by
              simpa only [certifiedOpening, named, found] using certified
            cases impossible
        | some fact =>
            have equality : decide (fact = ⟨candidate, ⟨payload, value⟩⟩) = true := by
              simpa only [certifiedOpening, named, found] using certified
            exact congrArg some (of_decide_eq_true equality)
      have leftInert : (original.respond app owner ⟨some material⟩).application =
          original.application := by
        rcases material with ⟨⟨packet, preparation⟩, evidence⟩
        change packet = .opening event candidate ⟨payload, value⟩ at call
        subst packet
        rfl
      have rightInert : (repaired.respond app owner ⟨some material⟩).application =
          repaired.application := by
        rcases material with ⟨⟨packet, preparation⟩, evidence⟩
        change packet = .opening event candidate ⟨payload, value⟩ at call
        subst packet
        rfl
      have envelope := PhaseCount.localEnvelope_eq_of_recall runtime leaks repaired right.1
        right.2.1 owner material
      have emittedCertificate :
          (material.emit repaired.application.current.native owner
            ((repaired.network.known owner).map PhaseCount.nativeMessage)).evidence =
              some ⟨candidate, ⟨payload, value⟩⟩ := by
        have same := congrArg (fun packet : Message Player (CommitAttemptPacket graph) =>
          packet.payload.packet.evidence) envelope
        change message.payload.packet.evidence =
          ((repaired.respond app owner ⟨some material⟩).application.emit owner
            (repaired.network.known owner) material).packet.evidence at same
        rw [rightInert, phase_emit_evidence] at same
        exact same.symm.trans certificate
      have nativePacket : material.emit original.application.current.native owner
          ((original.network.known owner).map PhaseCount.nativeMessage) =
        material.emit repaired.application.current.native owner
          ((repaired.network.known owner).map PhaseCount.nativeMessage) := by
        rw [frame.network]
        exact emit_eq_of_successful_certificate material _ _ owner _ frame.live.publicView
          ⟨candidate, ⟨payload, value⟩⟩ leftFixed rightFixed emittedCertificate
      have packets : app.packet (app.submit original.application owner material) owner
          (original.network.known owner) material =
        app.packet (app.submit repaired.application owner material) owner
          (repaired.network.known owner) material := by
        change (original.respond app owner ⟨some material⟩).application.emit owner
          (original.network.known owner) material =
            (repaired.respond app owner ⟨some material⟩).application.emit owner
              (repaired.network.known owner) material
        rw [leftInert, rightInert, emit_mask, emit_mask, nativePacket, frame.publicView]
        have attempts : original.application.attempt = repaired.application.attempt :=
          congrArg PhasePublicView.attempt frame.publicView
        rw [attempts]
      have envelopes : PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
          (original.observe app owner) material =
        PhaseCount.localEnvelope runtime leaks owner (repaired.recall owner)
          (repaired.observe app owner) material := by
        rw [PhaseCount.localEnvelope_eq_of_recall runtime leaks original left.1 left.2.1,
          PhaseCount.localEnvelope_eq_of_recall runtime leaks repaired right.1 right.2.1, packets]
        exact congrArg (fun serial => (⟨(owner, serial),
          app.packet (app.submit repaired.application owner material) owner
            (repaired.network.known owner) material⟩ : Message Player (CommitAttemptPacket graph)))
          (congrArg (fun pool : MessageNetwork Player (CommitAttemptPacket graph) =>
            pool.nextSerial owner) frame.network)
      exact (inert_response_menu_iff frame.network bounds left right material envelopes).mpr member

end Frame
end Vegas.EventGraphRuntime.PhaseBindingRepair

namespace Vegas.EventGraphRuntime.HiddenSwap

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

/-- A genuine guarded opening has the same entire counted raw menu under a
hidden swap, including every silent and evidence-alias atom. Original private
inputs may change; no binding-repair frame or equal initial draw is required. -/
theorem opening_menu_law_eq_of_history (swap : HiddenSwap graph)
    (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat)
    (owner : Player) (original : (phaseApplication runtime leaks).Execution)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, original⟩))
    (swappedTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, swap.phaseExecution original⟩))
    (event : graph.EventId) (payload : L.Ty)
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (node : nodeView graph event = .resolve owner payload binding checks outputEq codeEq)
    (request : original.application.SeedRequest owner ⟨original.application.attempt, event⟩)
    (fixed : RevealFixed swap original.application.current.native event) :
    PhaseCount.onePacketActions runtime leaks bounds owner (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner) =
      PhaseCount.onePacketActions runtime leaks bounds owner
        ((swap.phaseExecution original).recall owner)
        ((swap.phaseExecution original).observe (phaseApplication runtime leaks) owner) ∧
    (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler owner
          (some (original.recall owner,
            original.observe (phaseApplication runtime leaks) owner))).map
      Subtype.val) =
    (((PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy
        (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler owner
          (some ((swap.phaseExecution original).recall owner,
            (swap.phaseExecution original).observe (phaseApplication runtime leaks) owner))).map
      Subtype.val) := by
  have handles : ∀ candidate,
      original.application.current.native.accepted binding.field = some candidate →
        swap.raw candidate = id := (show _ ∧ (∀ candidate,
          original.application.current.native.accepted binding.field = some candidate →
            swap.raw candidate = id) from by simpa only [RevealFixed, node] using fixed).2
  have candidates (candidate) (accepted :
      original.application.current.native.accepted binding.field = some candidate) :
      original.application.current.native.candidates.lookup candidate =
        (swap.phaseExecution original).application.current.native.candidates.lookup candidate := by
    change _ = swapCandidate (swap.raw candidate) _
    rw [handles candidate accepted]
    have identity : swapCandidate (id : Raw L → Raw L) = id := by
      funext state
      cases state <;> rfl
    rw [identity]
    rfl
  have publicBefore : original.application.publicView =
      (swap.phaseExecution original).application.publicView :=
    (PhaseRuntimeState.swap_publicView swap original.application).symm
  have swappedRequest : (swap.phaseExecution original).application.SeedRequest owner
      ⟨(swap.phaseExecution original).application.attempt, event⟩ := request
  have left := PhaseCount.countRecall_history runtime leaks
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ trace)
  have right := PhaseCount.countRecall_history runtime leaks
    ((PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace _ _ _ swappedTrace)
  have menus : PhaseCount.onePacketActions runtime leaks bounds owner (original.recall owner)
        (original.observe (phaseApplication runtime leaks) owner) =
      PhaseCount.onePacketActions runtime leaks bounds owner
        ((swap.phaseExecution original).recall owner)
        ((swap.phaseExecution original).observe (phaseApplication runtime leaks) owner) := by
    apply Finset.ext
    intro response
    rcases response with ⟨transmission⟩
    cases transmission with
    | none =>
        exact iff_of_true (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
          (PhaseCount.silence_onePacket runtime leaks bounds owner _ _)
    | some material =>
        constructor
        · exact PhaseBindingRepair.opening_response_replay bounds plan ordered inputs horizon
            scheduler remaining owner original _ trace right rfl publicBefore event payload binding
              checks outputEq codeEq node request candidates material
        · exact PhaseBindingRepair.opening_response_replay bounds plan ordered inputs horizon
            scheduler remaining owner _ original swappedTrace left rfl publicBefore.symm event
              payload binding checks outputEq codeEq node swappedRequest
                (fun candidate accepted => (candidates candidate accepted).symm) material
  exact ⟨menus, (PhaseCount.onePacketMenu runtime leaks bounds).uniformPolicy_map_eq_of_actions
    (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler owner _ _ _ _ menus⟩

end Vegas.EventGraphRuntime.HiddenSwap
