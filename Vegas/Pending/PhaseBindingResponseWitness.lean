/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseBindingHistoryRepair

/-! # Observable unsent and canonical sending witnesses for repaired callbacks -/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseCount

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

/-- A genuinely available nonsilent response excludes a previous own packet
for its current request, as an exact property of the complete signed word. -/
theorem unsent_of_nonsilent (bounds : MessageBounds graph) (plan : RuntimePhasePlan graph)
    (ordered : graph.RevealRelaxedOrdered) (inputs : PMF graph.Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler) (remaining : Nat) (owner : Player)
    (physical : (phaseApplication runtime leaks).Execution)
    (trace : ((onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, physical⟩))
    (coordinate : CommitAttemptEvent graph) (request : physical.application.SeedRequest owner
      coordinate) (material : WitnessedSubmission graph)
    (member : (⟨some material⟩ : (phaseApplication runtime leaks).Action) ∈
      onePacketActions runtime leaks bounds owner (physical.recall owner)
        (physical.observe (phaseApplication runtime leaks) owner)) :
    ∀ message ∈ (phaseApplication runtime leaks).outputs (physical.recall owner),
      event? message.payload ≠ some coordinate := by
  let app := phaseApplication runtime leaks
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have recalled := (app).history_inputRecall initial horizon scheduler
    ((onePacketMenu runtime leaks bounds).toRawTrace initial horizon scheduler trace)
  intro message output same
  have own : message.sender = owner := by
    rw [← recalled owner] at output
    simpa only [decide_eq_true_eq] using (List.mem_filter.mp output).2
  have fields : message.payload.attempt = coordinate.attempt ∧
      message.payload.packet.call.event? graph = some coordinate.event := by
    unfold event? at same
    obtain ⟨event, named, paired⟩ := Option.map_eq_some_iff.mp same
    cases paired
    exact ⟨rfl, named⟩
  have sent : PhaseSeedScheduler.ownPacket coordinate owner message = true := by
    simp only [PhaseSeedScheduler.ownPacket, decide_eq_true_eq]
    exact ⟨own, fields⟩
  have singleton := onePacketActions_eq_singleton_of_sent runtime leaks bounds plan ordered
    inputs horizon scheduler remaining owner physical trace coordinate request
      ⟨message, output, sent⟩
  rw [singleton] at member
  have impossible := congrArg ReactiveApplication.Action.transmission
    (Finset.mem_singleton.mp member)
  cases impossible

end Vegas.EventGraphRuntime.PhaseCount

namespace Vegas.EventGraphRuntime.PhaseBindingRepair.Frame

open Interaction EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}
  {memory : BindingMemory runtime (nativeLeaks (graph := graph))} {owner : Player}
  {original repaired : (phaseApplication runtime leaks).Execution}

omit [Fintype Player] in
/-- The explicit repaired sending action is a successful typed binding at
the original prepared slot, even for absent or wrongly typed preparation. -/
theorem responseImage_binding (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .bind owner payload)
    (node : nodeView graph event = .bind owner payload outputEq codeEq)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph) :
    ∃ value : L.Val payload, responseImage (runtime := runtime) (leaks := leaks) owner owner
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ =
        phaseBindingResponse runtime leaks owner event payload (.success value) serial := by
  cases opening with
  | none =>
      refine ⟨L.someValue payload, ?_⟩
      simp only [responseImage, ↓reduceIte, node, Option.bind_none, phaseBindingResponse]
  | some raw =>
      rcases raw with ⟨kind, value⟩
      by_cases same : kind = payload
      · subst kind
        refine ⟨value, ?_⟩
        simp only [responseImage, ↓reduceIte, node, Option.bind_some, Raw.as?_mk,
          phaseBindingResponse]
      · refine ⟨L.someValue payload, ?_⟩
        simp only [responseImage, ↓reduceIte, node, Option.bind_some, Raw.as?, same, ↓reduceDIte,
          phaseBindingResponse]

/-- The original arbitrary evidence alias supplies an actual canonical raw
binding at the image input, with the same preparation and prepared serial.
This does not assume that the original evidence alias remains image-legal. -/
theorem canonical_binding_member (frame : Frame runtime leaks memory owner original repaired)
    (bounds : MessageBounds graph) (left : PhaseCount.CountRecall runtime leaks original)
    (right : PhaseCount.CountRecall runtime leaks repaired) (event : graph.EventId) (serial : Nat)
    (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (fresh : original.application.current.native.candidates.lookup (owner, .prepared serial) =
      .fresh)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (original.recall owner) (original.observe (phaseApplication runtime leaks) owner)) :
    (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, .none⟩⟩ :
      (phaseApplication runtime leaks).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds
        owner (repaired.recall owner)
          (repaired.observe (phaseApplication runtime leaks) owner) := by
  let app := phaseApplication runtime leaks
  let call : Submission graph := ⟨.commitment event (owner, .prepared serial), opening⟩
  let material : WitnessedSubmission graph := ⟨call, evidence⟩
  let source : app.Action := ⟨some material⟩
  let canonical : app.Action := ⟨some ⟨call, .none⟩⟩
  have permitted : PhaseCount.permits (app.outputs (original.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (original.recall owner)
        (original.observe app owner) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp member).2
      with impossible | ⟨supplied, same, allowed⟩
    · cases impossible
    · cases Option.some.inj same
      exact allowed
  have normalized : (PhaseCount.normalization runtime leaks).action owner (original.recall owner)
      (original.observe app owner) source = canonical := by
    have absent := PhaseCount.normalize_binding_evidence_none runtime leaks owner
      (original.recall owner) (original.observe app owner) material event
        (owner, .prepared serial) rfl permitted
    have effective : openingEffective owner (original.observe app owner).application.1
        (.commitment event (owner, .prepared serial)) := ⟨rfl, fresh⟩
    have calls : ((PhaseCount.normalization runtime leaks).normalize owner
        (original.observe app owner).application
        (ReactiveApplication.ResponseMenu.knownPackets (original.recall owner)
          (original.observe app owner)) material).call = call :=
      Submission.normalizeReactive_effective _ _ _ effective
    exact congrArg (fun material => (⟨some material⟩ : app.Action))
      (congrArg₂ WitnessedSubmission.mk calls absent)
  have canonicalMember := PhaseCount.normalize_mem_onePacketActions runtime leaks bounds owner
    (original.recall owner) (original.observe app owner) source member
  rw [normalized] at canonicalMember
  have raw := ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp
    canonicalMember).1
  rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at raw
  have bounded := ((bounds.submissions_mem _ _).mp raw).1.2
  exact frame.binding_menu bounds left right event serial opening opening bounded canonicalMember

end Vegas.EventGraphRuntime.PhaseBindingRepair.Frame
