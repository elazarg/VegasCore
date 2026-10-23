/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalShadowMenu
import Vegas.Pending.PhaseProposalPreparedBinding
import Vegas.Pending.PhaseBindingFreshness
import Vegas.Pending.PhaseBindingInvariant

/-! # Genuine counted fresh binding responses extend the repair -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- The two actual counted prefixes supply global slot freshness, including
all retired attempts. Repair changes only unusable private preparation;
the actual opaque packet and every other player's complete prefix agree. -/
theorem binding_response_repair (memory : BindingShadow graph) (owner : Player)
    (owned : memory.OwnBindings owner)
    (valid : ∀ slot, memory.candidates slot ≠ some .fresh)
    (left right : (app).Execution)
    (frame : PhaseStateFrame memory owner left.application right.application)
    (supported : memory.CompletedAt right.application.current.native.config)
    (network : left.network = right.network) (receipts : left.receipts = right.receipts)
    (service : left.environmentRecall = right.environmentRecall)
    (recalled : ∀ who, who ≠ owner → left.recall who = right.recall who)
    (prepared : PreparedBindings runtime leaks owner left right)
    (bounds : MessageBounds graph) (covered : bounds.CoversOutputValues)
    (plan : RuntimePhasePlan graph) (inputs : PMF graph.Inputs)
    (horizon : Nat) (scheduler : (app).Scheduler) (remaining : Nat)
    (leftTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, left⟩))
    (rightTrace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace
        (some ⟨remaining, some owner, right⟩))
    (event : graph.EventId) (payload : L.Ty)
    (outputEq : graph.outputLayout event = .binding owner payload)
    (serial : Nat) (opening : Option (Raw L)) (evidence : EvidenceRequest graph)
    (member : (⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩ :
      (app).Action) ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (left.recall owner) (left.observe app owner)) :
    let replacement := match opening.bind (fun raw => raw.as? payload) with
      | none => some (⟨payload, L.someValue payload⟩ : Raw L)
      | some _ => opening
    let source : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), opening⟩, evidence⟩⟩
    let target : (app).Action :=
      ⟨some ⟨⟨.commitment event (owner, .prepared serial), replacement⟩, .none⟩⟩
    let first := left.respond app owner source
    let second := right.respond app owner target
    let remembered := memory.rememberCandidate (.prepared serial)
      (first.application.current.native.candidates.lookup (owner, .prepared serial))
    target ∈ PhaseCount.onePacketActions runtime leaks bounds owner
        (right.recall owner) (right.observe app owner) ∧
      remembered.OwnBindings owner ∧
      (∀ slot, remembered.candidates slot ≠ some .fresh) ∧
      PhaseStateFrame remembered owner first.application second.application ∧
      remembered.CompletedAt second.application.current.native.config ∧
      first.network = second.network ∧
      phaseExternalObservation runtime leaks owner first =
        phaseExternalObservation runtime leaks owner second ∧
      PreparedBindings runtime leaks owner first second := by
  classical
  intro replacement source target first second remembered
  let initial := inputs.map (PhaseRuntimeState.initial plan)
  have rawLeft := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler leftTrace
  have rawRight := (PhaseCount.onePacketMenu runtime leaks bounds).toRawTrace
    initial horizon scheduler rightTrace
  have countLeft := PhaseCount.countRecall_history runtime leaks rawLeft
  have countRight := PhaseCount.countRecall_history runtime leaks rawRight
  have fresh := PhaseCount.onePacket_binding_fresh runtime leaks bounds plan inputs horizon
    scheduler leftTrace owner event serial opening evidence member
  have freshReconstructed : (memory.native owner right.application.current.native).candidates.lookup
      (owner, .prepared serial) = .fresh := by
    have nativeEq : left.application.current.native =
        memory.native owner right.application.current.native := by rw [frame.current]; rfl
    rwa [nativeEq] at fresh
  have rightFresh : right.application.current.native.candidates.lookup
      (owner, .prepared serial) = .fresh := by
    simp only [BindingShadow.native, CommitmentCandidates.lookup, ite_true] at freshReconstructed
    exact (memory.candidate_fresh_iff valid _ _).mp freshReconstructed
  have record := phaseBindingRecord_history runtime leaks plan inputs horizon scheduler rawRight
  have savedFresh : right.application.entry.native.candidates.lookup
      (owner, .prepared serial) = .fresh := by
    by_contra fixed
    have remains := record.fixed (owner, .prepared serial) fixed
    exact fixed (remains.symm.trans rightFresh)
  have originalBound : bounds.AllowsOpening opening := by
    have rawMember := ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp
      member).1
    rw [PhaseCount.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem] at rawMember
    exact ((bounds.submissions_mem _ _).mp rawMember).1.2
  have replacementBound : bounds.AllowsOpening replacement := by
    cases decoded : opening.bind (fun raw => raw.as? payload) with
    | none =>
        have values := covered event
        rw [outputEq] at values
        simpa only [replacement, decoded, MessageBounds.AllowsOpening] using
          values (L.someValue payload)
    | some value => simpa only [replacement, decoded] using originalBound
  have legal := binding_response_member runtime leaks memory owner owned left right frame network
    countLeft countRight bounds event serial opening replacement evidence replacementBound member
  obtain ⟨nextOwned, nextFrame, nextSupport, nextNetwork, external⟩ :=
    respond_binding_raw_external runtime leaks memory owner owned left right frame supported
      network receipts service recalled countLeft.1 bounds event serial opening replacement evidence
        fresh rightFresh savedFresh member
  have fixed : first.application.current.native.candidates.lookup
      (owner, .prepared serial) ≠ .fresh := by
    change (submitStep _ owner (.commitment event (owner, .prepared serial))).candidates.lookup
      (owner, .prepared serial) ≠ .fresh
    simp only [submitStep, ite_true]
    exact CommitmentCandidates.lookup_freeze_ne_fresh _ _
  have nextValid := memory.rememberCandidate_candidates_not_fresh valid (.prepared serial)
    (first.application.current.native.candidates.lookup (owner, .prepared serial)) fixed
  exact ⟨legal, nextOwned, nextValid, nextFrame, nextSupport, nextNetwork, external,
    PreparedBindings.binding_response runtime leaks prepared event payload outputEq serial opening
      evidence fresh rightFresh⟩

end Vegas.EventGraphRuntime.BindingShadow
