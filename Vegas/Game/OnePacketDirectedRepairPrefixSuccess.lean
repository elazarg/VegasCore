/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.OnePacketDecodedCells
import Vegas.Game.OnePacketDirectedRepairPrefix
import Vegas.EventGraph.BarrierBlocks

/-! # Successful reveal bindings along a forced information history -/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime
open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup leaks).Scheduler}
  [DecidableEq (CellTy Player L)]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L]
    [DecidableEq (CellTy Player L)] in
private theorem exists_context_reference : ∀ (Γ : SourceCtx Player L) (input : Fin Γ.length),
    ∃ (name : VarId) (kind : CellTy Player L) (source : HasVar Γ name kind),
      inputId source = input
  | [], input => Fin.elim0 input
  | (name, kind) :: Γ, input => by
      cases input using Fin.cases with
      | zero => exact ⟨name, kind, .here, rfl⟩
      | succ input =>
          obtain ⟨other, otherKind, source, rfl⟩ := exists_context_reference Γ input
          exact ⟨other, otherKind, .there source, rfl⟩

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L]
    [DecidableEq (CellTy Player L)] in
private theorem available_of_binding_read {Field : Type}
    {layout : Field → EventGraph.EventField Player L} {kind : EventGraph.EventField Player L}
    (ref : EventGraph.FieldRef layout kind) (store : EventGraph.Store layout)
    (value : kind.Value) (read : ref.get? store = some value) : (store ref.field).isSome := by
  cases ref with
  | mk field layoutEq =>
      cases layoutEq
      change (store field).isSome
      change store field = some value at read
      rw [read]
      rfl

omit [Fintype Player] in
private theorem decode_binding_output {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (point : ProtocolState program),
      (Γ.map Prod.fst).Nodup →
      decodeSourcePrefix? program refs registry revelations outputs count store history =
        some point →
      ∀ (event : Fin (eventCount program)), event.val < count →
      ∀ {owner payload} (outputEq : outputLayout program event = .binding owner payload)
        (value : PublicationResult (L.Val payload)),
        (⟨(outputs event).field, (outputs event).layout_eq.trans outputEq⟩ :
          EventGraph.FieldRef layout (.binding owner payload)).get? store = some value →
        ProtocolState.cell? program point (eventCell program event).1
          (.commitment owner payload) = some value
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, event, earlier, _, _, _, _, _ => by omega
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history,
      point, unique, decoded, event, earlier, owner, payload, outputEq, value, read => by
      cases program with
      | ret _ => exact Fin.elim0 event
      | sample _ fresh _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero => cases outputEq
          | succ event =>
              exact decode_binding_output count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded event
                (by simpa using earlier) outputEq value read
      | commit _ _ fresh _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero =>
              cases outputEq
              exact decodeSourcePrefix?_context_cell count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded .here value read
          | succ event =>
              exact decode_binding_output count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded event
                (by simpa using earlier) outputEq value read
      | reveal _ _ _ fresh _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero => cases outputEq
          | succ event =>
              exact decode_binding_output count next _ _ _ _ store history rest
                (List.nodup_cons.mpr ⟨fresh, unique⟩) restDecoded event
                (by simpa using earlier) outputEq value read

omit [Fintype Player] in
/-- A stored binding is the corresponding commitment cell at the decoded point. -/
theorem decodedPoint_binding_cell {config : (graph setup).Config}
    {point : ProtocolState setup.program}
    (decoded : decodedPoint setup config = some point)
    {owner : Player} {payload : L.Ty}
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (value : PublicationResult (L.Val payload))
    (stored : binding.get? config.store = some value) :
    ProtocolState.cell? setup.program point (fieldCell setup binding.field).1
      (.commitment owner payload) = some value := by
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    cases binding with
    | mk field layoutEq =>
      cases field with
      | inl input =>
          obtain ⟨name, kind, source, rfl⟩ := exists_context_reference setup.context input
          have kindEq := cellField_eq_binding
            ((inputLayout_inputId source).symm.trans layoutEq)
          subst kind
          have refEq : (ContextRefs.initial setup.context (outputLayout setup.program)).get
              source = (⟨.inl (inputId source), layoutEq⟩ : EventGraph.FieldRef
                (graph setup).layout (.binding owner payload)) := rfl
          have found := decodeSourcePrefix?_context_cell ordered.choose setup.program _ _ _ _
            config.store _ point setup.namesNodup decoded source value (refEq ▸ stored)
          simpa only [fieldCell, inputId_get] using found
      | inr event =>
          have present : (config.outputs event).isSome := by
            exact available_of_binding_read (⟨.inr event, layoutEq⟩ : EventGraph.FieldRef
              (graph setup).layout (.binding owner payload)) config.store value stored
          have completed := (config.output_available event).mp present
          have earlier : event.val < ordered.choose :=
            (ordered.choose_spec.2 event).mp completed
          exact decode_binding_output ordered.choose setup.program _ _ _ _ config.store _
            point setup.namesNodup decoded event earlier layoutEq value stored
  · cases decoded

section Witness

variable {p q : ProtocolState setup.program}
  (wellFormed : setup.WellFormed)
  {second : setup.intendedProtocol.History} (secondState : second.state = some q)
  (who : Player)
  (sameView : ProtocolState.observe who setup.program p =
    ProtocolState.observe who setup.program q)
  {final : (application setup leaks).Control}
  (trace : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some final))
  (decodedP : decodedPoint setup final.execution.application.config = some p)
  (staticQ : ProtocolState.StaticAt setup.program [] (Revelations.initial setup.context) q)
  (readyOwn : ∀ event, final.execution.application.config.cut.Ready event →
    ∀ owner payload binding checks outputEq codeEq,
      nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq →
        owner = who)
  {before : (application setup leaks).Control}
  (prior : (onePacketProtocol setup leaks bounds horizon scheduler).Trace (some before))
  (isPrefix : TracePrefix prior trace)

include wellFormed secondState who sameView trace decodedP staticQ readyOwn prior isPrefix

omit [DecidableEq (CellTy Player L)] in
/-- Every ready reveal along this history already reads a successful binding. -/
theorem binding_success_of_tracePrefix {event : (graph setup).EventId}
    (ready : before.execution.application.config.cut.Ready event)
    {owner : Player} {payload : L.Ty}
    (binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck (graph setup).layout payload))
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks)
    (view : nodeView (graph setup) event = .resolve owner payload binding checks outputEq codeEq) :
    ∃ value, binding.get? before.execution.application.config.store = some (.success value) := by
  classical
  have readsEq : ((graph setup).nodes event).readFields =
      insert binding.field (EventGraph.GuardCheck.listReadFields checks) := by
    calc
      _ = (cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
          ((graph setup).nodes event)).readFields :=
        (EventGraph.EventCode.readFields_cast outputEq ((graph setup).nodes event)).symm
      _ = _ := by rw [codeEq]; rfl
  have available := before.execution.application.config.read_available ready
    (show binding.field ∈ ((graph setup).nodes event).readFields by
      rw [readsEq]; exact Finset.mem_insert_self ..)
  obtain ⟨result, read⟩ := Option.isSome_iff_exists.mp
    (binding.get?_isSome before.execution.application.config.store available)
  have finalRead := binding.get?_preserved before.execution.application.config.store
    final.execution.application.config.store
    (fun field value stored => storedValue_of_tracePrefix prior isPrefix field value stored)
    result read
  have found := decodedPoint_binding_cell decodedP binding result finalRead
  obtain ⟨after, finalEq, active⟩ := readyOrCompleted_of_tracePrefix prior isPrefix
    (Or.inl ready)
  cases Option.some.inj finalEq
  have agree := bindingCellsAgree_of_decoded wellFormed secondState who sameView trace decodedP
    staticQ readyOwn active view
  obtain ⟨value, resultEq⟩ := ProtocolState.cell?_commitment_success
    (intended_of_history wellFormed second.trace q secondState) (agree.symm.trans found)
  exact ⟨value, read.trans (congrArg some resultEq)⟩

end Witness

end Vegas
