/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventGraphResolutionFields
import Vegas.Game.SourceSwapAgreement
import Vegas.Game.OnePacketIntendedProjection

/-! # Decoded points record the completed reveals

**The commitment a resolve event reads.** A reveal event of a source program
reveals one commitment cell (`Vegas.revealedCell`), whose name is the event's
resolution name (`Vegas.revealedCell_map_fst`). The lowerer compiles a reveal to
a resolve node reading the field of that commitment cell, so at a resolve event
of the default graph the binding field read is the field of the revealed
commitment cell (`Vegas.fieldCell_resolveBinding`).

**Decoded points record completed reveals.** Decoding a source prefix past a
reveal records the revealed commitment as revealed into the reveal's
publication cell, and later steps keep the record: a later reveal reveals a
different commitment, since each commitment is revealed at most once
(`Vegas.decodeSourcePrefix?_revealedInto`). The decoded point of a native
configuration is the decoding at the length of its completed prefix, so at the
decoded point every completed resolve event has revealed its commitment into
its publication cell (`Vegas.decodedPoint_revealedInto`).
-/

noncomputable section

namespace Vegas

open SourceProgram EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The commitment cell a reveal event reveals, and nothing at other events. -/
def revealedCell : {Γ : SourceCtx Player L} → {openNames : Finset VarId} →
    (program : SourceProgram Player L Γ openNames) → Fin (eventCount program) →
      Option (VarId × CellTy Player L)
  | _, _, .ret _, event => Fin.elim0 event
  | _, _, .sample _ _ _ next, event => Fin.cases none (revealedCell next) event
  | _, _, .commit _ _ _ _ next, event => Fin.cases none (revealedCell next) event
  | _, _, .reveal (payload := payload) _ owner name _ _ _ next, event =>
      Fin.cases (some (name, .commitment owner payload)) (revealedCell next) event

/-- The name of the revealed commitment cell is the resolution name. -/
theorem revealedCell_map_fst : ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (event : Fin (eventCount program)),
    (revealedCell program event).map Prod.fst = resolutionName? program event
  | _, _, .ret _, event => Fin.elim0 event
  | _, _, .sample _ _ _ next, event => by
      cases event using Fin.cases with
      | zero => rfl
      | succ event => exact revealedCell_map_fst next event
  | _, _, .commit _ _ _ _ next, event => by
      cases event using Fin.cases with
      | zero => rfl
      | succ event => exact revealedCell_map_fst next event
  | _, _, .reveal _ _ _ _ _ _ next, event => by
      cases event using Fin.cases with
      | zero => rfl
      | succ event => exact revealedCell_map_fst next event

/-- The lowered resolve nodes read the fields of the commitment cells their
reveals reveal, for any naming of fields by cells that the references and the
output embedding respect. -/
theorem compileRankedNodes_revealedCell {inputCount totalCount : Nat}
    {inputs : Fin inputCount → Vegas.EventGraph.EventField Player L}
    {outputs : Fin totalCount → Vegas.EventGraph.EventField Player L}
    (cellOf : Fin inputCount ⊕ Fin totalCount → VarId × CellTy Player L) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames)
      (refs : ContextRefs (Vegas.EventGraph.fieldLayout inputs outputs) Γ)
      (revelations : Revelations Γ) (registry : Registry Γ)
      (embedding : OutputEmbedding inputs outputs program)
      (refsBefore : ContextRefsBefore refs embedding),
      (∀ {name cell} (source : HasVar Γ name cell), cellOf (refs.get source).field = (name, cell)) →
      (∀ index, cellOf (.inr (embedding.event index)) = eventCell program index) →
      ∀ index, ((compileRankedNodes program refs revelations registry embedding refsBefore
        index).code.resolutionField?).map cellOf = revealedCell program index := by
  intro Γ openNames program
  induction program with
  | ret => intro _ _ _ _ _ _ _ index; exact Fin.elim0 index
  | sample name fresh law next ih =>
      intro refs revelations registry embedding before named outputsNamed index
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          apply ih
          · intro readName cell source
            cases source with
            | here => exact outputsNamed ⟨0, Nat.zero_lt_succ _⟩
            | there source => exact named source
          · intro remaining
            exact outputsNamed (Fin.succ remaining)
  | commit name owner fresh guard next ih =>
      intro refs revelations registry embedding before named outputsNamed index
      cases index using Fin.cases with
      | zero => rfl
      | succ index =>
          apply ih
          · intro readName cell source
            cases source with
            | here => exact outputsNamed ⟨0, Nat.zero_lt_succ _⟩
            | there source => exact named source
          · intro remaining
            exact outputsNamed (Fin.succ remaining)
  | reveal published owner name fresh selected unresolved next ih =>
      intro refs revelations registry embedding before named outputsNamed index
      cases index using Fin.cases with
      | zero => exact congrArg some (named selected)
      | succ index =>
          apply ih
          · intro readName cell source
            cases source with
            | here => exact outputsNamed ⟨0, Nat.zero_lt_succ _⟩
            | there source => exact named source
          · intro remaining
            exact outputsNamed (Fin.succ remaining)

/-- The resolve nodes of the default graph read the fields of the commitment
cells their reveals reveal. -/
theorem nodes_revealedCell (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) :
    (((graph setup).nodes event).resolutionField?).map (fieldCell setup) =
      revealedCell setup.program event := by
  apply compileRankedNodes_revealedCell
  · intro name cell source
    exact inputId_get source
  · intro index
    rfl

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem cellField_eq_binding {kind : CellTy Player L} {owner : Player} {payload : L.Ty}
    (same : cellField kind = .binding owner payload) : kind = .commitment owner payload := by
  cases kind with
  | publicData | privateInput | publication => cases same
  | commitment => cases same; rfl

variable {setup : Setup (Player := Player) (L := L)}

/-- **The binding a resolve event reads is the commitment cell it reveals.** At
an event whose node code is a resolve node, the event is a reveal of a commitment
name, and the binding field the node reads is the field of that commitment
cell. -/
theorem fieldCell_resolveBinding {event : (graph setup).EventId} {owner : Player}
    {payload : L.Ty} {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks) :
    ∃ name, resolutionName? setup.program event = some name ∧
      revealedCell setup.program event = some (name, .commitment owner payload) ∧
      fieldCell setup binding.field = (name, .commitment owner payload) := by
  have kind := cellField_eq_binding
    ((layout_fieldCell setup binding.field).symm.trans binding.layout_eq)
  have cell : fieldCell setup binding.field =
      ((fieldCell setup binding.field).1, .commitment owner payload) := Prod.ext rfl kind
  have revealed : revealedCell setup.program event = some (fieldCell setup binding.field) := by
    rw [← nodes_revealedCell setup event,
      ← EventGraph.EventCode.resolutionField?_cast outputEq, codeEq]
    rfl
  rw [cell] at revealed
  refine ⟨_, ?_, revealed, cell⟩
  rw [← revealedCell_map_fst, revealed]
  rfl

/-- The current configuration of an entry point is its entry configuration. -/
private theorem currentConfig_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ProtocolState.currentConfig program (ProtocolState.entry program config) = ⟨Γ, config⟩ := by
  cases program <;> rfl

/-- A revealed commitment that can no longer be revealed stays revealed into
the same publication cell through every later decoded step. -/
private theorem decodeSourcePrefix?_revealedInto_of_revealed {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {owner : Player} {payload : L.Ty}
    {name published : VarId} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history =
      some state →
    name ∉ O → ∀ (source : HasVar Γ name (.commitment owner payload))
      (cell : HasVar Γ published (.publication payload)),
      revelations source = .revealed cell →
      ProtocolState.RevealedInto program state owner payload name published
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, state, decoded,
      _, source, cell, recorded => by
      rw [decodeSourcePrefix?] at decoded
      obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
      unfold ProtocolState.RevealedInto
      rw [currentConfig_entry]
      exact ⟨source, cell, recorded⟩
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, state,
      decoded, closed, source, cell, recorded => by
      cases program with
      | ret _ => cases decoded
      | sample introduced fresh law next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact decodeSourcePrefix?_revealedInto_of_revealed count next _ _ _ _ store history
            rest restDecoded closed (.there source) (.there cell)
            (by rw [Revelations.weaken_there, recorded]; rfl)
      | commit introduced owner' fresh guard next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have different : name ≠ introduced := fun same =>
            fresh (same ▸ source.mem_map_fst)
          exact decodeSourcePrefix?_revealedInto_of_revealed count next _ _ _ _ store history
            rest restDecoded (by simp [different, closed]) (.there source) (.there cell)
            (by rw [Revelations.weaken_there, recorded]; rfl)
      | reveal published' owner' revealed fresh selected unresolved next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have different : name ≠ revealed := fun same => closed (same ▸ unresolved)
          exact decodeSourcePrefix?_revealedInto_of_revealed count next _ _ _ _ store history
            rest restDecoded (fun member => closed (Finset.mem_of_mem_erase member))
            (.there source) (.there cell)
            (by rw [Revelations.reveal_of_ne _ _ _ different, recorded]; rfl)

/-- **Decoding past a reveal records it.** A source state decoded past a reveal
event records the revealed commitment as revealed into the reveal's
publication cell. -/
theorem decodeSourcePrefix?_revealedInto {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} : ∀ (count : Nat)
    {Γ : SourceCtx Player L} {O : Finset VarId} (program : SourceProgram Player L Γ O)
    (refs : ContextRefs layout Γ) (registry : Registry Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L) (state : ProtocolState program),
    decodeSourcePrefix? program refs registry revelations outputs count store history =
      some state →
    ∀ (event : Fin (eventCount program)), event.val < count →
    ∀ {owner : Player} {payload : L.Ty} {name : VarId},
      revealedCell program event = some (name, .commitment owner payload) →
      ProtocolState.RevealedInto program state owner payload name (eventCell program event).1
  | 0, _, _, _, _, _, _, _, _, _, _, _, _, below, _, _, _, _ => absurd below (Nat.not_lt_zero _)
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, state,
      decoded, event, below, owner, payload, name, revealed => by
      cases program with
      | ret _ => cases decoded
      | sample introduced fresh law next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero => cases revealed
          | succ event =>
              exact decodeSourcePrefix?_revealedInto count next _ _ _ _ store history rest
                restDecoded event (by simpa using below) revealed
      | commit introduced owner' fresh guard next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero => cases revealed
          | succ event =>
              exact decodeSourcePrefix?_revealedInto count next _ _ _ _ store history rest
                restDecoded event (by simpa using below) revealed
      | reveal published' owner' revealedName fresh selected unresolved next =>
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          cases event using Fin.cases with
          | zero =>
              change some (revealedName, CellTy.commitment owner' _) = _ at revealed
              obtain ⟨rfl, rfl, rfl⟩ : revealedName = name ∧ owner' = owner ∧ _ := by
                simp only [Option.some.injEq, Prod.mk.injEq, CellTy.commitment.injEq] at revealed
                exact revealed
              exact decodeSourcePrefix?_revealedInto_of_revealed count next _ _ _ _ store history
                rest restDecoded (Finset.notMem_erase _ _) (.there selected) .here
                (Revelations.reveal_source _ selected)
          | succ event =>
              exact decodeSourcePrefix?_revealedInto count next _ _ _ _ store history rest
                restDecoded event (by simpa using below) revealed

/-- **Decoded points record completed reveals.** At the decoded point of a
native configuration, every completed resolve event has revealed the commitment
cell its binding reads into its own publication cell. -/
theorem decodedPoint_revealedInto {config : (graph setup).Config}
    {point : ProtocolState setup.program} (decoded : decodedPoint setup config = some point)
    {event : (graph setup).EventId} (completed : event ∈ config.cut.completed)
    {owner : Player} {payload : L.Ty}
    {binding : EventGraph.FieldRef (graph setup).layout (.binding owner payload)}
    {checks : List (EventGraph.GuardCheck (graph setup).layout payload)}
    (outputEq : (graph setup).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .resolve owner payload binding checks) :
    ProtocolState.RevealedInto setup.program point owner payload
      (fieldCell setup binding.field).1 (eventCell setup.program event).1 := by
  obtain ⟨name, -, revealed, cell⟩ := fieldCell_resolveBinding outputEq codeEq
  rw [cell]
  unfold decodedPoint at decoded
  split at decoded
  · rename_i ordered
    have below : event.val < ordered.choose := (ordered.choose_spec.2 event).mp completed
    exact decodeSourcePrefix?_revealedInto _ setup.program _ _ _ _ _ _ point decoded event
      below revealed
  · cases decoded

end Vegas
