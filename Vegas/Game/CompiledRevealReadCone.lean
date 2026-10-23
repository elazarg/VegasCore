/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealTail
import Vegas.Source.IntendedPlay

/-! # Original public guard reads stay before a compiled disclosure block -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- Direct public guard operands retain their entry references. Commitment
operands are separate: their eventual disclosure is owned by the author. -/
def GuardPublicReadsBefore {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {owner : Player} {subject : VarId} {payload : L.Ty}
    (target : Fin totalCount) (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (guard : SourceGuard L Γ owner subject payload) : Prop :=
  ∀ {name sort} (source : HasVar guard.schema name sort),
    match guard.reads source with
    | .publicData cell => FieldBefore target (refs.get cell).field
    | .publication cell => FieldBefore target (refs.get cell).field
    | .commitment _ => True

def RegistryPublicReadsBefore {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    (target : Fin totalCount) (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (registry : Registry Γ) : Prop :=
  ∀ obligation ∈ registry, GuardPublicReadsBefore target refs obligation.guard

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem GuardPublicReadsBefore.of_refs {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {owner : Player} {subject : VarId} {payload : L.Ty}
    (target : Fin totalCount) (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (before : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field)
    (guard : SourceGuard L Γ owner subject payload) : GuardPublicReadsBefore target refs guard := by
  intro name sort source
  cases read : guard.reads source with
  | publicData cell => exact before cell
  | publication cell => exact before cell
  | commitment cell => trivial

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem GuardPublicReadsBefore.weaken {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {owner : Player} {subject : VarId} {payload : L.Ty} {name : VarId}
    {cell : CellTy Player L} (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (head : FieldRef (fieldLayout inputs outputs) (cellField cell))
    (guard : SourceGuard L Γ owner subject payload)
    (before : GuardPublicReadsBefore target refs guard) :
    GuardPublicReadsBefore target (refs.cons (name := name) head) guard.weaken := by
  intro readName sort source
  have prior := before source
  cases read : guard.reads source with
  | publicData cell =>
      simpa only [SourceGuard.weaken, read, SourceGuardRead.weaken, ContextRefs.cons] using prior
  | publication cell =>
      simpa only [SourceGuard.weaken, read, SourceGuardRead.weaken, ContextRefs.cons] using prior
  | commitment cell =>
      simp only [SourceGuard.weaken, read, SourceGuardRead.weaken]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem RegistryPublicReadsBefore.weaken {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {name : VarId} {cell : CellTy Player L} (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (head : FieldRef (fieldLayout inputs outputs) (cellField cell)) (registry : Registry Γ)
    (before : RegistryPublicReadsBefore target refs registry) :
    RegistryPublicReadsBefore target (refs.cons (name := name) head) registry.weaken := by
  intro obligation member
  obtain ⟨original, present, rfl⟩ := List.mem_map.mp member
  exact GuardPublicReadsBefore.weaken target refs head original.guard (before original present)

/-- A publication referenced by an author's commitment was either already
present at block entry or was emitted by that same author within the block. -/
def RevealReadCone {inputCount totalCount : Nat}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount) (owner : Player) :
    (Fin inputCount ⊕ Fin totalCount) → Prop
  | .inl _ => True
  | .inr event => event.val < target.val ∨ actors event = some owner

def RevealedCommitmentReadCone {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ) (revelations : Revelations Γ) : Prop :=
  ∀ {name owner payload publicationName} (source : HasVar Γ name (.commitment owner payload))
    (publication : HasVar Γ publicationName (.publication payload)),
    revelations source = .revealed publication →
      RevealReadCone actors target owner
        (refs.get publication).field

omit [DecidableEq Player] [IExpr.ResultTypes L] in
 theorem RevealedCommitmentReadCone.of_refs {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (before : ∀ {name cell} (source : HasVar Γ name cell),
      FieldBefore target (refs.get source).field) (revelations : Revelations Γ) :
    RevealedCommitmentReadCone actors target refs revelations := by
  intro name owner payload publicationName source publication _revealed
  have bounded := before publication
  cases field : (refs.get publication).field with
  | inl input => trivial
  | inr event =>
      simp only [field, FieldBefore] at bounded
      exact Or.inl bounded

omit [DecidableEq Player] [IExpr.ResultTypes L] in
 theorem RevealedCommitmentReadCone.reveal {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {name published : VarId} {owner : Player} {payload : L.Ty}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ) (revelations : Revelations Γ)
    (selected : HasVar Γ name (.commitment owner payload))
    (head : FieldRef (fieldLayout inputs outputs) (.publication payload))
    (headCone : RevealReadCone actors target owner head.field)
    (bounded : RevealedCommitmentReadCone actors target refs revelations) :
    RevealedCommitmentReadCone actors target (refs.cons (name := published) head)
      (revelations.reveal selected) := by
  intro readName other sort publicationName source publication revealed
  cases source with
  | there source =>
      cases found : source.sameCell? selected with
      | some same =>
          have ownerEq := (CellTy.commitment.inj same.down.2).1
          have sortEq := (CellTy.commitment.inj same.down.2).2
          cases ownerEq
          cases sortEq
          simp only [Revelations.reveal, HasVar.tail?_there, found] at revealed
          obtain ⟨names, cells⟩ := Revelation.revealed.inj revealed
          cases names
          cases eq_of_heq cells
          exact headCone
      | none =>
          simp only [Revelations.reveal, HasVar.tail?_there, found] at revealed
          cases prior : revelations source with
          | unrevealed =>
              simp only [prior, Revelation.weaken] at revealed
              cases revealed
          | revealed original =>
              simp only [prior, Revelation.weaken] at revealed
              obtain ⟨names, cells⟩ := Revelation.revealed.inj revealed
              cases names
              cases eq_of_heq cells
              exact bounded source original prior


omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem RevealReadCone.of_before {inputCount totalCount : Nat}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount) (owner : Player)
    (field : Fin inputCount ⊕ Fin totalCount) (before : FieldBefore target field) :
    RevealReadCone actors target owner field := by
  cases field with
  | inl _ => trivial
  | inr _ => exact Or.inl before

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem compileGuardRead_field_cone {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {published : VarId} {payload : L.Ty} {author : Player} {sort : L.Ty}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (head : FieldRef (fieldLayout inputs outputs) (.publication payload))
    (revealed : Revelations ((published, .publication payload) :: Γ))
    (bounded : RevealedCommitmentReadCone actors target
      (refs.cons (name := published) head) revealed)
    (read : SourceGuardRead ((published, .publication payload) :: Γ) author sort)
    (direct : match read with
      | .publicData cell => RevealReadCone actors target author
          ((refs.cons (name := published) head).get cell).field
      | .publication cell => RevealReadCone actors target author
          ((refs.cons (name := published) head).get cell).field
      | .commitment _ => True)
    (isRevealed : read.revealed revealed = true)
    (field : Fin inputCount ⊕ Fin totalCount)
    (found : (compileGuardRead refs revealed read isRevealed).field? = some field) :
    RevealReadCone actors target author field := by
  cases read with
  | publicData cell =>
      cases cell with
      | there cell =>
          simp only [compileGuardRead, GuardOperand.field?, Option.some.injEq] at found
          subst field
          exact direct
  | publication cell =>
      cases cell with
      | here => cases found
      | there cell =>
          simp only [compileGuardRead, revealOperand, GuardOperand.field?,
            Option.some.injEq] at found
          subst field
          exact direct
  | commitment cell =>
      simp only [compileGuardRead] at found
      split at found
      · next publication revelation =>
          have cone := bounded cell publication revelation
          cases publication with
          | here => cases found
          | there publication =>
              simp only [revealOperand, GuardOperand.field?, Option.some.injEq] at found
              subst field
              exact cone
      · next revelation =>
          simp [SourceGuardRead.revealed, revelation, Revelation.isRevealed] at isRevealed

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem compileGuard_weaken_field_cone {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {published : VarId} {payload : L.Ty}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (head : FieldRef (fieldLayout inputs outputs) (.publication payload))
    (revealed : Revelations ((published, .publication payload) :: Γ))
    (bounded : RevealedCommitmentReadCone actors target
      (refs.cons (name := published) head) revealed)
    (obligation : Obligation (Player := Player) (L := L) Γ)
    (before : GuardPublicReadsBefore target refs obligation.guard)
    (isRevealed : obligation.weaken.revealed revealed = true)
    (field : Fin inputCount ⊕ Fin totalCount)
    (member : field ∈ (compileGuard refs revealed obligation.weaken isRevealed).readFields) :
    RevealReadCone actors target obligation.owner field := by
  rcases compileGuard_read_origin refs revealed obligation.weaken isRevealed field member with
    subject | ⟨name, sort, source, used, found⟩
  · exact compileGuardRead_field_cone actors target refs head revealed @bounded
      _ trivial _ field subject
  · apply compileGuardRead_field_cone actors target refs head revealed @bounded
      _ ?_ _ field found
    have prior := before source
    cases read : obligation.guard.reads source with
    | publicData cell =>
        simp only [read] at prior
        simp only [Obligation.weaken, SourceGuard.weaken, read, SourceGuardRead.weaken]
        exact RevealReadCone.of_before actors target obligation.owner _ prior
    | publication cell =>
        simp only [read] at prior
        simp only [Obligation.weaken, SourceGuard.weaken, read, SourceGuardRead.weaken]
        exact RevealReadCone.of_before actors target obligation.owner _ prior
    | commitment cell =>
        simp only [Obligation.weaken, SourceGuard.weaken, read, SourceGuardRead.weaken]

omit [DecidableEq Player] [IExpr.ResultTypes L] in
private theorem mem_listReadFields {Field : Type} [DecidableEq Field]
    {layout : Field → EventField Player L} {payload : L.Ty}
    (checks : List (GuardCheck layout payload)) (field : Field)
    (member : field ∈ GuardCheck.listReadFields checks) :
    ∃ check ∈ checks, field ∈ check.readFields := by
  induction checks with
  | nil => simp [GuardCheck.listReadFields] at member
  | cons check checks ih =>
      rw [GuardCheck.listReadFields, Finset.mem_union] at member
      rcases member with head | tail
      · exact ⟨check, List.mem_cons_self, head⟩
      · obtain ⟨other, present, reads⟩ := ih tail
        exact ⟨other, List.mem_cons_of_mem _ present, reads⟩

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- Actual compiled checks read only earlier public fields and publications
of the current author. The obligation owner is derived from completion. -/
theorem compileChecks_read_cone {inputCount totalCount : Nat}
    {inputs : Fin inputCount → EventField Player L}
    {outputs : Fin totalCount → EventField Player L} {Γ : SourceCtx Player L}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (actors : Fin totalCount → Option Player) (target : Fin totalCount)
    (refs : ContextRefs (fieldLayout inputs outputs) Γ)
    (registry : Registry Γ) (revelations : Revelations Γ)
    (selected : HasVar Γ name (.commitment owner payload))
    (head : FieldRef (fieldLayout inputs outputs) (.publication payload))
    (headCone : RevealReadCone actors target owner head.field)
    (publicBefore : RegistryPublicReadsBefore target refs registry)
    (commitmentCone : RevealedCommitmentReadCone actors target refs revelations)
    (field : Fin inputCount ⊕ Fin totalCount)
    (member : field ∈ GuardCheck.listReadFields
      (compileChecks (published := published) refs registry revelations selected)) :
    RevealReadCone actors target owner field := by
  obtain ⟨check, present, reads⟩ := mem_listReadFields _ field member
  obtain ⟨attached, _attachedMember, rfl⟩ := List.mem_map.mp present
  have completedMember := attached.property
  obtain ⟨original, filtered, originalEq⟩ := List.mem_map.mp completedMember
  obtain ⟨originalMember, completed⟩ := List.mem_filter.mp filtered
  have ownerEq := Obligation.owner_eq_of_completedBy original revelations selected completed
  have isRevealed : (original.weaken (x := published)).revealed
      (revelations.reveal (published := published) selected) = true := by
    simpa only [originalEq] using registry.revealed_of_mem_completedBy revelations selected
      attached.property
  have originalReads : field ∈ (compileGuard refs
      (revelations.reveal (published := published) selected)
      (original.weaken (x := published)) isRevealed).readFields := by
    simpa only [originalEq] using reads
  have nextCone : RevealedCommitmentReadCone actors target
      (refs.cons (name := published) head) (revelations.reveal selected) := by
    exact RevealedCommitmentReadCone.reveal (published := published)
      actors target refs revelations selected head headCone @commitmentCone
  rw [← ownerEq]
  exact compileGuard_weaken_field_cone actors target refs head _ @nextCone original
    (publicBefore original originalMember) _ field originalReads

variable (setup : Setup (Player := Player) (L := L))

/-- The actual compiled resolve node reads only the block's prior fields and
fields on its author's chain. Registry and revelation bounds are supplied by
the same compiled disclosure telescope, without a guard-acceptance premise. -/
theorem CompiledSuffix.resolve_read_cone
    {Γ : SourceCtx Player L} {names : Finset VarId}
    {published name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : published ∉ Γ.map Prod.fst)
    (selected : HasVar Γ name (.commitment owner payload))
    (unresolved : name ∈ names)
    (next : SourceProgram Player L ((published, .publication payload) :: Γ)
      (names.erase name))
    (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
    (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.reveal published owner name fresh selected unresolved next))
    (before : ContextRefsBefore refs embedding) (offset : Nat)
    (compiled : CompiledSuffix setup.program
      (.reveal published owner name fresh selected unresolved next)
      refs revelations registry embedding before offset)
    (target : Fin (eventCount setup.program))
    (publicBefore : RegistryPublicReadsBefore target refs registry)
    (commitmentCone : RevealedCommitmentReadCone (toEventGraph setup.program).actor?
      target refs revelations) :
    let event := embedding.event ⟨0, by simp only [eventCount]; omega⟩
    ∀ field, field ∈ ((toEventGraph setup.program).nodes event).readFields →
      RevealReadCone (toEventGraph setup.program).actor? target owner field := by
  let zero : Fin (eventCount (.reveal published owner name fresh selected unresolved next)) :=
    ⟨0, by simp only [eventCount]; omega⟩
  let event := embedding.event zero
  have outputEq : (toEventGraph setup.program).outputLayout event = .publication payload :=
    (embedding.layout_eq zero).trans rfl
  have code : cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) =
      .resolve owner payload (refs.get selected)
        (compileChecks (published := published) refs registry revelations selected) := by
    simpa only [event, zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
      using compiled.nodeEq zero
  have actor : (toEventGraph setup.program).actor? event = some owner :=
    (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor code)
  let head : FieldRef (graphLayout setup.program) (.publication payload) :=
    ⟨.inr event, outputEq⟩
  dsimp only
  intro field member
  change field ∈ ((toEventGraph setup.program).nodes event).readFields at member
  rw [← EventCode.readFields_cast outputEq, code, EventCode.readFields,
    Finset.mem_insert] at member
  rcases member with bound | checks
  · subst field
    cases located : (refs.get selected).field with
    | inl input => trivial
    | inr binding =>
        have bindingOutput : (toEventGraph setup.program).outputLayout binding =
            .binding owner payload := by
          simpa only [located, graphLayout, fieldLayout, Sum.elim_inr, cellField, toEventGraph]
            using (refs.get selected).layout_eq
        exact Or.inr (EventGraph.actor?_of_outputLayout_binding _ bindingOutput)
  · exact compileChecks_read_cone (toEventGraph setup.program).actor? target refs registry
      revelations selected head (Or.inr actor) publicBefore @commitmentCone field checks

end Vegas
