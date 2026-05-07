import Vegas.Core.ToEventGraph.Nodes

/-!
# Checked-program event-graph fields

Storage-field occurrences and final-environment assembly for checked Vegas
programs elaborated to event graphs.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Storage field occurrence in the final state of a source program. -/
inductive ProgramField :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | retField
      {Γ : VCtx P L}
      {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
      (field : VCtxField P L Γ) :
      ProgramField (.ret payoffs)
  | letTail
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.letExpr x e k)
  | sampleTail
      {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.sample x D k)
  | commitTail
      {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.commit x who R k)
  | revealTail
      {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar Γ x (.hidden who b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)}
      (field : ProgramField k) :
      ProgramField (.reveal y who x hx k)

namespace ProgramField

/-- Variable name of a final program field. -/
def name : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramField p → VarId
  | _, _, .retField field => field.name
  | _, _, .letTail field => field.name
  | _, _, .sampleTail field => field.name
  | _, _, .commitTail field => field.name
  | _, _, .revealTail field => field.name

/-- Semantic type of a final program field. -/
def ty : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramField p → L.Ty
  | _, _, .retField field => field.ty
  | _, _, .letTail field => field.ty
  | _, _, .sampleTail field => field.ty
  | _, _, .commitTail field => field.ty
  | _, _, .revealTail field => field.ty

/-- Owner of a final program field, if hidden. -/
def owner : {Γ : VCtx P L} → {p : VegasCore P L Γ} →
    ProgramField p → Option P
  | _, _, .retField field => field.owner
  | _, _, .letTail field => field.owner
  | _, _, .sampleTail field => field.owner
  | _, _, .commitTail field => field.owner
  | _, _, .revealTail field => field.owner

/-- A field is observable by a player when it is public or owned by that player. -/
abbrev VisibleTo {Γ : VCtx P L} {p : VegasCore P L Γ}
    (who : P) (field : ProgramField p) : Prop :=
  field.owner = none ∨ field.owner = some who

/-- Embed a field from the current context into the final field set of a
program. -/
def ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      VCtxField P L Γ → ProgramField p
  | _, .ret _, field => .retField field
  | _, .letExpr x _ k, field =>
      .letTail (ofCurrent k (field.weakenHead (x := x) (τ := .pub _)))
  | _, .sample x _ k, field =>
      .sampleTail (ofCurrent k (field.weakenHead (x := x) (τ := .pub _)))
  | _, .commit x who _ k, field =>
      .commitTail
        (ofCurrent k (field.weakenHead (x := x) (τ := .hidden who _)))
  | _, .reveal y _ _ _ k, field =>
      .revealTail (ofCurrent k (field.weakenHead (x := y) (τ := .pub _)))

@[simp] theorem ty_ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L Γ) →
        (ofCurrent p field).ty = field.ty
  | _, .ret _, field => rfl
  | _, .letExpr _ _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .sample _ _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .commit _ who _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .hidden who _))
  | _, .reveal _ _ _ _ k, field => by
      simpa using ty_ofCurrent k (field.weakenHead (τ := .pub _))

@[simp] theorem owner_ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L Γ) →
        (ofCurrent p field).owner = field.owner
  | _, .ret _, field => rfl
  | _, .letExpr _ _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .sample _ _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .pub _))
  | _, .commit _ who _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .hidden who _))
  | _, .reveal _ _ _ _ k, field => by
      simpa using owner_ofCurrent k (field.weakenHead (τ := .pub _))

theorem owner_eq_none_or_some_of_visible
    {Γ : VCtx P L} (hctx : WFCtx Γ) {who : P}
    (field : VCtxField P L Γ)
    (hvisible : field.name ∈ visibleVars (L := L) who Γ) :
    field.owner = none ∨ field.owner = some who := by
  cases field with
  | mk h =>
      induction h with
      | here =>
          rename_i Γ x τ
          match τ with
          | ⟨_, .pub⟩ =>
              left
              rfl
          | ⟨b, .hidden owner⟩ =>
              by_cases hwho : who = owner
              · subst owner
                right
                rfl
              · have hfresh : Fresh x Γ := WFCtx.fresh_head hctx
                have hnot := not_mem_visibleVars_hidden_other (L := L)
                  (Γ := Γ) (x := x) (who := who) (owner := owner)
                  (τ := b) hfresh hwho
                exact False.elim (hnot hvisible)
      | there h ih =>
          rename_i Γ x y τ τ'
          have htail : WFCtx Γ := WFCtx.tail hctx
          have hfresh : Fresh y Γ := WFCtx.fresh_head hctx
          have hvisibleTail : x ∈ visibleVars (L := L) who Γ := by
            match τ' with
            | ⟨_, .pub⟩ =>
                simp only [visibleVars] at hvisible
                rcases Finset.mem_insert.mp hvisible with hxy | htailVisible
                · exact False.elim
                    (hfresh (by simpa [← hxy] using HasVar.mem_map_fst h))
                · exact htailVisible
            | ⟨_, .hidden owner⟩ =>
                by_cases hwho : who = owner
                · subst owner
                  simp only [visibleVars, ↓reduceIte] at hvisible
                  rcases Finset.mem_insert.mp hvisible with hxy | htailVisible
                  · exact False.elim
                      (hfresh (by simpa [← hxy] using HasVar.mem_map_fst h))
                  · exact htailVisible
                · simp only [visibleVars, hwho, ↓reduceIte] at hvisible
                  exact hvisible
          exact ih htail hvisibleTail

/-- Current-context fields embedded into a program's final field set. -/
noncomputable def currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) : Finset (ProgramField p) := by
  classical
  exact ((VCtxField.enumerate Γ).map (fun field => ofCurrent p field)).toFinset

/-- Current-context fields visible to a player. -/
noncomputable def visibleCurrentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) (who : P) :
    Finset (ProgramField p) := by
  classical
  exact (currentFields p).filter
    (fun field => field.VisibleTo who)

theorem ofCurrent_mem_currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (field : VCtxField P L Γ) :
    ofCurrent p field ∈ currentFields p := by
  classical
  exact List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨field, VCtxField.mem_enumerate field, rfl⟩)

/-- Build the full current `VEnv` from a graph read environment over all
current fields. -/
noncomputable def currentReadEnvToVEnv
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (ρ : EventGraph.ReadEnv L (ProgramField p)
      (fun field => field.ty) (currentFields p)) :
    VEnv L Γ :=
  fun x τ h =>
    by
      let field : VCtxField P L Γ := .mk h
      have hmem : ofCurrent p field ∈ currentFields p :=
        ofCurrent_mem_currentFields p field
      simpa [field, VCtxField.ty] using
        (ρ.value (ofCurrent p field) hmem)

/-- Field written by a source node. -/
def writtenBy :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramNode p → ProgramField p
  | _, _, .letHere (x := x) (k := k) =>
      .letTail (ofCurrent k (.mk (x := x) (τ := .pub _) .here))
  | _, _, .letTail node => .letTail (writtenBy node)
  | _, _, .sampleHere (x := x) (k := k) =>
      .sampleTail (ofCurrent k (.mk (x := x) (τ := .pub _) .here))
  | _, _, .sampleTail node => .sampleTail (writtenBy node)
  | _, _, .commitHere (x := x) (who := who) (k := k) =>
      .commitTail (ofCurrent k (.mk (x := x) (τ := .hidden who _) .here))
  | _, _, .commitTail node => .commitTail (writtenBy node)
  | _, _, .revealHere (y := y) (k := k) =>
      .revealTail (ofCurrent k (.mk (x := y) (τ := .pub _) .here))
  | _, _, .revealTail node => .revealTail (writtenBy node)

/-- Structural source of a final program field: either it is an initial field
from the program's input context, or it is written by a unique source node.

This follows the syntax tree instead of searching completed result slices, so
field lookup is stable under unrelated frontier updates. -/
def source :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramField p → VCtxField P L Γ ⊕ ProgramNode p
  | _, .ret _, .retField field => .inl field
  | _, .letExpr _ _ _, .letTail field =>
      match source field with
      | .inl (.mk .here) => .inr .letHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.letTail node)
  | _, .sample _ _ _, .sampleTail field =>
      match source field with
      | .inl (.mk .here) => .inr .sampleHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.sampleTail node)
  | _, .commit _ _ _ _, .commitTail field =>
      match source field with
      | .inl (.mk .here) => .inr .commitHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.commitTail node)
  | _, .reveal _ _ _ _ _, .revealTail field =>
      match source field with
      | .inl (.mk .here) => .inr .revealHere
      | .inl (.mk (.there h)) => .inl (.mk h)
      | .inr node => .inr (.revealTail node)

/-- The unique source node that writes this field, if the field is not part of
the program's input context. -/
def writer? :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramField p → Option (ProgramNode p)
  | _, _, field =>
      match source field with
      | .inl _ => none
      | .inr node => some node

@[simp] theorem source_ofCurrent :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L Γ) →
        ProgramField.source (ProgramField.ofCurrent p field) = Sum.inl field
  | _, .ret _, field => by
      rfl
  | _, .letExpr _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]
  | _, .sample _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]
  | _, .commit _ _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]
  | _, .reveal _ _ _ _ k, field => by
      cases field with
      | mk h =>
          simp [ProgramField.ofCurrent, ProgramField.source,
            VCtxField.weakenHead, source_ofCurrent k]

@[simp] theorem source_writtenBy :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (node : ProgramNode p) →
        ProgramField.source (ProgramField.writtenBy node) = Sum.inr node
  | _, .letExpr _ _ _, .letHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .letExpr _ _ _, .letTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]
  | _, .sample _ _ _, .sampleHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .sample _ _ _, .sampleTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]
  | _, .commit _ _ _ _, .commitHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .commit _ _ _ _, .commitTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]
  | _, .reveal _ _ _ _ _, .revealHere => by
      simp [ProgramField.source, ProgramField.writtenBy]
  | _, .reveal _ _ _ _ _, .revealTail node => by
      simp [ProgramField.source, ProgramField.writtenBy, source_writtenBy node]

/-- A field whose structural source is an input-context field is that current
field embedded into the program's final field set. -/
theorem eq_ofCurrent_of_source_eq_inl :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      {field : ProgramField p} → {current : VCtxField P L Γ} →
        ProgramField.source field = Sum.inl current →
          field = ProgramField.ofCurrent p current
  | _, .ret _, .retField field, current, h => by
      cases h
      rfl
  | _, .letExpr x e k, .letTail field, current, h => by
      cases hsource : ProgramField.source field with
      | inl inner =>
          cases inner with
          | mk hvar =>
              cases hvar with
              | here =>
                  simp [ProgramField.source, hsource] at h
              | there htail =>
                  have hcurrent :
                      (VCtxField.mk htail : VCtxField P L _) = current := by
                    simpa [ProgramField.source, hsource] using h
                  cases hcurrent
                  have hfield :
                      field =
                        ProgramField.ofCurrent k (VCtxField.mk (VHasVar.there htail)) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.ofCurrent, VCtxField.weakenHead]
      | inr node =>
          simp [ProgramField.source, hsource] at h
  | _, .sample x D k, .sampleTail field, current, h => by
      cases hsource : ProgramField.source field with
      | inl inner =>
          cases inner with
          | mk hvar =>
              cases hvar with
              | here =>
                  simp [ProgramField.source, hsource] at h
              | there htail =>
                  have hcurrent :
                      (VCtxField.mk htail : VCtxField P L _) = current := by
                    simpa [ProgramField.source, hsource] using h
                  cases hcurrent
                  have hfield :
                      field =
                        ProgramField.ofCurrent k (VCtxField.mk (VHasVar.there htail)) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.ofCurrent, VCtxField.weakenHead]
      | inr node =>
          simp [ProgramField.source, hsource] at h
  | _, .commit x who R k, .commitTail field, current, h => by
      cases hsource : ProgramField.source field with
      | inl inner =>
          cases inner with
          | mk hvar =>
              cases hvar with
              | here =>
                  simp [ProgramField.source, hsource] at h
              | there htail =>
                  have hcurrent :
                      (VCtxField.mk htail : VCtxField P L _) = current := by
                    simpa [ProgramField.source, hsource] using h
                  cases hcurrent
                  have hfield :
                      field =
                        ProgramField.ofCurrent k (VCtxField.mk (VHasVar.there htail)) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.ofCurrent, VCtxField.weakenHead]
      | inr node =>
          simp [ProgramField.source, hsource] at h
  | _, .reveal y who x hx k, .revealTail field, current, h => by
      cases hsource : ProgramField.source field with
      | inl inner =>
          cases inner with
          | mk hvar =>
              cases hvar with
              | here =>
                  simp [ProgramField.source, hsource] at h
              | there htail =>
                  have hcurrent :
                      (VCtxField.mk htail : VCtxField P L _) = current := by
                    simpa [ProgramField.source, hsource] using h
                  cases hcurrent
                  have hfield :
                      field =
                        ProgramField.ofCurrent k (VCtxField.mk (VHasVar.there htail)) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.ofCurrent, VCtxField.weakenHead]
      | inr node =>
          simp [ProgramField.source, hsource] at h

/-- A field whose structural source is a source node is the field written by
that node. -/
theorem eq_writtenBy_of_source_eq_inr :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      {field : ProgramField p} → {node : ProgramNode p} →
        ProgramField.source field = Sum.inr node →
          field = ProgramField.writtenBy node
  | _, .ret _, .retField field, node, h => by
      simp [ProgramField.source] at h
  | _, .letExpr x e k, .letTail field, node, h => by
      cases hsource : ProgramField.source field with
      | inl current =>
          cases current with
          | mk hvar =>
              cases hvar with
              | here =>
                  have hnode :
                      ProgramNode.letHere (x := x) (e := e) (k := k) = node := by
                    simpa [ProgramField.source, hsource] using h
                  cases hnode
                  have hfield :
                      field =
                        ProgramField.ofCurrent k
                          (VCtxField.mk (x := x) (τ := .pub _) VHasVar.here) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.writtenBy]
              | there htail =>
                  simp [ProgramField.source, hsource] at h
      | inr inner =>
          have hnode : ProgramNode.letTail inner = node := by
            simpa [ProgramField.source, hsource] using h
          cases hnode
          have hfield : field = ProgramField.writtenBy inner :=
            eq_writtenBy_of_source_eq_inr hsource
          rw [hfield]
          rfl
  | _, .sample x D k, .sampleTail field, node, h => by
      cases hsource : ProgramField.source field with
      | inl current =>
          cases current with
          | mk hvar =>
              cases hvar with
              | here =>
                  have hnode :
                      ProgramNode.sampleHere (x := x) (D := D) (k := k) = node := by
                    simpa [ProgramField.source, hsource] using h
                  cases hnode
                  have hfield :
                      field =
                        ProgramField.ofCurrent k
                          (VCtxField.mk (x := x) (τ := .pub _) VHasVar.here) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.writtenBy]
              | there htail =>
                  simp [ProgramField.source, hsource] at h
      | inr inner =>
          have hnode : ProgramNode.sampleTail inner = node := by
            simpa [ProgramField.source, hsource] using h
          cases hnode
          have hfield : field = ProgramField.writtenBy inner :=
            eq_writtenBy_of_source_eq_inr hsource
          rw [hfield]
          rfl
  | _, .commit x who R k, .commitTail field, node, h => by
      cases hsource : ProgramField.source field with
      | inl current =>
          cases current with
          | mk hvar =>
              cases hvar with
              | here =>
                  have hnode :
                      ProgramNode.commitHere (x := x) (who := who) (R := R)
                        (k := k) = node := by
                    simpa [ProgramField.source, hsource] using h
                  cases hnode
                  have hfield :
                      field =
                        ProgramField.ofCurrent k
                          (VCtxField.mk (x := x) (τ := .hidden who _) VHasVar.here) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.writtenBy]
              | there htail =>
                  simp [ProgramField.source, hsource] at h
      | inr inner =>
          have hnode : ProgramNode.commitTail inner = node := by
            simpa [ProgramField.source, hsource] using h
          cases hnode
          have hfield : field = ProgramField.writtenBy inner :=
            eq_writtenBy_of_source_eq_inr hsource
          rw [hfield]
          rfl
  | _, .reveal y who x hx k, .revealTail field, node, h => by
      cases hsource : ProgramField.source field with
      | inl current =>
          cases current with
          | mk hvar =>
              cases hvar with
              | here =>
                  have hnode :
                      ProgramNode.revealHere (y := y) (who := who) (x := x)
                        (hx := hx) (k := k) = node := by
                    simpa [ProgramField.source, hsource] using h
                  cases hnode
                  have hfield :
                      field =
                        ProgramField.ofCurrent k
                          (VCtxField.mk (x := y) (τ := .pub _) VHasVar.here) :=
                    eq_ofCurrent_of_source_eq_inl hsource
                  rw [hfield]
                  simp [ProgramField.writtenBy]
              | there htail =>
                  simp [ProgramField.source, hsource] at h
      | inr inner =>
          have hnode : ProgramNode.revealTail inner = node := by
            simpa [ProgramField.source, hsource] using h
          cases hnode
          have hfield : field = ProgramField.writtenBy inner :=
            eq_writtenBy_of_source_eq_inr hsource
          rw [hfield]
          rfl

@[simp] theorem writer?_writtenBy
    {Γ : VCtx P L} {p : VegasCore P L Γ} (node : ProgramNode p) :
    ProgramField.writer? (ProgramField.writtenBy node) = some node := by
  simp [ProgramField.writer?]

theorem writer?_eq_none_of_mem_currentFields
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {field : ProgramField p}
    (hmem : field ∈ currentFields p) :
    ProgramField.writer? field = none := by
  classical
  unfold currentFields at hmem
  have hlist :
      field ∈
        (VCtxField.enumerate Γ).map (fun current => ofCurrent p current) :=
    List.mem_toFinset.mp hmem
  rcases List.mem_map.mp hlist with ⟨current, _hcurrent, rfl⟩
  simp [ProgramField.writer?]

private theorem tail_currentFields_or_eq_writtenBy_here
    {Γ : VCtx P L} {x : VarId} {τ : BindTy P L}
    {p : VegasCore P L Γ} {k : VegasCore P L ((x, τ) :: Γ)}
    (tail : ProgramField k → ProgramField p)
    (head : ProgramNode p)
    (tail_there :
      ∀ {y σ} (h : VHasVar Γ y σ),
        tail (ofCurrent k (.mk (VHasVar.there h))) =
          ofCurrent p (.mk h))
    (tail_here :
      tail (ofCurrent k (.mk (x := x) (τ := τ) VHasVar.here)) =
        ProgramField.writtenBy head)
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    tail field ∈ currentFields p ∨
      tail field = ProgramField.writtenBy head := by
  classical
  unfold currentFields at h ⊢
  simp only [List.mem_toFinset, List.mem_map] at h ⊢
  rcases h with ⟨current, _hcurrent, hfield⟩
  cases current with
  | mk hvar =>
      cases hvar with
      | here =>
          right
          rw [← hfield]
          exact tail_here
      | there htail =>
          left
          refine ⟨.mk htail, VCtxField.mem_enumerate (.mk htail), ?_⟩
          rw [← hfield]
          exact (tail_there htail).symm

theorem letTail_currentFields_or_eq_writtenBy_letHere
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.letTail (e := e) field ∈
        currentFields (.letExpr x e k) ∨
      ProgramField.letTail (e := e) field =
        ProgramField.writtenBy
          (.letHere (x := x) (e := e) (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .letExpr x e k) (k := k) ProgramField.letTail
    (ProgramNode.letHere (x := x) (e := e) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

theorem sampleTail_currentFields_or_eq_writtenBy_sampleHere
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.sampleTail (D := D) field ∈
        currentFields (.sample x D k) ∨
      ProgramField.sampleTail (D := D) field =
        ProgramField.writtenBy
          (.sampleHere (x := x) (D := D) (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .sample x D k) (k := k) ProgramField.sampleTail
    (ProgramNode.sampleHere (x := x) (D := D) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

theorem commitTail_currentFields_or_eq_writtenBy_commitHere
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.commitTail (R := R) field ∈
        currentFields (.commit x who R k) ∨
      ProgramField.commitTail (R := R) field =
        ProgramField.writtenBy
          (.commitHere (x := x) (who := who) (R := R) (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .commit x who R k) (k := k) ProgramField.commitTail
    (ProgramNode.commitHere (x := x) (who := who) (R := R) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

theorem revealTail_currentFields_or_eq_writtenBy_revealHere
    {Γ : VCtx P L} {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    {field : ProgramField k}
    (h : field ∈ currentFields k) :
    ProgramField.revealTail (x := x) (hx := hx) field ∈
        currentFields (.reveal y who x hx k) ∨
      ProgramField.revealTail (x := x) (hx := hx) field =
        ProgramField.writtenBy
          (.revealHere (y := y) (who := who) (x := x) (hx := hx)
            (k := k)) := by
  exact tail_currentFields_or_eq_writtenBy_here
    (p := .reveal y who x hx k) (k := k) ProgramField.revealTail
    (ProgramNode.revealHere (y := y) (who := who) (x := x)
      (hx := hx) (k := k))
    (by intro _ _ _; rfl)
    (by simp [ProgramField.writtenBy])
    h

/-- Hidden field read by a reveal node. For non-reveal nodes this is `none`. -/
def revealSource? :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramNode p → Option (ProgramField p)
  | _, _, .letHere => none
  | _, _, .letTail node => Option.map .letTail (revealSource? node)
  | _, _, .sampleHere => none
  | _, _, .sampleTail node => Option.map .sampleTail (revealSource? node)
  | _, _, .commitHere => none
  | _, _, .commitTail node => Option.map .commitTail (revealSource? node)
  | _, _, .revealHere (hx := hx) (k := k) =>
      some (.revealTail (ofCurrent k (.mk (VHasVar.there hx))))
  | _, _, .revealTail node => Option.map .revealTail (revealSource? node)

/-- Enumerate final fields of a source program. -/
def enumerate :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → List (ProgramField p)
  | Γ, .ret payoffs =>
      (VCtxField.enumerate Γ).map (fun field => .retField (payoffs := payoffs) field)
  | _, .letExpr _ _ k => (enumerate k).map .letTail
  | _, .sample _ _ k => (enumerate k).map .sampleTail
  | _, .commit _ _ _ k => (enumerate k).map .commitTail
  | _, .reveal _ _ _ _ k => (enumerate k).map .revealTail

theorem mem_enumerate :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (field : ProgramField p) → field ∈ enumerate p
  | _, _, .retField field => by
      exact List.mem_map.mpr
        ⟨field, VCtxField.mem_enumerate field, rfl⟩
  | _, _, .letTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩
  | _, _, .sampleTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩
  | _, _, .commitTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩
  | _, _, .revealTail field => by
      exact List.mem_map.mpr ⟨field, mem_enumerate field, rfl⟩

@[reducible] noncomputable instance instDecidableEq
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    DecidableEq (ProgramField p) :=
  Classical.decEq _

@[reducible] noncomputable instance instFintype
    {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Fintype (ProgramField p) :=
  Fintype.ofList (enumerate p) mem_enumerate

@[reducible] noncomputable def finiteTypeOfProof :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      FiniteVCtxProof Γ → FiniteProgramProof p →
        (field : ProgramField p) → FiniteType L field.ty
  | _, .ret _, hΓ, .ret, .retField field =>
      VCtxField.finiteTypeOfProof hΓ field
  | _, .letExpr (x := x) (b := b) _ _k,
      hΓ, .letExpr head tail, .letTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((x, .pub b) :: _) from
          .cons head hΓ)
        tail field
  | _, .sample (x := x) (b := b) _ _k,
      hΓ, .sample head tail, .sampleTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((x, .pub b) :: _) from
          .cons head hΓ)
        tail field
  | _, .commit (x := x) (who := who) (b := b) _ _k,
      hΓ, .commit head tail, .commitTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((x, .hidden who b) :: _) from
          .cons head hΓ)
        tail field
  | _, .reveal (y := y) (b := b) _ _ _ _k,
      hΓ, .reveal head tail, .revealTail field =>
      finiteTypeOfProof
        (show FiniteVCtxProof ((y, .pub b) :: _) from
          .cons head hΓ)
        tail field

@[reducible] noncomputable def instFintypeValue
    (g : WFProgram P L) [hfinite : FiniteDomains g]
    (field : ProgramField g.prog) :
    Fintype (L.Val field.ty) :=
  (finiteTypeOfProof hfinite.context.proof hfinite.program.proof field).fintype

/-- Finset of final fields. -/
noncomputable def finset {Γ : VCtx P L} (p : VegasCore P L Γ) :
    Finset (ProgramField p) := by
  classical
  exact (enumerate p).toFinset

@[simp] theorem mem_finset
    {Γ : VCtx P L} (p : VegasCore P L Γ) (field : ProgramField p) :
    field ∈ finset p := by
  classical
  exact List.mem_toFinset.mpr (mem_enumerate field)

/-- Interpret a source expression over the public current context as a
event-graph-local expression. The read set is the current source scope; this is
intentionally conservative until source-expression dependency projection is
made explicit. -/
noncomputable def publicEventExpr
    {Γ : VCtx P L} (p : VegasCore P L Γ) {b : L.Ty}
    (e : L.Expr (erasePubVCtx Γ) b) :
    EventGraph.EventExpr L (ProgramField p)
      (fun field => field.ty) b where
  reads := currentFields p
  eval := fun ρ =>
    L.eval e (VEnv.erasePubEnv (currentReadEnvToVEnv p ρ))

/-- Interpret a source distribution over the public current context as a
event-graph-local PMF kernel. Normalization is supplied by the checked program. -/
noncomputable def publicEventDist
    {Γ : VCtx P L} (p : VegasCore P L Γ) {b : L.Ty}
    (D : L.DistExpr (erasePubVCtx Γ) b)
    (normalized :
      ∀ env : VEnv L Γ,
        FWeight.totalWeight (L.evalDist D (VEnv.eraseSampleEnv env)) = 1) :
    EventGraph.EventDist L (ProgramField p)
      (fun field => field.ty) b where
  reads := currentFields p
  eval := fun ρ =>
    (L.evalDist D
        (VEnv.eraseSampleEnv (currentReadEnvToVEnv p ρ))).toPMF
      (normalized (currentReadEnvToVEnv p ρ))

/-- Interpret a source commit guard as an event-graph-local guard. The proposed
commit value is supplied separately from the current event-graph environment. -/
noncomputable def commitEventGuard
    {Γ : VCtx P L} (p : VegasCore P L Γ) {x : VarId} {b : L.Ty}
    {who : P} (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
    (field : ProgramField p) (hty : field.ty = b)
    (hctx : WFCtx Γ)
    (hfresh : Fresh x Γ)
    (hguard : GuardUsesOnly (L := L) (Γ := Γ) (x := x)
      (who := who) R)
    (hlegal :
      ∀ env : Env L.Val (eraseVCtx Γ),
        ∃ a : L.Val b,
          evalGuard (Player := P) (L := L) R a env = true) :
    EventGraph.EventGuard L (ProgramField p)
      (fun field => field.ty) field where
  reads := currentFields p
  visibleReads := visibleCurrentFields p who
  visibleReads_subset_reads := by
    intro read hread
    exact (Finset.mem_filter.mp hread).1
  eval := fun value ρ =>
    evalGuard (Player := P) (L := L) R
      (cast (by rw [hty]) value)
      (VEnv.eraseEnv (currentReadEnvToVEnv p ρ))
  eval_eq_of_visible_eq := by
    intro value ρ₁ ρ₂ hvisible
    apply evalGuard_eq_of_obsEq hfresh hguard
    intro y τ hy hyvisible
    rcases HasVar.toVHasVar (Γ := Γ) hy with
      ⟨σ, hv, ⟨hτ⟩⟩
    cases hτ
    let current : VCtxField P L Γ := .mk hv
    let read := ofCurrent p current
    have hmem : read ∈ currentFields p := by
      exact ofCurrent_mem_currentFields p current
    have hvisibleRead : read ∈ visibleCurrentFields p who := by
      have howner :=
        owner_eq_none_or_some_of_visible hctx current hyvisible
      exact Finset.mem_filter.mpr
        ⟨hmem, by
          simpa [ProgramField.VisibleTo, read, current,
            ProgramField.owner_ofCurrent] using howner⟩
    have heq := hvisible read hmem hmem hvisibleRead
    have hnodup : ((eraseVCtx Γ).map Prod.fst).Nodup := by
      simpa [eraseVCtx_map_fst] using hctx
    have hy_eq : hy = hv.toErased := HasVar.eq_of_nodup hnodup hy hv.toErased
    rw [hy_eq]
    simp [read, current, currentReadEnvToVEnv, heq]
  satisfiable := by
    intro ρ
    rcases hlegal (VEnv.eraseEnv (currentReadEnvToVEnv p ρ)) with
      ⟨value, hvalue⟩
    refine ⟨cast (by rw [hty]) value, ?_⟩
    simpa [evalGuard] using hvalue

/-- Transport a graph expression across an equality of result types. -/
noncomputable def castEventExpr
    {Γ : VCtx P L} {p : VegasCore P L Γ} {src dst : L.Ty}
    (h : src = dst)
    (expr : EventGraph.EventExpr L (ProgramField p)
      (fun field => field.ty) src) :
    EventGraph.EventExpr L (ProgramField p)
      (fun field => field.ty) dst where
  reads := expr.reads
  eval := fun ρ => cast (by rw [h]) (expr.eval ρ)

/-- Transport a graph distribution across an equality of result types. -/
noncomputable def castEventDist
    {Γ : VCtx P L} {p : VegasCore P L Γ} {src dst : L.Ty}
    (h : src = dst)
    (dist : EventGraph.EventDist L (ProgramField p)
      (fun field => field.ty) src) :
    EventGraph.EventDist L (ProgramField p)
      (fun field => field.ty) dst where
  reads := dist.reads
  eval := fun ρ => cast (by rw [h]) (dist.eval ρ)

/-- A write slice over the final field set of a source program. -/
abbrev WriteSlice {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  (field : ProgramField p) →
    Option (EventGraph.StoredValue (L.Val field.ty))

/-- Empty source write slice. -/
def emptySlice {Γ : VCtx P L} (p : VegasCore P L Γ) :
    WriteSlice p :=
  fun _ => none

/-- Singleton source write slice. -/
noncomputable def singleSlice
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (field : ProgramField p)
    (value : EventGraph.StoredValue (L.Val field.ty)) :
    WriteSlice p :=
  fun other =>
    if h : other = field then
      some (cast (by rw [h]) value)
    else
      none

@[simp] theorem singleSlice_self
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (field : ProgramField p)
    (value : EventGraph.StoredValue (L.Val field.ty)) :
    singleSlice field value field = some value := by
  simp [singleSlice]

/-- Initial value of a final field, if it comes from the initial context. -/
noncomputable def initialValue?
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    (field : ProgramField p) :
    Option (L.Val field.ty) := by
  classical
  exact
    if h : ∃ current : VCtxField P L Γ, ofCurrent p current = field then
      let current := Classical.choose h
      let hfield : ofCurrent p current = field := Classical.choose_spec h
      some (cast (by rw [← hfield, ty_ofCurrent]) (current.value env))
    else
      none

/-- Current-context fields are available from the initial source environment. -/
theorem initialValue?_isSome_of_mem_currentFields
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    {field : ProgramField p}
    (hmem : field ∈ currentFields p) :
    (initialValue? p env field).isSome := by
  classical
  unfold currentFields at hmem
  have hlist :
      field ∈
        (VCtxField.enumerate Γ).map (fun current => ofCurrent p current) :=
    List.mem_toFinset.mp hmem
  rcases List.mem_map.mp hlist with ⟨current, _hcurrent, hfield⟩
  unfold initialValue?
  rw [dif_pos ⟨current, hfield⟩]
  simp

/-- Value of a final field under a partial node-result assignment. Written
fields are read from their writer's completed slice; initial fields are read
from the initial environment. -/
noncomputable def value?
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (result : ProgramNode p → Option (WriteSlice p))
    (field : ProgramField p) :
    Option (L.Val field.ty) := by
  exact
    match writer? field with
    | some node =>
        match result node with
        | some slice =>
            match slice field with
            | some stored => some stored.raw
            | none => initialValue? p env field
        | none => initialValue? p env field
    | none => initialValue? p env field

theorem value?_isSome_of_result_slice
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p} {node : ProgramNode p} {slice : WriteSlice p}
    {stored : EventGraph.StoredValue (L.Val field.ty)}
    (hwriter : writer? field = some node)
    (hresult : result node = some slice)
    (hslice : slice field = some stored) :
    (value? env result field).isSome := by
  simp [value?, hwriter, hresult, hslice]

theorem value?_isSome_of_initialValue?
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p}
    (hinitial : (initialValue? p env field).isSome) :
    (value? env result field).isSome := by
  cases hwriter : writer? field with
  | none =>
      simpa [value?, hwriter] using hinitial
  | some node =>
      cases hresult : result node with
      | none =>
          simpa [value?, hwriter, hresult] using hinitial
      | some slice =>
          cases hslice : slice field with
          | none =>
              simpa [value?, hwriter, hresult, hslice] using hinitial
          | some stored =>
              simp [value?, hwriter, hresult, hslice]

theorem value?_update_of_writer?_ne
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {result : ProgramNode p → Option (WriteSlice p)}
    {field : ProgramField p} {node : ProgramNode p}
    {slice : WriteSlice p}
    (hne : ProgramField.writer? field ≠ some node) :
    ProgramField.value? env
        (fun candidate => if candidate = node then some slice else result candidate)
        field =
      ProgramField.value? env result field := by
  classical
  cases hwriter : ProgramField.writer? field with
  | none =>
      simp [ProgramField.value?, hwriter]
  | some writer =>
      have hwriter_ne : writer ≠ node := by
        intro heq
        subst writer
        exact hne hwriter
      simp [ProgramField.value?, hwriter, hwriter_ne]

/-- A read environment assembled from a result assignment and a proof that all
declared reads are already available. -/
noncomputable def readEnvOfResult
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (result : ProgramNode p → Option (WriteSlice p))
    (reads : Finset (ProgramField p))
    (available :
      ∀ field, field ∈ reads → (value? env result field).isSome) :
    EventGraph.ReadEnv L (ProgramField p) (fun field => field.ty) reads where
  value field hmem :=
    Classical.choose
      (Option.isSome_iff_exists.mp (available field hmem))

theorem readEnvOfResult_value_eq_of_value?_eq
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    {left right : ProgramNode p → Option (WriteSlice p)}
    {reads : Finset (ProgramField p)}
    {availableLeft :
      ∀ field, field ∈ reads → (value? env left field).isSome}
    {availableRight :
      ∀ field, field ∈ reads → (value? env right field).isSome}
    {field : ProgramField p} {hleft : field ∈ reads}
    {hright : field ∈ reads}
    (heq : value? env left field = value? env right field) :
    (readEnvOfResult env left reads availableLeft).value field hleft =
      (readEnvOfResult env right reads availableRight).value field hright := by
  classical
  let leftValue :=
    (readEnvOfResult env left reads availableLeft).value field hleft
  let rightValue :=
    (readEnvOfResult env right reads availableRight).value field hright
  have hleftValue :
      value? env left field = some leftValue :=
    Classical.choose_spec
      (Option.isSome_iff_exists.mp (availableLeft field hleft))
  have hrightValue :
      value? env right field = some rightValue :=
    Classical.choose_spec
      (Option.isSome_iff_exists.mp (availableRight field hright))
  have hsome : some leftValue = some rightValue := by
    rw [heq] at hleftValue
    rw [hrightValue] at hleftValue
    exact hleftValue.symm
  exact Option.some.inj hsome

/-- Final visibility context reached after all source nodes of a program have
executed. -/
def finalVCtx : {Γ : VCtx P L} → VegasCore P L Γ → VCtx P L
  | Γ, .ret _ => Γ
  | _, .letExpr _ _ k => finalVCtx k
  | _, .sample _ _ k => finalVCtx k
  | _, .commit _ _ _ k => finalVCtx k
  | _, .reveal _ _ _ _ k => finalVCtx k

/-- Terminal payoff expressions of a source program, typed over its final
context. -/
def finalPayoffs :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      List (P × L.Expr (erasePubVCtx (finalVCtx p)) L.int)
  | _, .ret payoffs => payoffs
  | _, .letExpr _ _ k => finalPayoffs k
  | _, .sample _ _ k => finalPayoffs k
  | _, .commit _ _ _ k => finalPayoffs k
  | _, .reveal _ _ _ _ k => finalPayoffs k

/-- Embed a final context field into the final field set of the source
program. -/
def ofFinal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      VCtxField P L (finalVCtx p) → ProgramField p
  | _, .ret _, field => .retField field
  | _, .letExpr _ _ k, field => .letTail (ofFinal k field)
  | _, .sample _ _ k, field => .sampleTail (ofFinal k field)
  | _, .commit _ _ _ k, field => .commitTail (ofFinal k field)
  | _, .reveal _ _ _ _ k, field => .revealTail (ofFinal k field)

@[simp] theorem ty_ofFinal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L (finalVCtx p)) →
        (ofFinal p field).ty = field.ty
  | _, .ret _, _ => rfl
  | _, .letExpr _ _ k, field => by
      exact ty_ofFinal k field
  | _, .sample _ _ k, field => by
      exact ty_ofFinal k field
  | _, .commit _ _ _ k, field => by
      exact ty_ofFinal k field
  | _, .reveal _ _ _ _ k, field => by
      exact ty_ofFinal k field

/-- Assemble the final `VEnv` when every final field has a value. -/
noncomputable def finalEnv?
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (value? : (field : ProgramField p) → Option (L.Val field.ty)) :
    Option (VEnv L (finalVCtx p)) := by
  classical
  exact
    if available :
        ∀ field : VCtxField P L (finalVCtx p),
          (value? (ofFinal p field)).isSome then
      some fun x τ h =>
        cast (by
          rw [ty_ofFinal p (.mk h)]
          rfl)
          (Classical.choose
            (Option.isSome_iff_exists.mp (available (.mk h))))
    else
      none

end ProgramField

end Vegas
