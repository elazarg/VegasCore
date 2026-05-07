import Vegas.Core.ToEventGraph.Fields

/-!
# Checked-program event-graph obligations

Static obligations and node semantics used by the Core-to-EventGraph
elaboration.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ProgramNode

/-- Static obligations needed to interpret a program occurrence in the syntax
graph layer. -/
structure ProgramObligations {Γ : VCtx P L} (p : VegasCore P L Γ) where
  hctx : WFCtx Γ
  fresh : FreshBindings p
  hscoped : ViewScoped p
  legal : Legal p
  normalized : NormalizedDists p

namespace ProgramObligations

def letTail :
    {Γ : VCtx P L} → {x : VarId} → {b : L.Ty} →
      {e : L.Expr (erasePubVCtx Γ) b} →
      {k : VegasCore P L ((x, .pub b) :: Γ)} →
      ProgramObligations (.letExpr x e k) → ProgramObligations k
  | _, _, _, _, _, obs =>
      { hctx := WFCtx.cons obs.fresh.1 obs.hctx
        fresh := obs.fresh.2
        hscoped := obs.hscoped
        legal := obs.legal
        normalized := obs.normalized }

def sampleTail :
    {Γ : VCtx P L} → {x : VarId} → {b : L.Ty} →
      {D : L.DistExpr (erasePubVCtx Γ) b} →
      {k : VegasCore P L ((x, .pub b) :: Γ)} →
      ProgramObligations (.sample x D k) → ProgramObligations k
  | _, _, _, _, _, obs =>
      { hctx := WFCtx.cons obs.fresh.1 obs.hctx
        fresh := obs.fresh.2
        hscoped := obs.hscoped
        legal := obs.legal
        normalized := obs.normalized.2 }

def commitTail :
    {Γ : VCtx P L} → {x : VarId} → {who : P} → {b : L.Ty} →
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool} →
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} →
      ProgramObligations (.commit x who R k) → ProgramObligations k
  | _, _, _, _, _, _, obs =>
      { hctx := WFCtx.cons obs.fresh.1 obs.hctx
        fresh := obs.fresh.2
        hscoped := obs.hscoped.2
        legal := obs.legal.2
        normalized := obs.normalized }

def revealTail :
    {Γ : VCtx P L} → {y : VarId} → {who : P} → {x : VarId} →
      {b : L.Ty} → {hx : VHasVar Γ x (.hidden who b)} →
      {k : VegasCore P L ((y, .pub b) :: Γ)} →
      ProgramObligations (.reveal y who x hx k) → ProgramObligations k
  | _, _, _, _, _, _, _, obs =>
      { hctx := WFCtx.cons obs.fresh.1 obs.hctx
        fresh := obs.fresh.2
        hscoped := obs.hscoped
        legal := obs.legal
        normalized := obs.normalized }

end ProgramObligations

/-- Semantic payload of a source occurrence, expressed over the final field set
of the enclosing program. -/
noncomputable def sem :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      ProgramObligations p → ProgramNode p →
      EventGraph.NodeSem P (ProgramField p) L
        (fun field => field.ty)
  | _, .letExpr x (b := b) e k, obs, .letHere =>
      let target : ProgramField (.letExpr x e k) :=
        ProgramField.writtenBy (.letHere (x := x) (e := e) (k := k))
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := x) (τ := .pub b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .assign target
        (ProgramField.castEventExpr htarget.symm
          (ProgramField.publicEventExpr (.letExpr x e k) e))
  | _, .letExpr x e k, obs, .letTail node =>
      (sem obs.letTail node).mapFields
        ProgramField.letTail (fun _ => rfl)
  | _, .sample x (b := b) D k, obs, .sampleHere =>
      let target : ProgramField (.sample x D k) :=
        ProgramField.writtenBy (.sampleHere (x := x) (D := D) (k := k))
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := x) (τ := .pub b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .sample target
        (ProgramField.castEventDist htarget.symm
          (ProgramField.publicEventDist (.sample x D k) D obs.normalized.1))
  | _, .sample x D k, obs, .sampleTail node =>
      (sem obs.sampleTail node).mapFields ProgramField.sampleTail
        (fun _ => rfl)
  | _, .commit x who (b := b) R k, obs, .commitHere =>
      let target : ProgramField (.commit x who R k) :=
        ProgramField.writtenBy (.commitHere (x := x) (who := who)
          (R := R) (k := k))
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := x) (τ := .hidden who b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .commit who target
        (ProgramField.commitEventGuard (.commit x who R k) R
          target htarget obs.hctx obs.fresh.1 obs.hscoped.1 obs.legal.1)
  | _, .commit x who R k, obs, .commitTail node =>
      (sem obs.commitTail node).mapFields ProgramField.commitTail
        (fun _ => rfl)
  | _, .reveal y who x (b := b) hx k, obs, .revealHere =>
      let source : ProgramField (.reveal y who x hx k) :=
        .revealTail (ProgramField.ofCurrent k (.mk (VHasVar.there hx)))
      let target : ProgramField (.reveal y who x hx k) :=
        ProgramField.writtenBy (.revealHere (y := y) (who := who)
          (x := x) (hx := hx) (k := k))
      have hsource : source.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (VHasVar.there hx))).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      have htarget : target.ty = b := by
        change
          (ProgramField.ofCurrent k
            (.mk (x := y) (τ := .pub b) .here)).ty = b
        rw [ProgramField.ty_ofCurrent]
        rfl
      .reveal source target (hsource.trans htarget.symm)
  | _, .reveal y who x hx k, obs, .revealTail node =>
      (sem obs.revealTail node).mapFields ProgramField.revealTail
        (fun _ => rfl)

/-- Every source node semantically writes its syntactic result field. -/
theorem writtenBy_mem_writeFields :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (obs : ProgramObligations p) → (node : ProgramNode p) →
        ProgramField.writtenBy node ∈
          (ProgramNode.sem obs node).writeFields
  | _, .letExpr x e k, obs, .letHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        EventGraph.NodeSem.writeFields, EventGraph.NodeSem.writes,
        EventGraph.FieldWrite.field]
  | _, .letExpr _ _ k, obs, .letTail node => by
      exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.letTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k) obs.letTail node)
  | _, .sample x D k, obs, .sampleHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        EventGraph.NodeSem.writeFields, EventGraph.NodeSem.writes,
        EventGraph.FieldWrite.field]
  | _, .sample _ _ k, obs, .sampleTail node => by
      exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.sampleTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k) obs.sampleTail node)
  | _, .commit x who R k, obs, .commitHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        EventGraph.NodeSem.writeFields, EventGraph.NodeSem.writes,
        EventGraph.FieldWrite.field]
  | _, .commit _ _ _ k, obs, .commitTail node => by
      exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.commitTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k) obs.commitTail node)
  | _, .reveal y who x hx k, obs, .revealHere => by
      simp [ProgramNode.sem, ProgramField.writtenBy,
        EventGraph.NodeSem.writeFields, EventGraph.NodeSem.writes,
        EventGraph.FieldWrite.field]
  | _, .reveal _ _ _ _ k, obs, .revealTail node => by
      exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
        (f := ProgramField.revealTail) (hty := fun _ => rfl)
        (writtenBy_mem_writeFields (p := k) obs.revealTail node)

/-- Every generated source node writes exactly its structural result field. -/
theorem eq_writtenBy_of_mem_writeFields
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramObligations p)
    (node : ProgramNode p) {field : ProgramField p}
    (hwrite :
      field ∈
        (ProgramNode.sem obs node).writeFields) :
    field = ProgramField.writtenBy node := by
  have hfield :=
    (EventGraph.NodeSem.mem_writeFields_iff_eq_writeTarget _ _).mp hwrite
  have hwritten :=
    (EventGraph.NodeSem.mem_writeFields_iff_eq_writeTarget _ _).mp
      (writtenBy_mem_writeFields obs node)
  exact hfield.trans hwritten.symm

/-- Membership in a generated node's write set identifies the field's
structural writer. -/
theorem writer?_eq_some_of_mem_writeFields
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramObligations p)
    (node : ProgramNode p) {field : ProgramField p}
    (hwrite :
      field ∈
        (ProgramNode.sem obs node).writeFields) :
    ProgramField.writer? field = some node := by
  have hfield :
      field = ProgramField.writtenBy node :=
    eq_writtenBy_of_mem_writeFields obs node hwrite
  subst field
  exact ProgramField.writer?_writtenBy node

/-- Source reads are causally available: a node reads either an initial current
field of the enclosing program or a field written by an earlier source node. -/
theorem read_current_or_prior_write :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (obs : ProgramObligations p) → (node : ProgramNode p) →
      {field : ProgramField p} →
      field ∈ (ProgramNode.sem obs node).reads →
        field ∈ ProgramField.currentFields p ∨
          ∃ prior : ProgramNode p,
            prior.rank < node.rank ∧
              field ∈
                (ProgramNode.sem obs prior).writeFields
  | _, .letExpr x e k, obs, .letHere, field, hread => by
      left
      simpa [ProgramNode.sem, EventGraph.NodeSem.reads,
        ProgramField.castEventExpr, ProgramField.publicEventExpr] using hread
  | _, .letExpr x e k, obs, .letTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.letTail (e := e) field).ty = field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k) obs.letTail node).mapFields
            ProgramField.letTail hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases EventGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) obs.letTail node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.letTail_currentFields_or_eq_writtenBy_letHere
            (e := e) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.letHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields obs
                  (.letHere (x := x) (e := e) (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.letTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.letTail) (hty := hty) hwrite
  | _, .sample x D k, obs, .sampleHere, field, hread => by
      left
      simpa [ProgramNode.sem, EventGraph.NodeSem.reads,
        ProgramField.castEventDist, ProgramField.publicEventDist] using hread
  | _, .sample x D k, obs, .sampleTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.sampleTail (D := D) field).ty = field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k) obs.sampleTail node).mapFields
            ProgramField.sampleTail hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases EventGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) obs.sampleTail node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.sampleTail_currentFields_or_eq_writtenBy_sampleHere
            (D := D) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.sampleHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields obs
                  (.sampleHere (x := x) (D := D) (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.sampleTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.sampleTail) (hty := hty) hwrite
  | _, .commit x who R k, obs, .commitHere, field, hread => by
      left
      simpa [ProgramNode.sem, EventGraph.NodeSem.reads,
        ProgramField.commitEventGuard] using hread
  | _, .commit x who R k, obs, .commitTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.commitTail (R := R) field).ty = field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k) obs.commitTail node).mapFields
            ProgramField.commitTail hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases EventGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) obs.commitTail node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.commitTail_currentFields_or_eq_writtenBy_commitHere
            (R := R) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.commitHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields obs
                  (.commitHere (x := x) (who := who) (R := R) (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.commitTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.commitTail) (hty := hty) hwrite
  | _, .reveal y who x hx k, obs, .revealHere, field, hread => by
      left
      have hfield :
          field = ProgramField.ofCurrent (.reveal y who x hx k) (.mk hx) := by
        simpa [ProgramNode.sem, EventGraph.NodeSem.reads] using hread
      rw [hfield]
      exact ProgramField.ofCurrent_mem_currentFields
        (.reveal y who x hx k) (.mk hx)
  | _, .reveal y who x hx k, obs, .revealTail node, field, hread => by
      let hty :
          ∀ field : ProgramField k,
            (ProgramField.revealTail (x := x) (hx := hx) field).ty =
              field.ty :=
        fun _ => rfl
      have hread' :
          field ∈ ((ProgramNode.sem (p := k) obs.revealTail node).mapFields
            ProgramField.revealTail hty).reads := by
        simpa [ProgramNode.sem] using hread
      rcases EventGraph.NodeSem.mem_reads_mapFields hread' with
        ⟨inner, rfl, hinner⟩
      have hrec :=
        read_current_or_prior_write (p := k) obs.revealTail node hinner
      rcases hrec with hcurrent | hprior
      · cases ProgramField.revealTail_currentFields_or_eq_writtenBy_revealHere
            (x := x) (hx := hx) hcurrent with
          | inl houter => exact Or.inl houter
          | inr hwriteEq =>
              right
              refine ⟨.revealHere, by simp [ProgramNode.rank], ?_⟩
              simpa [hwriteEq] using
                (writtenBy_mem_writeFields obs
                  (.revealHere (y := y) (who := who) (x := x) (hx := hx)
                    (k := k)))
      · rcases hprior with ⟨prior, hrank, hwrite⟩
        right
        refine ⟨.revealTail prior, Nat.succ_lt_succ hrank, ?_⟩
        exact EventGraph.NodeSem.mem_writeFields_mapFields_of_mem
          (f := ProgramField.revealTail) (hty := hty) hwrite

/-- Causal prerequisites of a source node.

A source node depends on earlier source nodes whose writes it reads. Source
order remains only as the acyclicity certificate: unrelated source occurrences
are allowed to share a frontier. -/
noncomputable def prereqs
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramObligations p) (node : ProgramNode p) :
    Finset (ProgramNode p) := by
  classical
  exact (finset p).filter fun prior =>
    prior.rank < node.rank ∧
      ∃ field,
        field ∈ (ProgramNode.sem obs node).reads ∧
          field ∈
            (ProgramNode.sem obs prior).writeFields

/-- The program event graph's prerequisites are exactly the causal read dependencies:
if a node reads a field written by another source node, that writer is a
prerequisite of the reader. -/
theorem writer_mem_prereqs_of_read_write
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramObligations p)
    {reader writer : ProgramNode p} {field : ProgramField p}
    (hread :
      field ∈
        (ProgramNode.sem obs reader).reads)
    (hwrite :
      field ∈
        (ProgramNode.sem obs writer).writeFields) :
    writer ∈
      ProgramNode.prereqs obs reader := by
  classical
  rcases ProgramNode.read_current_or_prior_write
      obs reader hread with
    hcurrent | hprior
  · have hnone :
        ProgramField.writer? field = none :=
      ProgramField.writer?_eq_none_of_mem_currentFields hcurrent
    have hsome :
        ProgramField.writer? field = some writer :=
      ProgramNode.writer?_eq_some_of_mem_writeFields obs writer hwrite
    rw [hsome] at hnone
    simp at hnone
  · rcases hprior with ⟨prior, hrank, hpriorWrite⟩
    have hpriorWriter :
        ProgramField.writer? field = some prior :=
      ProgramNode.writer?_eq_some_of_mem_writeFields obs prior hpriorWrite
    have hwriterWriter :
        ProgramField.writer? field = some writer :=
      ProgramNode.writer?_eq_some_of_mem_writeFields obs writer hwrite
    have hwriter_eq : writer = prior := by
      rw [hwriterWriter] at hpriorWriter
      exact Option.some.inj hpriorWriter
    subst writer
    exact Finset.mem_filter.mpr
      ⟨ProgramNode.mem_finset p prior, hrank, ⟨field, hread, hpriorWrite⟩⟩

/-- A program event graph slice is well-formed for a node when it has the storage
shape prescribed by the node semantics. Dynamic guard checks are handled by
`actionLegal`. -/
noncomputable def sliceLegal
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramObligations p)
    (node : ProgramNode p) (slice : ProgramField.WriteSlice p) : Prop :=
  match sem obs node with
  | .assign field _ =>
      ∃ value : L.Val field.ty,
        slice = ProgramField.singleSlice field (.clear value)
  | .sample field _ =>
      ∃ value : L.Val field.ty,
        slice = ProgramField.singleSlice field (.clear value)
  | .commit _ field _ =>
      ∃ value : L.Val field.ty,
        slice = ProgramField.singleSlice field (.hidden value)
  | .reveal _ target _ =>
      ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value)

/-- A legal slice contains a stored value for every semantic field written by
the node. -/
theorem sliceLegal_writeField_isSome
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramObligations p)
    (node : ProgramNode p) {slice : ProgramField.WriteSlice p}
    {field : ProgramField p}
    (hlegal : sliceLegal obs node slice)
    (hwrite :
      field ∈
        (ProgramNode.sem obs node).writeFields) :
    ∃ stored : EventGraph.StoredValue (L.Val field.ty),
      slice field = some stored := by
  classical
  cases hsem : ProgramNode.sem obs node with
  | assign target expr =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value) at hlegal
      rw [EventGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = EventGraph.FieldWrite.clear target := by
        simpa [EventGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [EventGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.clear value, by simp⟩
  | sample target dist =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value) at hlegal
      rw [EventGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = EventGraph.FieldWrite.clear target := by
        simpa [EventGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [EventGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.clear value, by simp⟩
  | commit owner target guard =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.hidden value) at hlegal
      rw [EventGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = EventGraph.FieldWrite.hidden owner target := by
        simpa [EventGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [EventGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.hidden value, by simp⟩
  | reveal source target hty =>
      rw [sliceLegal, hsem] at hlegal
      change ∃ value : L.Val target.ty,
        slice = ProgramField.singleSlice target (.clear value) at hlegal
      rw [EventGraph.NodeSem.mem_writeFields_iff] at hwrite
      rcases hwrite with ⟨write, hwrite, hfield⟩
      rw [hsem] at hwrite
      have hwrite_eq :
          write = EventGraph.FieldWrite.clear target := by
        simpa [EventGraph.NodeSem.writes] using hwrite
      subst write
      dsimp [EventGraph.FieldWrite.field] at hfield
      symm at hfield
      subst field
      rcases hlegal with ⟨value, rfl⟩
      exact ⟨.clear value, by simp⟩

/-- Dynamic legality for player-chosen program event graph slices. Only commit nodes
have an actor, so only commits admit legal player slices. -/
noncomputable def actionLegal
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (obs : ProgramObligations p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p))
    (node : ProgramNode p) (slice : ProgramField.WriteSlice p) : Prop :=
  match sem obs node with
  | .assign _ _ => False
  | .sample _ _ => False
  | .commit _ field guard =>
      ∃ available :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? env result read).isSome,
        ∃ value : L.Val field.ty,
          guard.eval value
              (ProgramField.readEnvOfResult env result guard.reads available) =
            true ∧
          slice = ProgramField.singleSlice field (.hidden value)
  | .reveal _ _ _ => False

/-- If the declared reads of a player-owned node are available, then that
node has a legal concrete graph action. -/
theorem exists_actionLegal_of_reads_available
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (obs : ProgramObligations p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p))
    (node : ProgramNode p) {who : P}
    (hactor :
      (sem obs node).actor = some who)
    (hreads :
      ∀ read, read ∈
        (sem obs node).reads →
        (ProgramField.value? env result read).isSome) :
    ∃ slice,
      sliceLegal obs node slice ∧
        actionLegal env obs result node slice := by
  cases hsem : sem obs node with
  | assign field expr =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | sample field dist =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | reveal source target hty =>
      simp [EventGraph.NodeSem.actor, hsem] at hactor
  | commit owner field guard =>
      have havailable :
          ∀ read, read ∈ guard.reads →
            (ProgramField.value? env result read).isSome := by
        intro read hread
        exact hreads read (by simpa [EventGraph.NodeSem.reads, hsem] using hread)
      let ρ :=
        ProgramField.readEnvOfResult env result guard.reads havailable
      rcases guard.satisfiable ρ with ⟨value, hvalue⟩
      let slice := ProgramField.singleSlice field (.hidden value)
      refine ⟨slice, ?_, ?_⟩
      · rw [sliceLegal, hsem]
        exact ⟨value, rfl⟩
      · rw [actionLegal, hsem]
        exact ⟨havailable, value, hvalue, rfl⟩

/-- Visible reads of a generated commit guard are exactly fields visible to the
committing player.  This is the bridge from event-graph-local guard invariance to
the FOSG player's private observation. -/
theorem guard_visibleReads_owner_of_sem_commit :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (obs : ProgramObligations p) →
      (node : ProgramNode p) →
      {commitWho : P} → {target : ProgramField p} →
      {guard : EventGraph.EventGuard L (ProgramField p)
        (fun field => field.ty) target} →
      sem obs node =
        .commit commitWho target guard →
      ∀ read, read ∈ guard.visibleReads →
        read.VisibleTo commitWho
  | _, .letExpr x e k, obs, .letHere, _, _, _, hsem => by
      simp [sem] at hsem
  | _, .letExpr x e k, obs, .letTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem obs.letTail node with
      | assign field expr =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.letTail innerTarget)
                  (innerGuard.mapFields ProgramField.letTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, EventGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) obs.letTail node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner
  | _, .sample x D k, obs, .sampleHere, _, _, _, hsem => by
      simp [sem] at hsem
  | _, .sample x D k, obs, .sampleTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem obs.sampleTail node with
      | assign field expr =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.sampleTail innerTarget)
                  (innerGuard.mapFields ProgramField.sampleTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, EventGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) obs.sampleTail node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner
  | _, .commit x who R k, obs, .commitHere, commitWho, target, guard, hsem => by
      intro read hread
      have hsem' := by
        simpa [sem, ProgramField.commitEventGuard] using hsem
      rcases hsem' with ⟨howner, htarget, hguard⟩
      subst commitWho
      subst target
      cases hguard
      exact (Finset.mem_filter.mp hread).2
  | _, .commit x who R k, obs, .commitTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem obs.commitTail node with
      | assign field expr =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.commitTail innerTarget)
                  (innerGuard.mapFields ProgramField.commitTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, EventGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) obs.commitTail node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner
  | _, .reveal y who x hx k, obs, .revealHere, _, _, _, hsem => by
      simp [sem] at hsem
  | _, .reveal y who x hx k, obs, .revealTail node, commitWho, target, guard, hsem => by
      cases hinner :
          sem obs.revealTail node with
      | assign field expr =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.revealTail innerTarget)
                  (innerGuard.mapFields ProgramField.revealTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [sem, hinner, EventGraph.NodeSem.mapFields] using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          intro read hread
          rcases Finset.mem_image.mp hread with
            ⟨innerRead, hinnerRead, rfl⟩
          have howner :=
            guard_visibleReads_owner_of_sem_commit
              (p := k) obs.revealTail node hinner innerRead hinnerRead
          simpa [ProgramField.owner] using howner

/-- A completed source node makes every field it semantically writes available
in the source-level extensional value lookup. -/
theorem value?_isSome_of_completed_write
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (obs : ProgramObligations p)
    {result : ProgramNode p → Option (ProgramField.WriteSlice p)}
    {writer : ProgramNode p} {field : ProgramField p}
    (hdone : (result writer).isSome)
    (hcfgLegal :
      ∀ {node slice},
        result node = some slice →
          ProgramNode.sliceLegal obs node slice)
    (hwrite :
      field ∈
        (ProgramNode.sem obs writer).writeFields) :
    (ProgramField.value? env result field).isSome := by
  rcases Option.isSome_iff_exists.mp hdone with ⟨slice, hresult⟩
  have hsliceLegal :
      ProgramNode.sliceLegal obs writer slice :=
    hcfgLegal hresult
  rcases ProgramNode.sliceLegal_writeField_isSome obs writer hsliceLegal hwrite with
    ⟨stored, hstored⟩
  have hfield :
      field = ProgramField.writtenBy writer :=
    ProgramNode.eq_writtenBy_of_mem_writeFields obs writer hwrite
  subst field
  exact ProgramField.value?_isSome_of_result_slice env
    (ProgramField.writer?_writtenBy writer) hresult hstored

/-- Internal kernel for source event nodes. Assignment and reveal nodes are
deterministic; sample nodes use the checked PMF distribution; commit nodes are
not internal. -/
noncomputable def internalKernel
    {Γ : VCtx P L} {p : VegasCore P L Γ} (env : VEnv L Γ)
    (obs : ProgramObligations p)
    (node : ProgramNode p)
    (result : ProgramNode p → Option (ProgramField.WriteSlice p)) :
    PMF (ProgramField.WriteSlice p) := by
  classical
  exact
    match hsem : sem obs node with
    | .assign field expr =>
        if available :
            ∀ read, read ∈ expr.reads →
              (ProgramField.value? env result read).isSome then
          PMF.pure
            (ProgramField.singleSlice field
              (.clear (expr.eval
                (ProgramField.readEnvOfResult env result expr.reads available))))
        else
          PMF.pure (ProgramField.emptySlice p)
    | .sample field dist =>
        if available :
            ∀ read, read ∈ dist.reads →
              (ProgramField.value? env result read).isSome then
          PMF.map
            (fun value => ProgramField.singleSlice field (.clear value))
            (dist.eval
              (ProgramField.readEnvOfResult env result dist.reads available))
        else
          PMF.pure (ProgramField.emptySlice p)
    | .commit _ _ _ =>
        PMF.pure (ProgramField.emptySlice p)
    | .reveal source target hty =>
        if available :
            ∀ read, read ∈ ({source} : Finset (ProgramField p)) →
              (ProgramField.value? env result read).isSome then
          let ρ :=
            ProgramField.readEnvOfResult env result
              ({source} : Finset (ProgramField p)) available
          PMF.pure
            (ProgramField.singleSlice target
              (.clear (cast (by rw [hty]) (ρ.value source (by simp)))))
        else
          PMF.pure (ProgramField.emptySlice p)

end ProgramNode

namespace WFProgram

def obligations (g : WFProgram P L) :
    ProgramNode.ProgramObligations g.prog where
  hctx := g.wctx
  fresh := g.wf.1
  hscoped := g.wf.2.2
  legal := g.legal
  normalized := g.normalized

end WFProgram

end Vegas
