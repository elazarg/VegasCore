/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.GraphLayout

/-! # Compilation to typed immutable graphs

Every source operation has one graph operation. Binding introduces a private
immutable field; resolution introduces a separate public result field. The
compiler specializes retained guards to public fields and literal pending
statuses at each resolution. The graph contains code and typed references,
not a source interpreter or a dynamic source guard registry.
-/

noncomputable section
namespace Vegas.SourceProgram

open Interaction GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [R : IExpr.ResultTypes L]

omit [DecidableEq Player] in
@[simp] theorem graphCtx_names (Γ : SourceCtx Player L) :
    (graphCtx (R := R) Γ).map Prod.fst = Γ.map Prod.fst := by
  induction Γ with
  | nil => rfl
  | cons entry rest ih =>
      rcases entry with ⟨name, cell⟩
      cases cell <;> simp [graphCtx, ih]

/-- Public source expressions retain their schema; this mapping gives each
schema variable a typed immutable graph field. -/
def publicField : {Γ : SourceCtx Player L} → {name : VarId} → {τ : L.Ty} →
    HasVar (SourcePublicCtx L Γ) name τ → Graph.PublicRead (L := L) (graphCtx Γ) τ
  | (_, .publicData _) :: _, _, _, .here => ⟨_, .here⟩
  | (_, .publicData _) :: tail, _, _, .there h =>
      ⟨(publicField (Γ := tail) h).field, .there (publicField (Γ := tail) h).ref⟩
  | (_, .privateData _ _) :: tail, _, _, h =>
      ⟨(publicField (Γ := tail) h).field, .there (publicField (Γ := tail) h).ref⟩
  | (_, .publication _) :: _, _, _, .here => ⟨_, .here⟩
  | (_, .publication _) :: tail, _, _, .there h =>
      ⟨(publicField (Γ := tail) h).field, .there (publicField (Γ := tail) h).ref⟩

def compilePublicExpr {Γ : SourceCtx Player L} {τ : L.Ty}
    (expression : L.Expr (SourcePublicCtx L Γ) τ) :
    Graph.PublicExpr (L := L) (graphCtx Γ) τ where
  schema := SourcePublicCtx L Γ
  code := expression
  reads := publicField

def compilePublicDist {Γ : SourceCtx Player L} {τ : L.Ty}
    (law : L.DistExpr (SourcePublicCtx L Γ) τ) :
    Graph.PublicDist (L := L) (graphCtx Γ) τ where
  schema := SourcePublicCtx L Γ
  code := law
  reads := publicField

/-- Guard inputs refer only to public results, ordinary public fields, or a
literal pending status. Private candidates are never guard operands. -/
def compileGuardRead {Γ : SourceCtx Player L} {owner : Player} {τ : L.Ty}
    (map : PublicationMap (R := R) Γ) :
    SourceGuardRead Γ owner τ → Graph.GuardRead (R := R) (graphCtx Γ) τ
  | .publicData h => .publicData (fieldRef h)
  | .privateData h => map h
  | .publication h => .publication (fieldRef h)

omit [DecidableEq Player] in
@[simp] theorem compileGuardRead_get {Γ : SourceCtx Player L} {owner : Player}
    {τ : L.Ty} (map : PublicationMap (R := R) Γ) (read : SourceGuardRead Γ owner τ)
    (env : VEnv L (graphCtx Γ)) :
    (compileGuardRead map read).get env = read.get (decodeState map env) := by
  cases read with
  | publicData => rfl
  | privateData => rfl
  | publication h =>
      simp only [compileGuardRead, Graph.GuardRead.get, SourceGuardRead.get,
        decodeState_publication]
      generalize R.valueEquiv _ (env.get (fieldRef h)) = result
      cases result <;> rfl

def compileGuard {Γ : SourceCtx Player L} (map : PublicationMap (R := R) Γ)
    (obligation : Obligation (Player := Player) (L := L) Γ) :
    Graph.GuardCheck (R := R) (graphCtx Γ) where
  subject := obligation.subject
  payload := obligation.payload
  code := obligation.guard.toDeferredGuardCode
  subjectRead := map obligation.source
  reads := fun h => compileGuardRead map (obligation.guard.reads h)

omit [DecidableEq Player] in
@[simp] theorem compileGuard_eval {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ)
    (obligation : Obligation (Player := Player) (L := L) Γ)
    (env : VEnv L (graphCtx Γ)) :
    (compileGuard map obligation).eval env = obligation.check (decodeState map env) := by
  simp only [compileGuard, Graph.GuardCheck.eval, Obligation.check, SourceGuard.check,
    compileGuardRead_get, decodeState_privateData]

omit [DecidableEq Player] in
@[simp] theorem compileGuards_accept {Γ : SourceCtx Player L}
    (map : PublicationMap (R := R) Γ) (registry : Registry Γ)
    (env : VEnv L (graphCtx Γ)) :
    Graph.checksAccepted (registry.map (compileGuard map)) env =
      registry.ok (decodeState map env) := by
  simp [Graph.checksAccepted, Registry.ok, List.all_map, Function.comp_def]

/-- Full source lowering. Guard registration is compiler state; its
specialized code is emitted at each atomic resolution. -/
def compileGraph : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (unique : (Γ.map Prod.fst).Nodup) → PublicationMap (R := R) Γ → Registry Γ →
    Graph Player L (graphCtx Γ) (graphCtx program.terminalCtx)
  | _, _, .ret payoffs, _, _, _ =>
      .ret (payoffs.map fun payoff => (payoff.1, compilePublicExpr payoff.2))
  | _, _, .sample name fresh law next, unique, map, registry =>
      .sample name (by simpa using fresh) (compilePublicDist law)
        (compileGraph next (by simp [fresh, unique]) (weakenMap map) registry.weaken)
  | _, _, .commit name owner fresh guard next, unique, map, registry =>
      let obligation : Obligation _ :=
        { owner := owner, subject := name, payload := _, source := .here,
          guard := guard.weaken }
      .bind name owner (by simpa using fresh)
        (compileGraph next (by simp [fresh, unique]) (weakenMap map)
          (obligation :: registry.weaken))
  | _, _, .reveal published owner name fresh source _ next, unique, map, registry =>
      let nextMap : PublicationMap (R := R)
          ((published, .publication _) :: _) :=
        resolveMap map unique source (published := published)
      .resolve published owner name (by simpa using fresh) (fieldRef source)
        (registry.weaken.map (compileGuard nextMap))
        (compileGraph next (by simp [fresh, unique]) nextMap registry.weaken)

/-- The final publication references retained for outcome decoding. -/
def terminalMap : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) →
    (unique : (Γ.map Prod.fst).Nodup) → PublicationMap (R := R) Γ →
    PublicationMap (R := R) program.terminalCtx
  | _, _, .ret _, _, map => map
  | _, _, .sample _ fresh _ next, unique, map =>
      terminalMap next (by simp [fresh, unique]) (weakenMap map)
  | _, _, .commit _ _ fresh _ next, unique, map =>
      terminalMap next (by simp [fresh, unique]) (weakenMap map)
  | _, _, .reveal published _ _ fresh source _ next, unique, map =>
      terminalMap next (by simp [fresh, unique])
        (resolveMap map unique source (published := published))

def Initial.graph (source : Initial (Player := Player) (L := L)) :
    Graph Player L (graphCtx source.context) (graphCtx source.program.terminalCtx) :=
  compileGraph source.program source.namesNodup initialMap []

def Initial.graphInputs (source : Initial (Player := Player) (L := L)) :
    VEnv L (graphCtx source.context) := encodeState source.state

def Initial.decodeGraph (source : Initial (Player := Player) (L := L)) :
    VEnv L (graphCtx source.program.terminalCtx) → State L source.program.terminalCtx :=
  decodeState (terminalMap source.program source.namesNodup initialMap)

end Vegas.SourceProgram
