import Vegas.FOSG.Observed.Pure

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed

/-!
## Current-observation Kuhn model

The reachable FOSG theorem indexes behavioral strategies by full player-event
histories. The total Vegas strategy space is indexed by the current program
cursor and current player view. This file starts the direct bridge: an
`ObsModelCore` whose information state is exactly the current private
observation and whose local actions are optional program moves legal at every
cursor world with that private observation.
-/

/-- Optional program moves that are legal for every cursor world matching the
given current private observation. This is the local action carrier for the
current-observation Kuhn model. -/
abbrev CurrentProgramMove
    (g : WFProgram P L) (who : P) (priv : PrivateObs g who) : Type :=
  { oi : Option (ProgramAction g.prog who) //
    ∀ w : CursorCheckedWorld g,
      privateObsOfCursorWorld who w = priv →
        oi ∈ CursorCheckedWorld.availableProgramMovesAt
          w.1.prog w.1.env w.1.suffix who }

/-- Cursor-local value move for the current-observation model.

At an owned commit observation this is the committed value, restricted to
values whose guard is forced by the current player view. At inactive
observations the action type is `PUnit`. This is the strategy-facing action
carrier; `ProgramAction` is reconstructed only at concrete worlds. -/
@[reducible] noncomputable def CurrentValueMove
    (g : WFProgram P L) (who : P) (priv : PrivateObs g who) : Type :=
  match priv.cursor.prog with
  | VegasCore.commit _x owner (b := b) R _k =>
      if owner = who then
        {v : L.Val b // ∀ ρ : Env L.Val (eraseVCtx priv.cursor.Γ),
          projectViewEnv who ρ = VEnv.eraseEnv priv.env →
            evalGuard (Player := P) (L := L) R v ρ = true}
      else PUnit
  | _ => PUnit

namespace CurrentValueMove

@[reducible] noncomputable def instFintype
    (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (priv : PrivateObs g who) :
    Fintype (CurrentValueMove g who priv) := by
  classical
  letI : ∀ τ : L.Ty, Fintype (L.Val τ) :=
    fun τ => FiniteValuation.instFintypeVal L LF τ
  unfold CurrentValueMove
  cases hprog : priv.cursor.prog with
  | ret payoffs => infer_instance
  | letExpr x e k => infer_instance
  | sample x D k => infer_instance
  | reveal y owner x hx k => infer_instance
  | commit x owner R k =>
      by_cases howner : owner = who
      · simp only [howner, ↓reduceIte]
        exact Fintype.ofFinite
          {v : L.Val _ // ∀ ρ : Env L.Val (eraseVCtx priv.cursor.Γ),
            projectViewEnv who ρ = VEnv.eraseEnv priv.env →
              evalGuard (Player := P) (L := L) R v ρ = true}
      · simp only [howner, ↓reduceIte]
        exact inferInstanceAs (Fintype PUnit)

/-- Reconstruct the concrete program-local action at a concrete world. -/
noncomputable def toProgramMoveAtWorld
    {g : WFProgram P L} (w : CursorCheckedWorld g) (who : P)
    (m : CurrentValueMove g who (privateObsOfCursorWorld who w)) :
    Option (ProgramAction g.prog who) :=
  match hprog : w.1.cursor.prog with
  | .ret _ => none
  | .letExpr _ _ _ => none
  | .sample _ _ _ => none
  | .reveal _ _ _ _ _ => none
  | .commit x owner R k =>
      if howner : owner = who then
        by
          cases howner
          let mv :
              {v : L.Val _ //
                ∀ ρ : Env L.Val (eraseVCtx w.1.cursor.Γ),
                  projectViewEnv who ρ =
                      VEnv.eraseEnv (VEnv.toView who w.1.env) →
                    evalGuard (Player := P) (L := L) R v ρ = true} := by
            dsimp [CurrentValueMove, privateObsOfCursorWorld] at m
            rw [hprog] at m
            simpa only [if_pos rfl] using m
          exact some
            (ProgramAction.commitAt
              (by
                rw [← hprog]
                exact w.1.suffix)
              mv.1)
      else none

theorem toProgramMoveAtWorld_available
    {g : WFProgram P L} (w : CursorCheckedWorld g) (who : P)
    (m : CurrentValueMove g who (privateObsOfCursorWorld who w)) :
    toProgramMoveAtWorld w who m ∈
      CursorCheckedWorld.availableProgramMovesAt
        w.1.prog w.1.env w.1.suffix who := by
  unfold toProgramMoveAtWorld
  split
  · rename_i payoffs hprog
    simp [CursorCheckedWorld.availableProgramMovesAt,
      CursorWorldData.prog, hprog, active]
  · rename_i x b e k hprog
    simp [CursorCheckedWorld.availableProgramMovesAt,
      CursorWorldData.prog, hprog, active]
  · rename_i x b D k hprog
    simp [CursorCheckedWorld.availableProgramMovesAt,
      CursorWorldData.prog, hprog, active]
  · rename_i y owner x b hx k hprog
    simp [CursorCheckedWorld.availableProgramMovesAt,
      CursorWorldData.prog, hprog, active]
  · rename_i x owner b R k hprog
    split
    · rename_i howner
      cases howner
      let suffix : ProgramSuffix g.prog (VegasCore.commit x who R k) := by
        rw [← hprog]
        exact w.1.suffix
      let mv :
          {v : L.Val _ //
            ∀ ρ : Env L.Val (eraseVCtx w.1.cursor.Γ),
              projectViewEnv who ρ =
                  VEnv.eraseEnv (VEnv.toView who w.1.env) →
                evalGuard (Player := P) (L := L) R v ρ = true} := by
        dsimp [CurrentValueMove, privateObsOfCursorWorld] at m
        rw [hprog] at m
        simpa only [if_pos rfl] using m
      have hguard :
          evalGuard (Player := P) (L := L) R mv.1
            (VEnv.eraseEnv w.1.env) = true := by
        exact mv.2 (VEnv.eraseEnv w.1.env)
          ((privateObsOfCursorWorld_eraseEnv (g := g) who w).symm)
      have hai :
          ProgramAction.commitAt suffix mv.1 ∈
            CursorCheckedWorld.availableProgramActionsAt
              (VegasCore.commit x who R k) w.1.env suffix who := by
        rw [CursorCheckedWorld.availableProgramActionsAt_commit_owner_iff]
        exact ⟨mv.1, rfl, hguard⟩
      have hai' :
          ProgramAction.commitAt suffix mv.1 ∈
            CursorCheckedWorld.availableProgramActionsAt
              w.1.cursor.prog w.1.env w.1.suffix who := by
        constructor
        · have hbroad := hai.1
          simpa [FOSGBridge.availableActions, hprog] using hbroad
        · exact ⟨x, who, _, R, k, hprog, rfl, rfl⟩
      simpa [CursorCheckedWorld.availableProgramMovesAt,
        CursorWorldData.prog, hprog, active, suffix, mv] using
          (⟨by simp [active, hprog], hai'⟩ :
            some (ProgramAction.commitAt suffix mv.1) ∈
              CursorCheckedWorld.availableProgramMovesAt
                w.1.cursor.prog w.1.env w.1.suffix who)
    · rename_i howner
      simpa [CursorCheckedWorld.availableProgramMovesAt,
        CursorWorldData.prog, hprog, active] using
          (fun h : who = owner => howner h.symm)

/-- Repackage a value move as the proof-carrying optional program move used by
the checked cursor transition. -/
noncomputable def toCurrentProgramMove
    {g : WFProgram P L} (w : CursorCheckedWorld g) (who : P)
    (m : CurrentValueMove g who (privateObsOfCursorWorld who w)) :
    CurrentProgramMove g who (privateObsOfCursorWorld who w) :=
  ⟨toProgramMoveAtWorld w who m, by
    intro w' hpriv
    have hsets :=
      availableProgramMovesAt_eq_of_privateObs_eq
        g who w' w hpriv
    rw [hsets]
    exact toProgramMoveAtWorld_available w who m⟩

/-- A legal pure Vegas strategy gives a canonical current-value move. -/
noncomputable def ofPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (priv : PrivateObs g who) : CurrentValueMove g who priv := by
  unfold CurrentValueMove
  cases hprog : priv.cursor.prog with
  | ret payoffs => exact PUnit.unit
  | letExpr x e k => exact PUnit.unit
  | sample x D k => exact PUnit.unit
  | reveal y owner x hx k => exact PUnit.unit
  | commit x owner R k =>
      dsimp
      by_cases howner : owner = who
      · cases howner
        rw [if_pos rfl]
        let suffix : ProgramSuffix g.prog (.commit x who R k) := by
          rw [← hprog]
          exact priv.cursor.toSuffix
        refine ⟨(ProgramPureStrategy.headKernel
          (ProgramSuffix.pureStrategy suffix who σ.val))
          (VEnv.eraseEnv priv.env), ?_⟩
        intro ρ hview
        have hlegal := headPureStrategyKernel_legal_atCursor
          g hctx σ suffix ρ
        simpa [hview] using hlegal
      · rw [if_neg howner]
        exact PUnit.unit

/-- At inactive observations the value-indexed local action type carries no
strategic choice. -/
theorem subsingleton_of_not_active
    {g : WFProgram P L} {who : P} (w : CursorCheckedWorld g)
    (hnot : who ∉ CursorCheckedWorld.active w) :
    Subsingleton
      (CurrentValueMove g who (privateObsOfCursorWorld who w)) := by
  unfold CurrentValueMove privateObsOfCursorWorld
  cases hprog : w.1.cursor.prog with
  | ret payoffs =>
      infer_instance
  | letExpr x e k =>
      infer_instance
  | sample x D k =>
      infer_instance
  | reveal y owner x hx k =>
      infer_instance
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        have hactive := cursor_active_eq_singleton_of_commit (w := w) hprog
        exact False.elim (hnot (by simp [hactive]))
      · simpa only [howner, ↓reduceIte] using
          (show Subsingleton PUnit from
            ⟨fun a b => by cases a; cases b; rfl⟩)

end CurrentValueMove

namespace ProgramSuffix

/-- Following a suffix through a fresh program preserves the SSA context
invariant at the suffix endpoint. -/
def wctx
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    WFCtx Γ₀ → FreshBindings root → WFCtx Γ := by
  induction s with
  | here =>
      intro hctx _hfresh
      exact hctx
  | letExpr s ih =>
      intro hctx hfresh
      exact WFCtx.cons (s.fresh hfresh).1 (ih hctx hfresh)
  | sample s ih =>
      intro hctx hfresh
      exact WFCtx.cons (s.fresh hfresh).1 (ih hctx hfresh)
  | commit s ih =>
      intro hctx hfresh
      exact WFCtx.cons (s.fresh hfresh).1 (ih hctx hfresh)
  | reveal s ih =>
      intro hctx hfresh
      exact WFCtx.cons (s.fresh hfresh).1 (ih hctx hfresh)

end ProgramSuffix

namespace ProgramCursor

/-- A cursor endpoint of a `WFProgram` inherits all local obligations needed by
the cursor transition machine. -/
def endpointValid
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (c : ProgramCursor g.prog) : c.EndpointValid :=
  ⟨ProgramSuffix.wctx c.toSuffix hctx g.wf.1,
    c.toSuffix.fresh g.wf.1,
    c.toSuffix.viewScoped g.wf.2.2,
    c.toSuffix.normalized g.normalized,
    c.toSuffix.legal g.legal⟩

end ProgramCursor

/-- Rebuild a visibility-annotated environment from its erased version.

The operation is used only for player views: current-observation strategies are
indexed by `PrivateObs`, while ordinary Vegas behavioral kernels are indexed by
the erased `ViewEnv`. -/
def VEnv.ofErased {Γ : VCtx P L}
    (env : Env L.Val (eraseVCtx Γ)) : VEnv L Γ :=
  fun x τ h => env x τ.base h.toErased

omit [DecidableEq P] in
theorem VEnv.eraseEnv_ofErased {Γ : VCtx P L}
    (hctx : WFCtx Γ) (env : Env L.Val (eraseVCtx Γ)) :
    VEnv.eraseEnv (Player := P) (L := L) (VEnv.ofErased env : VEnv L Γ) =
      env := by
  induction Γ with
  | nil =>
      funext x τ h
      cases h
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      funext x τ h
      cases h with
      | here => rfl
      | there htail =>
          have htailCtx : WFCtx tl := WFCtx.tail hctx
          have hrec := ih htailCtx (fun x τ h => env x τ (.there h))
          exact congrFun (congrFun (congrFun hrec x) τ) htail

omit [DecidableEq P] in
theorem VEnv.eq_of_eraseEnv_eq {Γ : VCtx P L}
    {env₁ env₂ : VEnv L Γ}
    (h : VEnv.eraseEnv (Player := P) (L := L) env₁ =
      VEnv.eraseEnv (Player := P) (L := L) env₂) :
    env₁ = env₂ := by
  funext x τ hx
  have hget := congrFun (congrFun (congrFun h x) τ.base) hx.toErased
  simpa [VEnv.eraseEnv_get_of_erased] using hget

theorem VEnv.toView_cons_hidden_self_head_eq {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {v₁ v₂ : L.Val b} {env₁ env₂ : VEnv L Γ}
    (hctx : WFCtx ((x, .hidden who b) :: Γ))
    (h : VEnv.toView who
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who b) v₁ env₁) =
      VEnv.toView who
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who b) v₂ env₂)) :
    v₁ = v₂ := by
  have hproj :
      projectViewEnv who
          (VEnv.eraseEnv (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who b) v₁ env₁)) =
        projectViewEnv who
          (VEnv.eraseEnv (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who b) v₂ env₂)) := by
    simpa [projectViewEnv_eraseEnv_eq_toView (who := who) hctx]
      using congrArg VEnv.eraseEnv h
  exact projectViewEnv_cons_head_eq (who := who) (Γ := Γ)
    (x := x) (τ := .hidden who b) (hnodup := hctx)
    (hsee := by simp [canSee]) hproj

theorem VEnv.toView_cons_hidden_self_tail_eq {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {v₁ v₂ : L.Val b} {env₁ env₂ : VEnv L Γ}
    (hctx : WFCtx ((x, .hidden who b) :: Γ))
    (h : VEnv.toView who
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who b) v₁ env₁) =
      VEnv.toView who
        (VEnv.cons (Player := P) (L := L) (x := x)
          (τ := .hidden who b) v₂ env₂)) :
    VEnv.toView who env₁ = VEnv.toView who env₂ := by
  apply VEnv.eq_of_eraseEnv_eq (P := P)
  rw [← projectViewEnv_eraseEnv_eq_toView
      (who := who) (WFCtx.tail hctx) env₁]
  rw [← projectViewEnv_eraseEnv_eq_toView
      (who := who) (WFCtx.tail hctx) env₂]
  have hproj :
      projectViewEnv who
          (VEnv.eraseEnv (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who b) v₁ env₁)) =
        projectViewEnv who
          (VEnv.eraseEnv (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who b) v₂ env₂)) := by
    simpa [projectViewEnv_eraseEnv_eq_toView (who := who) hctx]
      using congrArg VEnv.eraseEnv h
  exact projectViewEnv_cons_eq (hnodup := hctx) hproj

theorem VEnv.toView_ofErased_projectViewEnv {Γ : VCtx P L}
    (hctx : WFCtx Γ) (who : P) (env : Env L.Val (eraseVCtx Γ)) :
    VEnv.toView who (VEnv.ofErased env : VEnv L Γ) =
      (VEnv.ofErased (projectViewEnv who env) :
        VEnv L (viewVCtx who Γ)) := by
  apply VEnv.eq_of_eraseEnv_eq (P := P)
  rw [← projectViewEnv_eraseEnv_eq_toView
      (who := who) hctx (VEnv.ofErased env)]
  rw [VEnv.eraseEnv_ofErased (P := P) hctx env]
  rw [VEnv.eraseEnv_ofErased (P := P) (WFCtx.viewVCtx (p := who) hctx)
    (projectViewEnv who env)]

theorem projectViewEnv_cast_ctx
    {Γ Γ' : VCtx P L} (who : P) (h : Γ = Γ')
    (env : Env L.Val (eraseVCtx Γ')) :
    projectViewEnv who
        (cast (congrArg (fun Δ => Env L.Val (eraseVCtx Δ)) h.symm) env) =
      cast
        (congrArg (fun Δ => Env L.Val (eraseVCtx (viewVCtx who Δ))) h.symm)
        (projectViewEnv who env) := by
  cases h
  rfl

omit [DecidableEq P] in
theorem VEnv.ofErased_cast_ctx
    {Γ Γ' : VCtx P L} (h : Γ = Γ')
    (env : Env L.Val (eraseVCtx Γ')) :
    (VEnv.ofErased
        (cast (congrArg (fun Δ => Env L.Val (eraseVCtx Δ)) h.symm) env) :
      VEnv L Γ) =
      cast (congrArg (fun Δ => VEnv L Δ) h.symm)
        (VEnv.ofErased env : VEnv L Γ') := by
  cases h
  rfl

/-- Current private observation reconstructed from an ordinary erased Vegas
view at a known program cursor. -/
def privateObsOfViewAtCursor
    {g : WFProgram P L} (who : P) (c : ProgramCursor g.prog)
    (view : ViewEnv who c.Γ) : PrivateObs g who where
  cursor := c
  env := VEnv.ofErased view

@[simp] theorem privateObsOfViewAtCursor_eraseEnv
    {g : WFProgram P L} (who : P) (c : ProgramCursor g.prog)
    (hctx : WFCtx c.Γ) (view : ViewEnv who c.Γ) :
    VEnv.eraseEnv (Player := P) (L := L)
        (privateObsOfViewAtCursor who c view).env =
      view :=
  VEnv.eraseEnv_ofErased (P := P) (WFCtx.viewVCtx (p := who) hctx) view

theorem privateObsOfCursorWorld_ofErased
    {g : WFProgram P L} (hctx : WFCtx g.Γ)
    (who : P) (c : ProgramCursor g.prog)
    (env : Env L.Val (eraseVCtx c.Γ)) :
    privateObsOfCursorWorld who
        (⟨{ cursor := c, env := VEnv.ofErased env },
          ProgramCursor.endpointValid g hctx c⟩ : CursorCheckedWorld g) =
      privateObsOfViewAtCursor who c (projectViewEnv who env) := by
  change
    ({ cursor := c
       env := VEnv.toView who (VEnv.ofErased env : VEnv L c.Γ) } :
        PrivateObs g who) =
      { cursor := c
        env := VEnv.ofErased (projectViewEnv who env) }
  congr
  exact VEnv.toView_ofErased_projectViewEnv
    (ProgramSuffix.wctx c.toSuffix hctx g.wf.1) who env

namespace CurrentProgramMove

@[simp] theorem val_mk
    {g : WFProgram P L} {who : P} {priv : PrivateObs g who}
    (oi : Option (ProgramAction g.prog who))
    (h) : ((⟨oi, h⟩ : CurrentProgramMove g who priv).1) = oi := rfl

theorem eq_none_of_not_active
    {g : WFProgram P L} {who : P} (w : CursorCheckedWorld g)
    (a : CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hnot : who ∉ CursorCheckedWorld.active w) :
    a.1 = none := by
  have hmem := a.2 w rfl
  cases ha : a.1 with
  | none => rfl
  | some ai =>
      rw [ha] at hmem
      exact False.elim (hnot (by
        simpa [CursorCheckedWorld.availableProgramMovesAt] using hmem.1))

theorem eq_none_of_terminal
    {g : WFProgram P L} {who : P} (w : CursorCheckedWorld g)
    (a : CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hterm : CursorCheckedWorld.terminal w) :
    a.1 = none := by
  exact eq_none_of_not_active w a
    (by
      have hactive := cursor_terminal_active_eq_empty (w := w) hterm
      simp [hactive])

theorem subsingleton_of_not_active
    {g : WFProgram P L} {who : P} (w : CursorCheckedWorld g)
    (hnot : who ∉ CursorCheckedWorld.active w) :
    Subsingleton
      (CurrentProgramMove g who (privateObsOfCursorWorld who w)) := by
  refine ⟨fun a b => ?_⟩
  apply Subtype.ext
  rw [eq_none_of_not_active w a hnot,
    eq_none_of_not_active w b hnot]

theorem subsingleton_of_terminal
    {g : WFProgram P L} {who : P} (w : CursorCheckedWorld g)
    (hterm : CursorCheckedWorld.terminal w) :
    Subsingleton
      (CurrentProgramMove g who (privateObsOfCursorWorld who w)) := by
  apply subsingleton_of_not_active w
  have hactive := cursor_terminal_active_eq_empty (w := w) hterm
  simp [hactive]

end CurrentProgramMove

/-- Current private observations are finite for concrete finite expression
languages. -/
@[reducible] noncomputable def PrivateObs.instFintype
    (g : WFProgram P L) (LF : FiniteValuation L) (who : P) :
    Fintype (PrivateObs g who) := by
  classical
  let _ : Fintype (ProgramCursor g.prog) :=
    ProgramCursor.instFintype g.prog
  have hEnv : ∀ c : ProgramCursor g.prog,
      Fintype (VEnv L (viewVCtx who c.Γ)) := fun _ =>
    VEnv.instFintype LF
  let e :
      PrivateObs g who ≃
        Sigma (fun c : ProgramCursor g.prog =>
          VEnv L (viewVCtx who c.Γ)) :=
    { toFun := fun obs => ⟨obs.cursor, obs.env⟩
      invFun := fun obs => { cursor := obs.1, env := obs.2 }
      left_inv := by
        intro obs
        cases obs
        rfl
      right_inv := by
        intro obs
        cases obs
        rfl }
  let _ : ∀ c : ProgramCursor g.prog,
      Fintype (VEnv L (viewVCtx who c.Γ)) := hEnv
  exact Fintype.ofEquiv
    (Sigma (fun c : ProgramCursor g.prog =>
      VEnv L (viewVCtx who c.Γ))) e.symm

/-- Legal current moves are finite because they are a subtype of the finite
program-local optional action carrier. -/
@[reducible] noncomputable def CurrentProgramMove.instFintype
    (g : WFProgram P L) (LF : FiniteValuation L)
    (who : P) (priv : PrivateObs g who) :
    Fintype (CurrentProgramMove g who priv) := by
  classical
  let _ : Fintype (ProgramAction g.prog who) :=
    ProgramAction.instFintype LF g.prog who
  exact Fintype.ofFinite (CurrentProgramMove g who priv)

/-- A legal pure Vegas strategy supplies a legal current-observation move at
every private observation. This is used as the nonempty/fallback witness for
the current-observation Kuhn model. -/
noncomputable def currentProgramMoveOfPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (priv : PrivateObs g who) :
    CurrentProgramMove g who priv := by
  refine ⟨
    movePureStrategyAtProgramCursor g hctx who σ
      (ProgramCursor.toSuffix priv.cursor)
      (VEnv.eraseEnv priv.env), ?_⟩
  intro w hpriv
  cases hpriv
  have hmove :
      movePureStrategyAtProgramCursor g hctx who σ
          (ProgramCursor.toSuffix (privateObsOfCursorWorld who w).cursor)
          (VEnv.eraseEnv (privateObsOfCursorWorld who w).env) =
        movePureStrategyAtCursorWorld g hctx who σ w := by
    unfold movePureStrategyAtCursorWorld
    rw [privateObsOfCursorWorld_eraseEnv]
    rfl
  rw [hmove]
  exact movePureStrategyAtProgramCursor_availableAt
    g hctx who σ w.1.suffix w.1.env

/-- A pure profile supplies fallback/nonempty witnesses for all players'
current-observation local action types. -/
@[reducible] noncomputable def currentProgramMoveNonemptyOfPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    ∀ who (priv : PrivateObs g who),
      Nonempty (CurrentProgramMove g who priv) :=
  fun who priv => ⟨currentProgramMoveOfPureStrategy g hctx who (σ who) priv⟩

/-- Erase a current-observation joint action to the program-local optional
joint action used by the cursor transition. -/
def currentProgramJointActionRaw
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    ProgramJointAction g :=
  fun who => (a who).1

theorem currentProgramJointActionRaw_eq_of_active_empty
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hactive : CursorCheckedWorld.active w = ∅) :
    currentProgramJointActionRaw w a =
      currentProgramJointActionRaw w a' := by
  funext who
  have hnot : who ∉ CursorCheckedWorld.active w := by
    simp [hactive]
  change (a who).1 = (a' who).1
  rw [CurrentProgramMove.eq_none_of_not_active w (a who) hnot,
    CurrentProgramMove.eq_none_of_not_active w (a' who) hnot]

theorem currentProgramJointActionRaw_eq_of_agree_active
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hagree : ∀ who, who ∈ CursorCheckedWorld.active w →
      (a who).1 = (a' who).1) :
    currentProgramJointActionRaw w a =
      currentProgramJointActionRaw w a' := by
  funext who
  by_cases hmem : who ∈ CursorCheckedWorld.active w
  · exact hagree who hmem
  · change (a who).1 = (a' who).1
    rw [CurrentProgramMove.eq_none_of_not_active w (a who) hmem,
      CurrentProgramMove.eq_none_of_not_active w (a' who) hmem]

theorem currentProgramJointAction_eq_of_active_empty
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hactive : CursorCheckedWorld.active w = ∅) :
    a = a' := by
  funext who
  apply Subtype.ext
  have hnot : who ∉ CursorCheckedWorld.active w := by
    simp [hactive]
  rw [CurrentProgramMove.eq_none_of_not_active w (a who) hnot,
    CurrentProgramMove.eq_none_of_not_active w (a' who) hnot]

theorem currentProgramMove_eq_none_of_commit_nonowner
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.commit x who R k)
    {i : P} (hi : i ≠ who)
    (a : CurrentProgramMove g i (privateObsOfCursorWorld i w)) :
    a.1 = none := by
  apply CurrentProgramMove.eq_none_of_not_active w a
  have hactive := cursor_active_eq_singleton_of_commit (w := w) hprog
  simp [hactive, hi]

theorem currentProgramMove_exists_available_action_of_commit_owner
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.commit x who R k)
    (a : CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    ∃ ai : ProgramAction g.prog who,
      a.1 = some ai ∧
        ai ∈ CursorCheckedWorld.availableProgramActionsAt
          w.1.prog w.1.env w.1.suffix who := by
  have hmem := a.2 w rfl
  cases ha : a.1 with
  | none =>
      rw [ha] at hmem
      have hactive := cursor_active_eq_singleton_of_commit (w := w) hprog
      have hin : who ∈ CursorCheckedWorld.active w := by
        simp [hactive]
      exact False.elim (hmem hin)
  | some ai =>
      have hmem' := hmem
      rw [ha] at hmem'
      exact ⟨ai, rfl, hmem'.2⟩

/-- Extract the committed value from a current-model local move at a commit
site, using an arbitrary value only for impossible/default branches. -/
noncomputable def currentMoveCommitValueOrDefault
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {g : WFProgram P L} {who : P} {priv : PrivateObs g who}
    {b : L.Ty} (m : CurrentProgramMove g who priv) :
    L.Val b :=
  match m.1 with
  | some ai =>
      if hty : CommitCursor.ty ai.cursor = b then
        hty ▸ ai.value
      else
        Classical.ofNonempty
  | none =>
      Classical.ofNonempty

theorem currentMoveCommitValueOrDefault_eq_programAction_value
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {g : WFProgram P L} {who : P} {priv : PrivateObs g who}
    {b : L.Ty} (m : CurrentProgramMove g who priv)
    {ai : ProgramAction g.prog who}
    (hm : m.1 = some ai)
    (hty : CommitCursor.ty ai.cursor = b) :
    currentMoveCommitValueOrDefault (b := b) m = hty ▸ ai.value := by
  simp [currentMoveCommitValueOrDefault, hm, hty]

theorem currentProgramMove_commit_valueOrDefault_eq_action
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.commit x who R k)
    (m : CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    ∃ (ai : ProgramAction g.prog who)
      (hty : CommitCursor.ty ai.cursor = b),
      m.1 = some ai ∧
        currentMoveCommitValueOrDefault (b := b) m = hty ▸ ai.value := by
  rcases currentProgramMove_exists_available_action_of_commit_owner
      (g := g) w hprog m with
    ⟨ai, hm, hai⟩
  have hbroad :
      ProgramAction.toAction ai ∈
        availableActions
          ({ Γ := w.1.cursor.Γ, prog := VegasCore.commit x who R k,
             env := w.1.env } : World P L) who := by
    rw [← hprog]
    exact hai.1
  rcases (by simpa [availableActions] using hbroad) with
    ⟨v, haiEq, _hguard⟩
  cases ai with
  | mk cursor value =>
      simp only [ProgramAction.toAction] at haiEq
      simp only [Sigma.mk.injEq] at haiEq
      rcases haiEq with ⟨hty, _hval⟩
      exact ⟨⟨cursor, value⟩, hty, hm,
        currentMoveCommitValueOrDefault_eq_programAction_value
          m hm hty⟩

theorem currentMoveCommitValueOrDefault_guard_at_commit
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx w.1.cursor.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: w.1.cursor.Γ)}
    (hprog : w.1.prog = VegasCore.commit x who R k)
    (m : CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    evalGuard (Player := P) (L := L) R
        (currentMoveCommitValueOrDefault (b := b) m)
        (VEnv.eraseEnv w.1.env) = true := by
  have hmem := m.2 w rfl
  cases hm : m.1 with
  | none =>
      rw [hm] at hmem
      have hactive := cursor_active_eq_singleton_of_commit (w := w) hprog
      have hin : who ∈ CursorCheckedWorld.active w := by
        simp [hactive]
      exact False.elim (hmem hin)
  | some ai =>
      rw [hm] at hmem
      have hbroad := hmem.2.1
      have hbroad' :
          ProgramAction.toAction ai ∈
            availableActions
              ({ Γ := w.1.cursor.Γ, prog := VegasCore.commit x who R k,
                 env := w.1.env } : World P L) who := by
        rw [← hprog]
        exact hbroad
      rcases (by
          simpa [availableActions] using hbroad') with
        ⟨v, hai, hguard⟩
      unfold currentMoveCommitValueOrDefault
      rw [hm]
      cases ai with
      | mk cursor value =>
          simp only [ProgramAction.toAction] at hai
          simp only [Sigma.mk.injEq] at hai
          rcases hai with ⟨hty, hval⟩
          have hvalue : hty ▸ value = v := by
            cases hty
            exact eq_of_heq hval
          simpa [currentMoveCommitValueOrDefault, hm, hty, hvalue] using hguard

theorem currentMoveCommitValueOrDefault_guard_at_cursor
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (c : ProgramCursor g.prog)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx c.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: c.Γ)}
    (hprog : c.prog = VegasCore.commit x who R k)
    (env : Env L.Val (eraseVCtx c.Γ))
    (m : CurrentProgramMove g who
      (privateObsOfViewAtCursor who c (projectViewEnv who env))) :
    evalGuard (Player := P) (L := L) R
        (currentMoveCommitValueOrDefault (b := b) m) env = true := by
  let w : CursorCheckedWorld g :=
    ⟨{ cursor := c, env := VEnv.ofErased env },
      ProgramCursor.endpointValid g hctx c⟩
  have hobs := privateObsOfCursorWorld_ofErased hctx who c env
  let mAtW : CurrentProgramMove g who (privateObsOfCursorWorld who w) :=
    ⟨m.1, fun w' hw' => m.2 w' (hw'.trans hobs)⟩
  have hmAtW : mAtW.1 = m.1 := by
    rfl
  have hguard :=
    currentMoveCommitValueOrDefault_guard_at_commit
      (g := g) (w := w) (x := x) (who := who)
      (b := b) (R := R) (k := k) hprog mAtW
  simpa [w, mAtW, hmAtW, VEnv.eraseEnv_ofErased (P := P)
      (ProgramSuffix.wctx c.toSuffix hctx g.wf.1) env]
    using hguard

theorem currentProgramJointActionLegal
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hterm : ¬ CursorCheckedWorld.terminal w) :
    CursorProgramJointActionLegal w (currentProgramJointActionRaw w a) := by
  constructor
  · exact hterm
  · intro who
    have hmem :
        (currentProgramJointActionRaw w a who) ∈
          CursorCheckedWorld.availableProgramMovesAt
            w.1.prog w.1.env w.1.suffix who :=
      (a who).2 w rfl
    cases hmove : currentProgramJointActionRaw w a who with
    | none =>
        rw [hmove] at hmem
        simpa [currentProgramJointActionRaw,
          CursorProgramJointActionLegal,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.active]
          using hmem
    | some ai =>
        rw [hmove] at hmem
        simpa [currentProgramJointActionRaw,
          CursorProgramJointActionLegal,
          CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.active,
          CursorCheckedWorld.availableProgramActions]
          using hmem

/-- One-step transition of the current-observation Kuhn model. -/
noncomputable def currentProgramStep
    (g : WFProgram P L)
    (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w)) :
    PMF (CursorCheckedWorld g) := by
  classical
  exact
    if hterm : CursorCheckedWorld.terminal w then
      PMF.pure w
    else
      cursorProgramTransition w
        ⟨currentProgramJointActionRaw w a,
          currentProgramJointActionLegal w a hterm⟩

@[simp] theorem currentProgramStep_terminal
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hterm : CursorCheckedWorld.terminal w) :
    currentProgramStep g w a = PMF.pure w := by
  simp [currentProgramStep, hterm]

theorem currentProgramStep_nonterminal
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hterm : ¬ CursorCheckedWorld.terminal w) :
    currentProgramStep g w a =
      cursorProgramTransition w
        ⟨currentProgramJointActionRaw w a,
          currentProgramJointActionLegal w a hterm⟩ := by
  simp [currentProgramStep, hterm]

/-- Erase a current value joint action to the program-local optional joint
action used by the cursor transition. -/
noncomputable def currentValueProgramJointActionRaw
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w)) :
    ProgramJointAction g :=
  currentProgramJointActionRaw w
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a who))

theorem currentValueProgramJointActionRaw_eq
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w)) :
    currentValueProgramJointActionRaw w a =
      fun who => CurrentValueMove.toProgramMoveAtWorld w who (a who) := rfl

theorem currentValueProgramJointActionLegal
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w))
    (hterm : ¬ CursorCheckedWorld.terminal w) :
    CursorProgramJointActionLegal w
      (currentValueProgramJointActionRaw w a) := by
  exact currentProgramJointActionLegal w
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a who))
    hterm

/-- One-step transition of the value-indexed current-observation Kuhn model. -/
noncomputable def currentValueProgramStep
    (g : WFProgram P L)
    (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w)) :
    PMF (CursorCheckedWorld g) :=
  currentProgramStep g w
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a who))

@[simp] theorem currentValueProgramStep_terminal
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w))
    (hterm : CursorCheckedWorld.terminal w) :
    currentValueProgramStep g w a = PMF.pure w := by
  simp [currentValueProgramStep, hterm]

theorem currentValueProgramStep_nonterminal
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w))
    (hterm : ¬ CursorCheckedWorld.terminal w) :
    currentValueProgramStep g w a =
      cursorProgramTransition w
        ⟨currentValueProgramJointActionRaw w a,
          currentValueProgramJointActionLegal w a hterm⟩ := by
  simp [currentValueProgramStep, currentValueProgramJointActionRaw,
    currentProgramStep_nonterminal g w
      (fun who => CurrentValueMove.toCurrentProgramMove w who (a who))
      hterm]

theorem currentValueProgramStep_checkedTransition_support
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w dst : CursorCheckedWorld g)
    (a : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w))
    (hterm : ¬ CursorCheckedWorld.terminal w)
    (hsupp : currentValueProgramStep g w a dst ≠ 0) :
    checkedTransition (hctx := hctx) (CheckedWorld.ofCursorChecked w)
        ⟨ProgramJointAction.toAction (currentValueProgramJointActionRaw w a),
          CursorProgramJointActionLegal.toAction
            (currentValueProgramJointActionLegal w a hterm)⟩
        (CheckedWorld.ofCursorChecked dst) ≠ 0 := by
  have hmem :
      dst ∈ (currentValueProgramStep g w a).support := by
    exact (PMF.mem_support_iff _ _).mpr hsupp
  have hmapmem :
      CheckedWorld.ofCursorChecked (hctx := hctx) dst ∈
        (PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          (currentValueProgramStep g w a)).support := by
    rw [PMF.support_map]
    exact ⟨dst, hmem, rfl⟩
  have hmap :
      PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          (currentValueProgramStep g w a) =
        checkedTransition (CheckedWorld.ofCursorChecked (hctx := hctx) w)
          ⟨ProgramJointAction.toAction (currentValueProgramJointActionRaw w a),
            CursorProgramJointActionLegal.toAction
              (currentValueProgramJointActionLegal w a hterm)⟩ := by
    rw [currentValueProgramStep_nonterminal g w a hterm]
    simpa [currentValueProgramJointActionRaw] using
      cursorProgramTransition_map_checkedWorld
        (hctx := hctx) w
        ⟨currentValueProgramJointActionRaw w a,
          currentValueProgramJointActionLegal w a hterm⟩
  rw [hmap] at hmapmem
  exact (PMF.mem_support_iff _ _).mp hmapmem

theorem checkedTransition_commit_support_eq_programActionContinuation
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (wctx : WFCtx Γ) (fresh : FreshBindings (.commit x who R k))
    (viewScoped : ViewScoped (.commit x who R k))
    (normalized : NormalizedDists (.commit x who R k))
    (legal : Legal (.commit x who R k))
    (a : ProgramJointAction g)
    (ha : JointActionLegal
      ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
      (ProgramJointAction.toAction a))
    (dst : CheckedWorld g hctx)
    (hsupp :
      checkedTransition
        ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env,
           suffix := suffix, wctx := wctx, fresh := fresh,
           viewScoped := viewScoped, normalized := normalized, legal := legal } :
          CheckedWorld g hctx)
        ⟨ProgramJointAction.toAction a, by
          simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
            checkedAvailableActions, CheckedWorld.toWorld] using ha⟩ dst ≠ 0) :
    ∃ (ai : ProgramAction g.prog who)
      (_ : a who = some ai)
      (hty : CommitCursor.ty ai.cursor = b),
      dst =
        ({ Γ := (x, .hidden who b) :: Γ
           prog := k
           env := VEnv.cons (Player := P) (L := L) (x := x)
             (τ := .hidden who b) (hty ▸ ai.value) env
           suffix := .commit suffix
           wctx := WFCtx.cons fresh.1 wctx
           fresh := fresh.2
           viewScoped := viewScoped.2
           normalized := normalized
           legal := legal.2 } : CheckedWorld g hctx) := by
  have hstep :=
    checkedTransition_commit_eq_programActionContinuation
      g hctx env suffix wctx fresh viewScoped normalized legal a ha
  rw [hstep] at hsupp
  cases hai : a who with
  | none =>
      have hlocal := ha.2 who
      have hnone : ProgramJointAction.toAction a who = none := by
        simp [ProgramJointAction.toAction, hai]
      rw [hnone] at hlocal
      have hmem :
          who ∈ active
            ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } :
              World P L) := by
        simp [active]
      exact False.elim (hlocal hmem)
  | some ai =>
      by_cases hty : CommitCursor.ty ai.cursor = b
      · refine ⟨ai, rfl, hty, ?_⟩
        simpa [hai, hty, PMF.pure_apply] using hsupp
      · have hlocal := ha.2 who
        have hsome :
            ProgramJointAction.toAction a who =
              some (ProgramAction.toAction ai) := by
          simp [ProgramJointAction.toAction, hai]
        rw [hsome] at hlocal
        have havail := hlocal.2
        rcases (by
            simpa [availableActions, ProgramAction.toAction] using havail) with
          ⟨_v, htyv, _hguard⟩
        exact False.elim (hty htyv.1)

theorem currentProgramStep_eq_of_active_empty
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hactive : CursorCheckedWorld.active w = ∅) :
    currentProgramStep g w a = currentProgramStep g w a' := by
  by_cases hterm : CursorCheckedWorld.terminal w
  · simp [currentProgramStep_terminal, hterm]
  · rw [currentProgramStep_nonterminal g w a hterm,
      currentProgramStep_nonterminal g w a' hterm]
    have hraw := currentProgramJointActionRaw_eq_of_active_empty w a a' hactive
    congr 1
    exact Subtype.ext hraw

theorem currentProgramStep_eq_of_agree_active
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hagree : ∀ who, who ∈ CursorCheckedWorld.active w →
      (a who).1 = (a' who).1) :
    currentProgramStep g w a = currentProgramStep g w a' := by
  by_cases hterm : CursorCheckedWorld.terminal w
  · simp [currentProgramStep_terminal, hterm]
  · rw [currentProgramStep_nonterminal g w a hterm,
      currentProgramStep_nonterminal g w a' hterm]
    have hraw := currentProgramJointActionRaw_eq_of_agree_active w a a' hagree
    congr 1
    exact Subtype.ext hraw

theorem currentProgramStep_actionDeterministic_of_active_empty
    (g : WFProgram P L) (w t : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (hactive : CursorCheckedWorld.active w = ∅)
    (_ha : currentProgramStep g w a t ≠ 0)
    (_ha' : currentProgramStep g w a' t ≠ 0) :
    a = a' :=
  currentProgramJointAction_eq_of_active_empty w a a' hactive

theorem currentProgramStep_massInvariant
    (g : WFProgram P L) (w dst : CursorCheckedWorld g)
    (a₁ a₂ : ∀ who,
      CurrentProgramMove g who (privateObsOfCursorWorld who w))
    (h₁ : currentProgramStep g w a₁ dst ≠ 0)
    (h₂ : currentProgramStep g w a₂ dst ≠ 0) :
    currentProgramStep g w a₁ dst =
      currentProgramStep g w a₂ dst := by
  by_cases hterm : CursorCheckedWorld.terminal w
  · simp [currentProgramStep_terminal, hterm]
  · rw [currentProgramStep_nonterminal g w a₁ hterm] at h₁ ⊢
    rw [currentProgramStep_nonterminal g w a₂ hterm] at h₂ ⊢
    exact cursorProgramTransition_massInvariant w
      ⟨currentProgramJointActionRaw w a₁,
        currentProgramJointActionLegal w a₁ hterm⟩
      ⟨currentProgramJointActionRaw w a₂,
        currentProgramJointActionLegal w a₂ hterm⟩
      dst h₁ h₂

theorem currentValueProgramStep_massInvariant
    (g : WFProgram P L) (w dst : CursorCheckedWorld g)
    (a₁ a₂ : ∀ who,
      CurrentValueMove g who (privateObsOfCursorWorld who w))
    (h₁ : currentValueProgramStep g w a₁ dst ≠ 0)
    (h₂ : currentValueProgramStep g w a₂ dst ≠ 0) :
    currentValueProgramStep g w a₁ dst =
      currentValueProgramStep g w a₂ dst := by
  exact currentProgramStep_massInvariant g w dst
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a₁ who))
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a₂ who))
    h₁ h₂

theorem currentValueProgramStep_eq_of_active_empty
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w))
    (hactive : CursorCheckedWorld.active w = ∅) :
    currentValueProgramStep g w a = currentValueProgramStep g w a' := by
  exact currentProgramStep_eq_of_active_empty g w
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a who))
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a' who))
    hactive

theorem currentValueProgramStep_eq_of_agree_active
    (g : WFProgram P L) (w : CursorCheckedWorld g)
    (a a' : ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w))
    (hagree : ∀ who, who ∈ CursorCheckedWorld.active w →
      a who = a' who) :
    currentValueProgramStep g w a = currentValueProgramStep g w a' := by
  exact currentProgramStep_eq_of_agree_active g w
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a who))
    (fun who => CurrentValueMove.toCurrentProgramMove w who (a' who))
    (by
      intro who hwho
      exact congrArg
        (fun m => (CurrentValueMove.toCurrentProgramMove w who m).1)
        (hagree who hwho))

/-- Kuhn core model whose information state is Vegas' current private
observation and whose local actions are cursor-local committed values. -/
noncomputable def currentValueObsModel
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) :
    ObsModelCore P (CursorCheckedWorld g)
      (fun who => PrivateObs g who)
      (fun who priv => CurrentValueMove g who priv) where
  infoState := fun who => InfoStateCore.identity (PrivateObs g who)
  observe := fun who w => privateObsOfCursorWorld who w
  machine :=
    { init := CursorCheckedWorld.initial g _hctx
      step := fun w a => currentValueProgramStep g w a }

theorem currentValueObsModel_stepMassInvariant
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    letI : ∀ who obs, Fintype (CurrentValueMove g who obs) :=
      fun who obs => CurrentValueMove.instFintype g LF who obs
    ObsModelCore.StepMassInvariant (currentValueObsModel g hctx) := by
  letI : ∀ who obs, Fintype (CurrentValueMove g who obs) :=
    fun who obs => CurrentValueMove.instFintype g LF who obs
  intro ss t π₁ π₂ h₁ h₂
  let w := (currentValueObsModel g hctx).lastState ss
  let a₁ : ∀ who,
      CurrentValueMove g who ((currentValueObsModel g hctx).observe who w) :=
    fun who =>
      (currentValueObsModel g hctx).currentObs_projectStates who ss ▸
        π₁ who ((currentValueObsModel g hctx).projectStates who ss)
  let a₂ : ∀ who,
      CurrentValueMove g who ((currentValueObsModel g hctx).observe who w) :=
    fun who =>
      (currentValueObsModel g hctx).currentObs_projectStates who ss ▸
        π₂ who ((currentValueObsModel g hctx).projectStates who ss)
  have h₁' : currentValueProgramStep g w a₁ t ≠ 0 := by
    simpa [ObsModelCore.pureStep_eq, w, a₁, currentValueObsModel,
      ObsModelCore.step] using h₁
  have h₂' : currentValueProgramStep g w a₂ t ≠ 0 := by
    simpa [ObsModelCore.pureStep_eq, w, a₂, currentValueObsModel,
      ObsModelCore.step] using h₂
  simpa [ObsModelCore.pureStep_eq, w, a₁, a₂, currentValueObsModel,
    ObsModelCore.step] using
      currentValueProgramStep_massInvariant g w t a₁ a₂ h₁' h₂'

theorem currentValueObsModel_action_subsingleton_of_not_active
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hnot : who ∉ CursorCheckedWorld.active
        ((currentValueObsModel g hctx).lastState ss)) :
    Subsingleton
      (CurrentValueMove g who
        ((currentValueObsModel g hctx).currentObs who
          ((currentValueObsModel g hctx).projectStates who ss))) := by
  let O := currentValueObsModel g hctx
  have hobs :
      O.currentObs who (O.projectStates who ss) =
        privateObsOfCursorWorld who (O.lastState ss) := by
    simpa [O, currentValueObsModel] using
      O.currentObs_projectStates who ss
  rw [hobs]
  exact CurrentValueMove.subsingleton_of_not_active
    (O.lastState ss) hnot

theorem currentValueObsModel_active_of_not_subsingleton
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hsub :
      ¬ Subsingleton
        (CurrentValueMove g who
          ((currentValueObsModel g hctx).currentObs who
            ((currentValueObsModel g hctx).projectStates who ss)))) :
    who ∈ CursorCheckedWorld.active
      ((currentValueObsModel g hctx).lastState ss) := by
  by_contra hnot
  exact hsub
    (currentValueObsModel_action_subsingleton_of_not_active
      g hctx who ss hnot)

theorem currentValueObsModel_not_terminal_of_not_subsingleton
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hsub :
      ¬ Subsingleton
        (CurrentValueMove g who
          ((currentValueObsModel g hctx).currentObs who
            ((currentValueObsModel g hctx).projectStates who ss)))) :
    ¬ CursorCheckedWorld.terminal
      ((currentValueObsModel g hctx).lastState ss) := by
  intro hterm
  have hactive :
      CursorCheckedWorld.active ((currentValueObsModel g hctx).lastState ss) = ∅ :=
    cursor_terminal_active_eq_empty
      (w := (currentValueObsModel g hctx).lastState ss) hterm
  have hin :=
    currentValueObsModel_active_of_not_subsingleton g hctx who ss hsub
  simp [hactive] at hin

theorem currentValueObsModel_commit_owner_of_not_subsingleton
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hsub :
      ¬ Subsingleton
        (CurrentValueMove g who
          ((currentValueObsModel g hctx).currentObs who
            ((currentValueObsModel g hctx).projectStates who ss)))) :
    ∃ (x : VarId) (b : L.Ty)
      (R : L.Expr ((x, b) ::
          eraseVCtx ((currentValueObsModel g hctx).lastState ss).1.cursor.Γ)
          L.bool)
      (k : VegasCore P L ((x, .hidden who b) ::
          ((currentValueObsModel g hctx).lastState ss).1.cursor.Γ)),
      ((currentValueObsModel g hctx).lastState ss).1.prog =
        VegasCore.commit x who R k := by
  let w := (currentValueObsModel g hctx).lastState ss
  have hactive :
      who ∈ CursorCheckedWorld.active w :=
    currentValueObsModel_active_of_not_subsingleton g hctx who ss hsub
  cases hprog : w.1.prog with
  | ret payoffs =>
      have hprog' : w.1.cursor.prog = VegasCore.ret payoffs := by
        simpa [CursorWorldData.prog] using hprog
      simp [CursorCheckedWorld.active, CursorCheckedWorld.toWorld,
        CursorWorldData.prog, active, hprog'] at hactive
  | letExpr x e k =>
      have hnone := cursor_active_eq_empty_of_letExpr (w := w) hprog
      simp [hnone] at hactive
  | sample x D k =>
      have hnone := cursor_active_eq_empty_of_sample (w := w) hprog
      simp [hnone] at hactive
  | reveal y owner x hx k =>
      have hnone := cursor_active_eq_empty_of_reveal (w := w) hprog
      simp [hnone] at hactive
  | @commit Γ x owner b R k =>
      have hsingle := cursor_active_eq_singleton_of_commit (w := w) hprog
      have howner' : who = owner := by
        simpa [hsingle] using hactive
      have howner : owner = who := howner'.symm
      subst owner
      refine ⟨x, b, R, k, ?_⟩
      simp [w] at hprog ⊢

theorem currentValueObsModel_stepSupportFactorization
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    letI : ∀ who obs, Fintype (CurrentValueMove g who obs) :=
      fun who obs => CurrentValueMove.instFintype g LF who obs
    ObsModelCore.StepSupportFactorization (currentValueObsModel g hctx) := by
  classical
  letI : ∀ who obs, Fintype (CurrentValueMove g who obs) :=
    fun who obs => CurrentValueMove.instFintype g LF who obs
  intro ss t π₀ π h₀
  let O := currentValueObsModel g hctx
  let w := O.lastState ss
  let act (ρ : O.PureProfile) :
      ∀ who, CurrentValueMove g who (privateObsOfCursorWorld who w) :=
    fun who => by
      have hobs : O.projectStates who ss =
          privateObsOfCursorWorld who w := by
        simpa [O, w, currentValueObsModel, ObsModelCore.currentObs] using
          O.currentObs_projectStates who ss
      exact
        (hobs ▸ ρ who (O.projectStates who ss))
  have hpure : ∀ ρ : O.PureProfile,
      O.pureStep ρ ss = currentValueProgramStep g w (act ρ) := by
    intro ρ
    simpa [O, w, act, currentValueObsModel, ObsModelCore.step]
      using (ObsModelCore.pureStep_eq (O := O) ρ ss)
  have hsame_of_active_empty
      (hactive : CursorCheckedWorld.active w = ∅)
      (ρ ρ' : O.PureProfile) :
      O.pureStep ρ ss = O.pureStep ρ' ss := by
    simpa [hpure ρ, hpure ρ'] using
      currentValueProgramStep_eq_of_active_empty g w (act ρ) (act ρ') hactive
  cases hprog : w.1.prog with
  | ret payoffs =>
      have hactive : CursorCheckedWorld.active w = ∅ := by
        apply cursor_terminal_active_eq_empty
        have hterm :
            terminal
              ({ Γ := w.1.cursor.Γ, prog := w.1.prog,
                 env := w.1.env } : World P L) := by
          rw [hprog]
          exact terminal_ret payoffs
        simpa [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
          CursorWorldData.prog] using hterm
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀
  | letExpr x e k =>
      have hactive := cursor_active_eq_empty_of_letExpr (w := w) hprog
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀
  | sample x D k =>
      have hactive := cursor_active_eq_empty_of_sample (w := w) hprog
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀
  | commit x owner R k =>
      have hactive := cursor_active_eq_singleton_of_commit (w := w) hprog
      have hsame_of_owner
          (ρ ρ' : O.PureProfile)
          (howner :
            act ρ owner = act ρ' owner) :
          O.pureStep ρ ss = O.pureStep ρ' ss := by
        simpa [hpure ρ, hpure ρ'] using
          currentValueProgramStep_eq_of_agree_active g w (act ρ) (act ρ')
            (by
              intro who hwho
              have hwho_eq : who = owner := by
                simpa [hactive] using hwho
              cases hwho_eq
              exact howner)
      constructor
      · intro hπ i
        by_cases hi : i = owner
        · subst i
          have howner :
              act (Function.update π₀ owner (π owner)) owner =
                act π owner := by
            simp [act]
          rw [hsame_of_owner
            (Function.update π₀ owner (π owner)) π howner]
          exact hπ
        · have howner :
              act (Function.update π₀ i (π i)) owner =
                act π₀ owner := by
            have hfun :
                Function.update π₀ i (π i) owner = π₀ owner :=
              Function.update_of_ne (Ne.symm hi) (π i) π₀
            simp [act, hfun]
          rw [hsame_of_owner
            (Function.update π₀ i (π i)) π₀ howner]
          exact h₀
      · intro hall
        have howner :
            act π owner =
              act (Function.update π₀ owner (π owner)) owner := by
          simp [act]
        rw [hsame_of_owner π
          (Function.update π₀ owner (π owner)) howner]
        exact hall owner
  | reveal y owner x hx k =>
      have hactive := cursor_active_eq_empty_of_reveal (w := w) hprog
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀

/-- A pure profile supplies fallback/nonempty witnesses for all players'
value-indexed current-observation local action types. -/
@[reducible] noncomputable def currentValueMoveNonemptyOfPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    ∀ who (priv : PrivateObs g who),
      Nonempty (CurrentValueMove g who priv) :=
  fun who priv => ⟨CurrentValueMove.ofPureStrategy g hctx who (σ who) priv⟩

/-- Embed a legal Vegas pure strategy as a value-indexed local strategy of
the current-observation Kuhn model. -/
noncomputable def currentValueLocalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    (currentValueObsModel g hctx).LocalStrategy who :=
  fun priv => CurrentValueMove.ofPureStrategy g hctx who σ priv

/-- Profile-level embedding of legal Vegas pure strategies into the
value-indexed current-observation Kuhn model. -/
noncomputable def currentValueLocalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (currentValueObsModel g hctx).PureProfile :=
  fun who => currentValueLocalPureStrategy g hctx who (σ who)

/-- Independent mixed legal Vegas pure strategies transported to the
value-indexed current-observation Kuhn model. -/
noncomputable def currentValueLocalMixedPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    ∀ who, PMF ((currentValueObsModel g hctx).LocalStrategy who) :=
  fun who => PMF.map (currentValueLocalPureStrategy g hctx who) (μ who)

theorem currentValueLocalMixedPureProfile_joint
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentValueObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentValueMove g who obs) :=
      fun who obs => CurrentValueMove.instFintype g LF who obs
    Math.PMFProduct.pmfPi (currentValueLocalMixedPureProfile g hctx μ) =
      PMF.map (currentValueLocalPureProfile g hctx)
        (Math.PMFProduct.pmfPi μ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentValueObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentValueMove g who obs) :=
    fun who obs => CurrentValueMove.instFintype g LF who obs
  change Math.PMFProduct.pmfPi
      (fun who =>
        PMF.map (currentValueLocalPureStrategy g hctx who) (μ who)) =
    PMF.map
      (fun σ => currentValueLocalPureProfile g hctx σ)
      (Math.PMFProduct.pmfPi μ)
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun who => currentValueLocalPureStrategy g hctx who)).symm

/-- Semantic M→B specialized to the value-indexed current-observation model,
under the exact GameTheory semantic hypotheses. -/
theorem currentValueObsModel_mixedPure_realized_by_behavioral_of_semanticConditions
    [Fintype P] [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) (k : Nat) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentValueObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentValueMove g who obs) :=
      fun who obs => CurrentValueMove.instFintype g LF who obs
    ObsModelCore.RunSupportFactorization (currentValueObsModel g hctx) →
    (∀ who, ObsModelCore.ActionPosteriorLocal
      (currentValueObsModel g hctx) who) →
    ∃ β : ObsModelCore.BehavioralProfile (currentValueObsModel g hctx),
      (currentValueObsModel g hctx).runDist k β =
        (PMF.map (currentValueLocalPureProfile g hctx)
          (Math.PMFProduct.pmfPi μ)).bind
            ((currentValueObsModel g hctx).runDistPure k) := by
  classical
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentValueObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentValueMove g who obs) :=
    fun who obs => CurrentValueMove.instFintype g LF who obs
  intro hRun hLocal
  have hMass : ObsModelCore.StepMassInvariant (currentValueObsModel g hctx) :=
    currentValueObsModel_stepMassInvariant g hctx LF
  letI : Nonempty (LegalProgramPureProfile g) :=
    LegalProgramPureProfile.instNonempty_of_wfctx g hctx
  let fallback : LegalProgramPureProfile g := Classical.choice inferInstance
  letI : ∀ who obs, Nonempty (CurrentValueMove g who obs) :=
    currentValueMoveNonemptyOfPureProfile g hctx fallback
  obtain ⟨β, hβ⟩ :=
    ObsModelCore.kuhn_mixed_to_behavioral_of_runSupport
      (O := currentValueObsModel g hctx)
      hMass hRun hLocal
      (currentValueLocalMixedPureProfile g hctx μ) k
  refine ⟨β, ?_⟩
  rw [hβ]
  rw [currentValueLocalMixedPureProfile_joint g hctx LF μ]

/-- Semantic M→B specialized to the value-indexed current-observation model
after discharging support factorization. -/
theorem currentValueObsModel_mixedPure_realized_by_behavioral_of_posteriorLocal
    [Fintype P] [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) (k : Nat) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentValueObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentValueMove g who obs) :=
      fun who obs => CurrentValueMove.instFintype g LF who obs
    (∀ who, ObsModelCore.ActionPosteriorLocal
      (currentValueObsModel g hctx) who) →
    ∃ β : ObsModelCore.BehavioralProfile (currentValueObsModel g hctx),
      (currentValueObsModel g hctx).runDist k β =
        (PMF.map (currentValueLocalPureProfile g hctx)
          (Math.PMFProduct.pmfPi μ)).bind
            ((currentValueObsModel g hctx).runDistPure k) := by
  classical
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentValueObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentValueMove g who obs) :=
    fun who obs => CurrentValueMove.instFintype g LF who obs
  intro hLocal
  exact currentValueObsModel_mixedPure_realized_by_behavioral_of_semanticConditions
    g hctx LF μ k
    (ObsModelCore.StepSupportFactorization.toRunSupportFactorization
      (currentValueObsModel_stepSupportFactorization g hctx LF))
    hLocal

/-- Kuhn core model whose information state is exactly Vegas' current private
observation. Its behavioral profiles are the semantic target for total
Vegas-view PMF behavioral strategies. -/
noncomputable def currentObsModel
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) :
    ObsModelCore P (CursorCheckedWorld g)
      (fun who => PrivateObs g who)
      (fun who priv => CurrentProgramMove g who priv) where
  infoState := fun who => InfoStateCore.identity (PrivateObs g who)
  observe := fun who w => privateObsOfCursorWorld who w
  machine :=
    { init := CursorCheckedWorld.initial g _hctx
      step := fun w a => currentProgramStep g w a }

theorem currentObsModel_stepMassInvariant
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    letI : ∀ who obs, Fintype (CurrentProgramMove g who obs) :=
      fun who obs => CurrentProgramMove.instFintype g LF who obs
    ObsModelCore.StepMassInvariant (currentObsModel g hctx) := by
  letI : ∀ who obs, Fintype (CurrentProgramMove g who obs) :=
    fun who obs => CurrentProgramMove.instFintype g LF who obs
  intro ss t π₁ π₂ h₁ h₂
  let w := (currentObsModel g hctx).lastState ss
  let a₁ : ∀ who,
      CurrentProgramMove g who ((currentObsModel g hctx).observe who w) :=
    fun who =>
      (currentObsModel g hctx).currentObs_projectStates who ss ▸
        π₁ who ((currentObsModel g hctx).projectStates who ss)
  let a₂ : ∀ who,
      CurrentProgramMove g who ((currentObsModel g hctx).observe who w) :=
    fun who =>
      (currentObsModel g hctx).currentObs_projectStates who ss ▸
        π₂ who ((currentObsModel g hctx).projectStates who ss)
  have h₁' : currentProgramStep g w a₁ t ≠ 0 := by
    simpa [ObsModelCore.pureStep_eq, w, a₁, currentObsModel,
      ObsModelCore.step] using h₁
  have h₂' : currentProgramStep g w a₂ t ≠ 0 := by
    simpa [ObsModelCore.pureStep_eq, w, a₂, currentObsModel,
      ObsModelCore.step] using h₂
  simpa [ObsModelCore.pureStep_eq, w, a₁, a₂, currentObsModel,
    ObsModelCore.step] using
      currentProgramStep_massInvariant g w t a₁ a₂ h₁' h₂'

theorem currentObsModel_action_subsingleton_of_not_active
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hnot :
      who ∉ CursorCheckedWorld.active
        ((currentObsModel g hctx).lastState ss)) :
    Subsingleton
      (CurrentProgramMove g who
        ((currentObsModel g hctx).currentObs who
          ((currentObsModel g hctx).projectStates who ss))) := by
  let O := currentObsModel g hctx
  have hobs :
      O.currentObs who (O.projectStates who ss) =
        privateObsOfCursorWorld who (O.lastState ss) := by
    simpa [O, currentObsModel] using
      O.currentObs_projectStates who ss
  rw [hobs]
  exact CurrentProgramMove.subsingleton_of_not_active
    (O.lastState ss) hnot

theorem currentObsModel_active_of_not_subsingleton
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hsub :
      ¬ Subsingleton
        (CurrentProgramMove g who
          ((currentObsModel g hctx).currentObs who
            ((currentObsModel g hctx).projectStates who ss)))) :
    who ∈ CursorCheckedWorld.active
      ((currentObsModel g hctx).lastState ss) := by
  by_contra hnot
  exact hsub
    (currentObsModel_action_subsingleton_of_not_active
      g hctx who ss hnot)

theorem currentObsModel_not_terminal_of_not_subsingleton
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hsub :
      ¬ Subsingleton
        (CurrentProgramMove g who
          ((currentObsModel g hctx).currentObs who
            ((currentObsModel g hctx).projectStates who ss)))) :
    ¬ CursorCheckedWorld.terminal
      ((currentObsModel g hctx).lastState ss) := by
  intro hterm
  have hactive :=
    currentObsModel_active_of_not_subsingleton g hctx who ss hsub
  have hempty := cursor_terminal_active_eq_empty
    (w := (currentObsModel g hctx).lastState ss) hterm
  simp [hempty] at hactive

theorem currentObsModel_commit_owner_of_not_subsingleton
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g))
    (hsub :
      ¬ Subsingleton
        (CurrentProgramMove g who
          ((currentObsModel g hctx).currentObs who
            ((currentObsModel g hctx).projectStates who ss)))) :
    ∃ (x : VarId) (b : L.Ty)
      (R : L.Expr
        ((x, b) ::
          eraseVCtx ((currentObsModel g hctx).lastState ss).1.cursor.Γ)
        L.bool)
      (k : VegasCore P L
        ((x, .hidden who b) ::
          ((currentObsModel g hctx).lastState ss).1.cursor.Γ)),
      ((currentObsModel g hctx).lastState ss).1.prog =
        VegasCore.commit x who R k := by
  let w := (currentObsModel g hctx).lastState ss
  have hactive :
      who ∈ CursorCheckedWorld.active w :=
    currentObsModel_active_of_not_subsingleton g hctx who ss hsub
  cases hprog : w.1.prog with
  | ret payoffs =>
      have hfalse : False := by
        have hterm : CursorCheckedWorld.terminal w := by
          have htermWorld :
              terminal
                ({ Γ := w.1.cursor.Γ, prog := w.1.prog,
                   env := w.1.env } : World P L) := by
            rw [hprog]
            exact terminal_ret payoffs
          simpa [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
            CursorWorldData.prog] using htermWorld
        have hempty := cursor_terminal_active_eq_empty (w := w) hterm
        simp [hempty] at hactive
      exact False.elim hfalse
  | letExpr x e k =>
      have hfalse : False := by
        have hempty := cursor_active_eq_empty_of_letExpr (w := w) hprog
        simp [hempty] at hactive
      exact False.elim hfalse
  | sample x D k =>
      have hfalse : False := by
        have hempty := cursor_active_eq_empty_of_sample (w := w) hprog
        simp [hempty] at hactive
      exact False.elim hfalse
  | commit x owner R k =>
      have howner : owner = who := by
        have hmem : who ∈ ({owner} : Finset P) := by
          have hsingle := cursor_active_eq_singleton_of_commit (w := w) hprog
          simpa [hsingle] using hactive
        exact (Finset.mem_singleton.mp hmem).symm
      cases howner
      exact ⟨x, _, R, k, by simp [w]⟩
  | reveal y owner x hx k =>
      have hfalse : False := by
        have hempty := cursor_active_eq_empty_of_reveal (w := w) hprog
        simp [hempty] at hactive
      exact False.elim hfalse

theorem currentObsModel_stepSupportFactorization
    [Fintype P] (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (LF : FiniteValuation L) :
    letI : ∀ who obs, Fintype (CurrentProgramMove g who obs) :=
      fun who obs => CurrentProgramMove.instFintype g LF who obs
    ObsModelCore.StepSupportFactorization (currentObsModel g hctx) := by
  classical
  letI : ∀ who obs, Fintype (CurrentProgramMove g who obs) :=
    fun who obs => CurrentProgramMove.instFintype g LF who obs
  intro ss t π₀ π h₀
  let O := currentObsModel g hctx
  let w := O.lastState ss
  let act (ρ : O.PureProfile) :
      ∀ who, CurrentProgramMove g who (privateObsOfCursorWorld who w) :=
    fun who => by
      have hobs : O.projectStates who ss =
          privateObsOfCursorWorld who w := by
        simpa [O, w, currentObsModel, ObsModelCore.currentObs] using
          O.currentObs_projectStates who ss
      exact
        (hobs ▸ ρ who (O.projectStates who ss))
  have hpure : ∀ ρ : O.PureProfile,
      O.pureStep ρ ss = currentProgramStep g w (act ρ) := by
    intro ρ
    simpa [O, w, act, currentObsModel, ObsModelCore.step]
      using (ObsModelCore.pureStep_eq (O := O) ρ ss)
  have hsame_of_active_empty
      (hactive : CursorCheckedWorld.active w = ∅)
      (ρ ρ' : O.PureProfile) :
      O.pureStep ρ ss = O.pureStep ρ' ss := by
    simpa [hpure ρ, hpure ρ'] using
      currentProgramStep_eq_of_active_empty g w (act ρ) (act ρ') hactive
  cases hprog : w.1.prog with
  | ret payoffs =>
      have hactive : CursorCheckedWorld.active w = ∅ := by
        apply cursor_terminal_active_eq_empty
        have hterm :
            terminal
              ({ Γ := w.1.cursor.Γ, prog := w.1.prog,
                 env := w.1.env } : World P L) := by
          rw [hprog]
          exact terminal_ret payoffs
        simpa [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
          CursorWorldData.prog] using hterm
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀
  | letExpr x e k =>
      have hactive := cursor_active_eq_empty_of_letExpr (w := w) hprog
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀
  | sample x D k =>
      have hactive := cursor_active_eq_empty_of_sample (w := w) hprog
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀
  | commit x owner R k =>
      have hactive := cursor_active_eq_singleton_of_commit (w := w) hprog
      have hsame_of_owner
          (ρ ρ' : O.PureProfile)
          (howner :
            (act ρ owner).1 = (act ρ' owner).1) :
          O.pureStep ρ ss = O.pureStep ρ' ss := by
        simpa [hpure ρ, hpure ρ'] using
          currentProgramStep_eq_of_agree_active g w (act ρ) (act ρ')
            (by
              intro who hwho
              have hwho_eq : who = owner := by
                simpa [hactive] using hwho
              cases hwho_eq
              exact howner)
      constructor
      · intro hπ i
        by_cases hi : i = owner
        · subst i
          have howner :
              (act (Function.update π₀ owner (π owner)) owner).1 =
                (act π owner).1 := by
            simp [act]
          rw [hsame_of_owner
            (Function.update π₀ owner (π owner)) π howner]
          exact hπ
        · have howner :
              (act (Function.update π₀ i (π i)) owner).1 =
                (act π₀ owner).1 := by
            have hfun :
                Function.update π₀ i (π i) owner = π₀ owner :=
              Function.update_of_ne (Ne.symm hi) (π i) π₀
            simp [act, hfun]
          rw [hsame_of_owner
            (Function.update π₀ i (π i)) π₀ howner]
          exact h₀
      · intro hall
        have howner :
            (act π owner).1 =
              (act (Function.update π₀ owner (π owner)) owner).1 := by
          simp [act]
        rw [hsame_of_owner π
          (Function.update π₀ owner (π owner)) howner]
        exact hall owner
  | reveal y owner x hx k =>
      have hactive := cursor_active_eq_empty_of_reveal (w := w) hprog
      constructor
      · intro _ i
        rw [hsame_of_active_empty hactive
          (Function.update π₀ i (π i)) π₀]
        exact h₀
      · intro _
        rw [hsame_of_active_empty hactive π π₀]
        exact h₀

/-- The PMF kernel obtained by reading a current-observation behavioral
profile at one owned commit cursor. -/
noncomputable def currentBehavioralKernelPMFAtCursor
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : ObsModelCore.BehavioralProfile (currentObsModel g hctx))
    (c : ProgramCursor g.prog)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx c.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: c.Γ)}
    (_hprog : c.prog = VegasCore.commit x who R k) :
    ProgramBehavioralKernelPMF who c.Γ b where
  run := fun view =>
    PMF.map (currentMoveCommitValueOrDefault (b := b))
      (β who (privateObsOfViewAtCursor who c view))

theorem currentBehavioralKernelPMFAtCursor_isLegalAt
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : ObsModelCore.BehavioralProfile (currentObsModel g hctx))
    (c : ProgramCursor g.prog)
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx c.Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: c.Γ)}
    (hprog : c.prog = VegasCore.commit x who R k) :
    (currentBehavioralKernelPMFAtCursor g hctx β c hprog).IsLegalAt R := by
  intro env v hv
  change v ∈
      (PMF.map (currentMoveCommitValueOrDefault (b := b))
        (β who
          (privateObsOfViewAtCursor who c
            (projectViewEnv who env)))).support at hv
  rcases (PMF.mem_support_map_iff _ _ _).mp hv with ⟨m, _hm, hm⟩
  rw [← hm]
  exact currentMoveCommitValueOrDefault_guard_at_cursor
    g hctx c hprog env m

/-- Current-observation private state at a concrete commit suffix, using the
canonical finite cursor for that suffix. -/
noncomputable def privateObsOfViewAtCommitSuffix
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) : PrivateObs g who :=
  let c := ProgramCursor.CommitCursor.toProgramCursor
    (ProgramSuffix.commitCursor suffix)
  { cursor := c
    env := cast
      (congrArg (fun Δ => VEnv L (viewVCtx who Δ))
        (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix).symm)
      (VEnv.ofErased view :
        VEnv L (viewVCtx who Γ)) }

theorem privateObsOfCursorWorld_ofErased_commitSuffix
    {g : WFProgram P L} (hctx : WFCtx g.Γ)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (env : Env L.Val (eraseVCtx Γ)) :
    let c := ProgramCursor.CommitCursor.toProgramCursor
      (ProgramSuffix.commitCursor suffix)
    let envAtCursor : Env L.Val (eraseVCtx c.Γ) :=
      cast (congrArg (fun Δ => Env L.Val (eraseVCtx Δ))
        (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix).symm) env
    privateObsOfCursorWorld who
        (⟨{ cursor := c, env := VEnv.ofErased envAtCursor },
          ProgramCursor.endpointValid g hctx c⟩ : CursorCheckedWorld g) =
      privateObsOfViewAtCommitSuffix suffix
        (projectViewEnv who env) := by
  dsimp [privateObsOfViewAtCommitSuffix, privateObsOfCursorWorld]
  congr
  let c := ProgramCursor.CommitCursor.toProgramCursor
    (ProgramSuffix.commitCursor suffix)
  let hΓ := ProgramSuffix.commitCursor_toProgramCursor_Γ suffix
  let envAtCursor : Env L.Val (eraseVCtx c.Γ) :=
    cast (congrArg (fun Δ => Env L.Val (eraseVCtx Δ)) hΓ.symm) env
  have hview :=
    VEnv.toView_ofErased_projectViewEnv
      (ProgramSuffix.wctx c.toSuffix hctx g.wf.1) who envAtCursor
  have hproject :=
    projectViewEnv_cast_ctx (P := P) (L := L) who hΓ env
  rw [hproject] at hview
  rw [VEnv.ofErased_cast_ctx
    (P := P) (L := L) (congrArg (viewVCtx who) hΓ)
      (projectViewEnv who env)] at hview
  simpa [c, hΓ, envAtCursor] using hview

/-- The PMF kernel obtained by reading a current-observation behavioral profile
at a suffix-indexed owned commit site. -/
noncomputable def currentBehavioralKernelPMFAtSuffix
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : ObsModelCore.BehavioralProfile (currentObsModel g hctx))
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k)) :
    ProgramBehavioralKernelPMF who Γ b where
  run := fun view =>
    PMF.map (currentMoveCommitValueOrDefault (b := b))
      (β who (privateObsOfViewAtCommitSuffix suffix view))

/-- Read a current-observation behavioral profile as an ordinary total Vegas
PMF behavioral profile at a suffix of the root program. -/
noncomputable def currentBehavioralProfilePMFAtSuffix
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : ObsModelCore.BehavioralProfile (currentObsModel g hctx)) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      ProgramSuffix g.prog p → ProgramBehavioralProfilePMF p
  | _, .ret _, _suffix =>
      fun _who => .ret
  | _, .letExpr _ _ k, suffix =>
      fun who => .letExpr
        (currentBehavioralProfilePMFAtSuffix g hctx β k
          (ProgramSuffix.letExpr suffix) who)
  | _, .sample _ _ k, suffix =>
      fun who => .sample
        (currentBehavioralProfilePMFAtSuffix g hctx β k
          (ProgramSuffix.sample suffix) who)
  | _, .commit x owner R k, suffix =>
      fun who => by
        by_cases howner : owner = who
        · cases howner
          exact .commitOwn
            (currentBehavioralKernelPMFAtSuffix g hctx β suffix)
            (currentBehavioralProfilePMFAtSuffix g hctx β k
              (ProgramSuffix.commit suffix) owner)
        · exact .commitOther howner
            (currentBehavioralProfilePMFAtSuffix g hctx β k
              (ProgramSuffix.commit suffix) who)
  | _, .reveal _ _ _ _ k, suffix =>
      fun who => .reveal
        (currentBehavioralProfilePMFAtSuffix g hctx β k
          (ProgramSuffix.reveal suffix) who)
termination_by _Γ p _suffix => syntaxSteps p
decreasing_by
  simp_wf
  all_goals
    first
    | rw [syntaxSteps_letExpr]
    | rw [syntaxSteps_sample]
    | rw [syntaxSteps_commit]
    | rw [syntaxSteps_reveal]
    omega

/-- Root version of `currentBehavioralProfilePMFAtSuffix`. -/
noncomputable def currentBehavioralProfilePMF
    [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : ObsModelCore.BehavioralProfile (currentObsModel g hctx)) :
    ProgramBehavioralProfilePMF g.prog :=
  currentBehavioralProfilePMFAtSuffix g hctx β g.prog .here

/-- Embed a legal Vegas pure strategy as a local strategy of the
current-observation Kuhn model. -/
noncomputable def currentLocalPureStrategy
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who) :
    (currentObsModel g hctx).LocalStrategy who :=
  fun priv => currentProgramMoveOfPureStrategy g hctx who σ priv

/-- Profile-level embedding of legal Vegas pure strategies into the
current-observation Kuhn model. -/
noncomputable def currentLocalPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramPureProfile g) :
    (currentObsModel g hctx).PureProfile :=
  fun who => currentLocalPureStrategy g hctx who (σ who)

/-- Independent mixed legal Vegas pure strategies transported to the
current-observation Kuhn model. -/
noncomputable def currentLocalMixedPureProfile
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    ∀ who, PMF ((currentObsModel g hctx).LocalStrategy who) :=
  fun who => PMF.map (currentLocalPureStrategy g hctx who) (μ who)

theorem currentLocalMixedPureProfile_joint
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentProgramMove g who obs) :=
      fun who obs => CurrentProgramMove.instFintype g LF who obs
    Math.PMFProduct.pmfPi (currentLocalMixedPureProfile g hctx μ) =
      PMF.map (currentLocalPureProfile g hctx)
        (Math.PMFProduct.pmfPi μ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentProgramMove g who obs) :=
    fun who obs => CurrentProgramMove.instFintype g LF who obs
  change Math.PMFProduct.pmfPi
      (fun who =>
        PMF.map (currentLocalPureStrategy g hctx who) (μ who)) =
    PMF.map
      (fun σ => currentLocalPureProfile g hctx σ)
      (Math.PMFProduct.pmfPi μ)
  exact (Math.PMFProduct.pmfPi_push_coordwise μ
    (fun who => currentLocalPureStrategy g hctx who)).symm

/-- Semantic M→B specialized to the current-observation model, under the
exact GameTheory semantic hypotheses.

This states preservation of the current-model run distribution, not yet the
final Vegas outcome distribution. It is intentionally phrased with
`RunSupportFactorization` and `ActionPosteriorLocal`, because those are the
semantic facts used by the run-level core M→B theorem; full obs-local
feasibility is only one sufficient way to obtain them. -/
theorem currentObsModel_mixedPure_realized_by_behavioral_of_semanticConditions
    [Fintype P] [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) (k : Nat) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentProgramMove g who obs) :=
      fun who obs => CurrentProgramMove.instFintype g LF who obs
    ObsModelCore.RunSupportFactorization (currentObsModel g hctx) →
    (∀ who, ObsModelCore.ActionPosteriorLocal (currentObsModel g hctx) who) →
    ∃ β : ObsModelCore.BehavioralProfile (currentObsModel g hctx),
      (currentObsModel g hctx).runDist k β =
        (PMF.map (currentLocalPureProfile g hctx)
          (Math.PMFProduct.pmfPi μ)).bind
            ((currentObsModel g hctx).runDistPure k) := by
  classical
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentProgramMove g who obs) :=
    fun who obs => CurrentProgramMove.instFintype g LF who obs
  intro hRun hLocal
  have hMass : ObsModelCore.StepMassInvariant (currentObsModel g hctx) :=
    currentObsModel_stepMassInvariant g hctx LF
  letI : Nonempty (LegalProgramPureProfile g) :=
    LegalProgramPureProfile.instNonempty_of_wfctx g hctx
  let fallback : LegalProgramPureProfile g := Classical.choice inferInstance
  letI : ∀ who obs, Nonempty (CurrentProgramMove g who obs) :=
    currentProgramMoveNonemptyOfPureProfile g hctx fallback
  obtain ⟨β, hβ⟩ :=
    ObsModelCore.kuhn_mixed_to_behavioral_of_runSupport
      (O := currentObsModel g hctx)
      hMass hRun hLocal
      (currentLocalMixedPureProfile g hctx μ) k
  refine ⟨β, ?_⟩
  rw [hβ]
  rw [currentLocalMixedPureProfile_joint g hctx LF μ]

/-- Semantic M→B specialized to the current-observation model, after
discharging Vegas' support-factorization obligation.

At this point the only semantic assumption left is action-posterior locality:
conditional next-action posteriors must depend only on the acting player's
current private observation. -/
theorem currentObsModel_mixedPure_realized_by_behavioral_of_posteriorLocal
    [Fintype P] [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) (k : Nat) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentProgramMove g who obs) :=
      fun who obs => CurrentProgramMove.instFintype g LF who obs
    (∀ who, ObsModelCore.ActionPosteriorLocal (currentObsModel g hctx) who) →
    ∃ β : ObsModelCore.BehavioralProfile (currentObsModel g hctx),
      (currentObsModel g hctx).runDist k β =
        (PMF.map (currentLocalPureProfile g hctx)
          (Math.PMFProduct.pmfPi μ)).bind
            ((currentObsModel g hctx).runDistPure k) := by
  classical
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentProgramMove g who obs) :=
    fun who obs => CurrentProgramMove.instFintype g LF who obs
  intro hLocal
  exact currentObsModel_mixedPure_realized_by_behavioral_of_semanticConditions
    g hctx LF μ k
    (ObsModelCore.StepSupportFactorization.toRunSupportFactorization
      (currentObsModel_stepSupportFactorization g hctx LF))
    hLocal

/-- Semantic M→B specialized to the current-observation model, with full
obs-local feasibility as a sufficient packaged hypothesis.

Step mass invariance and support factorization are discharged by the cursor
transition semantics. Full obs-local feasibility remains as one sufficient way
to obtain posterior locality. -/
theorem currentObsModel_mixedPure_realized_by_behavioral_semantic
    [Fintype P] [∀ τ : L.Ty, Nonempty (L.Val τ)]
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) (k : Nat) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
      fun who => PrivateObs.instFintype g LF who
    letI : ∀ who obs,
        Fintype (CurrentProgramMove g who obs) :=
      fun who obs => CurrentProgramMove.instFintype g LF who obs
    (∀ who, ObsModelCore.ObsLocalFeasibilityFull
      (currentObsModel g hctx) who) →
    ∃ β : ObsModelCore.BehavioralProfile (currentObsModel g hctx),
      (currentObsModel g hctx).runDist k β =
        (PMF.map (currentLocalPureProfile g hctx)
          (Math.PMFProduct.pmfPi μ)).bind
            ((currentObsModel g hctx).runDistPure k) := by
  classical
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : ∀ who, Fintype ((currentObsModel g hctx).InfoState who) :=
    fun who => PrivateObs.instFintype g LF who
  letI : ∀ who obs,
      Fintype (CurrentProgramMove g who obs) :=
    fun who obs => CurrentProgramMove.instFintype g LF who obs
  intro hObsLocal
  exact currentObsModel_mixedPure_realized_by_behavioral_of_posteriorLocal
    g hctx LF μ k
    (fun who =>
      ObsModelCore.actionPosteriorLocal_of_obsLocalFeasibility
        (O := currentObsModel g hctx)
        (currentObsModel_stepMassInvariant g hctx LF)
        who
        (fun n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ _hnontriv πᵢ =>
          hObsLocal who n₁ n₂ π₀ π₀' ss₁ ss₂ hobs h₁ h₂ πᵢ))

@[simp] theorem currentLocalPureStrategy_apply_observe
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (σ : LegalProgramPureStrategy g who)
    (w : CursorCheckedWorld g) :
    ((currentLocalPureStrategy g hctx who σ)
        (privateObsOfCursorWorld who w)).1 =
      movePureStrategyAtCursorWorld g hctx who σ w := by
  unfold currentLocalPureStrategy currentProgramMoveOfPureStrategy
  simp only
  unfold movePureStrategyAtCursorWorld
  rw [privateObsOfCursorWorld_eraseEnv]
  rfl

@[simp] theorem currentObsModel_init
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (currentObsModel g hctx).init = CursorCheckedWorld.initial g hctx := rfl

@[simp] theorem currentObsModel_observe
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (w : CursorCheckedWorld g) :
    (currentObsModel g hctx).observe who w =
      privateObsOfCursorWorld who w := rfl

@[simp] theorem currentObsModel_currentObs
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (priv : (currentObsModel g hctx).InfoState who) :
    (currentObsModel g hctx).currentObs who priv = priv := rfl

/-- With identity information states, a projected state trace is exactly the
current private observation at the trace endpoint. This is the deterministic
current-view fact the total Vegas strategy space relies on. -/
theorem currentObsModel_projectStates
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g)) :
    (currentObsModel g hctx).projectStates who ss =
      privateObsOfCursorWorld who ((currentObsModel g hctx).lastState ss) := by
  have h :=
    (currentObsModel g hctx).currentObs_projectStates who ss
  simpa using h

@[simp] theorem currentObsModel_projectStates_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) :
    (currentObsModel g hctx).projectStates who [] =
      privateObsOfCursorWorld who (CursorCheckedWorld.initial g hctx) := by
  simpa using currentObsModel_projectStates g hctx who []

@[simp] theorem currentValueObsModel_init
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (currentValueObsModel g hctx).init = CursorCheckedWorld.initial g hctx := rfl

@[simp] theorem currentValueObsModel_observe
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (w : CursorCheckedWorld g) :
    (currentValueObsModel g hctx).observe who w =
      privateObsOfCursorWorld who w := rfl

@[simp] theorem currentValueObsModel_currentObs
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (priv : (currentValueObsModel g hctx).InfoState who) :
    (currentValueObsModel g hctx).currentObs who priv = priv := rfl

theorem currentValueObsModel_projectStates
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) (ss : List (CursorCheckedWorld g)) :
    (currentValueObsModel g hctx).projectStates who ss =
      privateObsOfCursorWorld who ((currentValueObsModel g hctx).lastState ss) := by
  simpa [currentValueObsModel] using
    (currentValueObsModel g hctx).currentObs_projectStates who ss

@[simp] theorem currentValueObsModel_projectStates_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (who : P) :
    (currentValueObsModel g hctx).projectStates who [] =
      privateObsOfCursorWorld who (CursorCheckedWorld.initial g hctx) := by
  simpa using currentValueObsModel_projectStates g hctx who []

end Observed

end FOSGBridge
end Vegas
