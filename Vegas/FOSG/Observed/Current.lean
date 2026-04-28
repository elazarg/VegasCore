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

/-- Semantic M→B specialized to the current-observation model, with full
obs-local feasibility as a sufficient packaged hypothesis.

Step mass invariance is discharged by the cursor transition semantics. Full
obs-local feasibility supplies the remaining support-factorization and
posterior-locality obligations expected by the exact semantic theorem above. -/
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
  exact currentObsModel_mixedPure_realized_by_behavioral_of_semanticConditions
    g hctx LF μ k
    (ObsModelCore.obsLocalFeasibilityFull_toRunSupportFactorization
      (O := currentObsModel g hctx) hObsLocal)
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

end Observed

end FOSGBridge
end Vegas
