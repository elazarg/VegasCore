import Vegas.FOSG.Basic

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}
/-! ## Observation-preserving target -/

/-- The FOSG public-observation channel is unused for Vegas.

Public Vegas bindings are already included in every player's private
`ViewEnv`, so carrying them again as `PubObs` only duplicates information and
creates dependent transport noise. -/
abbrev PublicObs (g : WFProgram P L) (_hctx : WFCtx g.Γ) := PUnit

/-- Private observation after a Vegas/FOSG transition: the observing player's
current program cursor and view environment. The cursor is public information,
but storing it here makes the player's local observation self-sufficient for
strategy lookup and action-availability proofs. -/
@[ext]
structure PrivateObs (g : WFProgram P L) (who : P) where
  cursor : ProgramCursor g.prog
  env : ViewEnv who cursor.Γ

def publicObsOfCursorWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (_w : CursorCheckedWorld g) : PublicObs g hctx :=
  PUnit.unit

def publicObsOfCursorEnv {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (c : ProgramCursor g.prog) (_env : VEnv L c.Γ) :
    PublicObs g hctx :=
  PUnit.unit

noncomputable def privateObsOfCursorWorld {g : WFProgram P L}
    (who : P) (w : CursorCheckedWorld g) :
    PrivateObs g who where
  cursor := w.1.cursor
  env := projectViewEnv who (VEnv.eraseEnv w.1.env)

noncomputable def privateObsOfCursorEnv {g : WFProgram P L}
    (who : P) (c : ProgramCursor g.prog) (env : VEnv L c.Γ) :
    PrivateObs g who where
  cursor := c
  env := projectViewEnv who (VEnv.eraseEnv env)

/-- The private-observation key corresponding to a syntax-recursive owned
commit site and a current Vegas view at that site. -/
noncomputable def privateObsOfCommitSite {g : WFProgram P L}
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) :
    PrivateObs g who where
  cursor :=
    ProgramCursor.CommitCursor.toProgramCursor
      (ProgramSuffix.commitCursor suffix)
  env := by
    rw [ProgramSuffix.commitCursor_toProgramCursor_Γ suffix]
    exact view

theorem privateObsOfCursorWorld_eraseEnv
    {g : WFProgram P L}
    (who : P) (w : CursorCheckedWorld g) :
    (privateObsOfCursorWorld who w).env =
      projectViewEnv who (VEnv.eraseEnv w.1.env) := rfl

theorem availableProgramMovesAt_eq_of_privateObs_eq
    (g : WFProgram P L) (who : P)
    (w₁ w₂ : CursorCheckedWorld g)
    (hpriv : privateObsOfCursorWorld who w₁ = privateObsOfCursorWorld who w₂) :
    CursorCheckedWorld.availableProgramMovesAt
        w₁.1.prog w₁.1.env w₁.1.suffix who =
      CursorCheckedWorld.availableProgramMovesAt
        w₂.1.prog w₂.1.env w₂.1.suffix who := by
  rcases w₁ with ⟨⟨c₁, env₁⟩, valid₁⟩
  rcases w₂ with ⟨⟨c₂, env₂⟩, valid₂⟩
  dsimp [privateObsOfCursorWorld] at hpriv ⊢
  injection hpriv with hcursor henv
  cases hcursor
  change CursorCheckedWorld.availableProgramMovesAt
      c₁.prog env₁ c₁.toSuffix who =
    CursorCheckedWorld.availableProgramMovesAt
      c₁.prog env₂ c₁.toSuffix who
  have hview : projectViewEnv who (VEnv.eraseEnv env₁) =
      projectViewEnv who (VEnv.eraseEnv env₂) := eq_of_heq henv
  exact availableProgramMovesAt_eq_of_projectViewEnv_eq
    g who c₁.prog c₁.toSuffix env₁ env₂
    valid₁.1 valid₁.2.1 valid₁.2.2.1 hview

/-- Cursor-keyed observation-preserving FOSG over the program-local action
alphabet.

This is the finite executable FOSG target for program-action strategy and
equilibrium transport. -/
noncomputable def observedProgramFOSG (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    GameTheory.FOSG P (CursorCheckedWorld g)
      (fun who : P => ProgramAction g.prog who)
      (fun who : P => PrivateObs g who)
      (PublicObs g hctx) where
  init := CursorCheckedWorld.initial g hctx
  active := fun w => active w.toWorld
  availableActions := CursorCheckedWorld.availableProgramActions
  terminal := fun w => terminal w.toWorld
  transition := cursorProgramTransition
  reward := rewardOnEnteringRetCursor
  privObs := fun who _ _ w' => privateObsOfCursorWorld who w'
  pubObs := fun _ _ w' => publicObsOfCursorWorld w'
  terminal_active_eq_empty := by
    intro w hterm
    exact cursor_terminal_active_eq_empty hterm
  terminal_no_legal := by
    intro w a hterm
    exact cursor_terminal_no_program_legal hterm
  nonterminal_exists_legal := by
    intro w hterm
    exact cursor_nonterminal_exists_program_legal hterm

theorem observedProgram_availableMovesAtState_eq_of_privateObs_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (w₁ w₂ : CursorCheckedWorld g)
    (hpriv : privateObsOfCursorWorld who w₁ = privateObsOfCursorWorld who w₂) :
    (observedProgramFOSG g hctx).availableMovesAtState w₁ who =
      (observedProgramFOSG g hctx).availableMovesAtState w₂ who := by
  have h :=
    availableProgramMovesAt_eq_of_privateObs_eq
      g who w₁ w₂ hpriv
  ext oi
  have hmem : oi ∈ CursorCheckedWorld.availableProgramMovesAt
        w₁.1.prog w₁.1.env w₁.1.suffix who ↔
      oi ∈ CursorCheckedWorld.availableProgramMovesAt
        w₂.1.prog w₂.1.env w₂.1.suffix who := by
    simp [h]
  cases oi with
  | none =>
      simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.availableProgramMovesAt,
        CursorCheckedWorld.toWorld, active] using hmem
  | some ai =>
      simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.availableProgramMovesAt,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.toWorld, active,
        availableActions] using hmem

/-- The observed-program FOSG transition is the checked transition after
forgetting cursor keys and erasing program-local actions. -/
theorem observedProgramTransition_map_checkedWorld_eq_checkedTransition
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld g)
    (a : (observedProgramFOSG g hctx).LegalAction w) :
    PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
        ((observedProgramFOSG g hctx).transition w a) =
      checkedTransition
        (CheckedWorld.ofCursorChecked (hctx := hctx) w)
        ⟨ProgramJointAction.toAction a.1,
          CursorProgramJointActionLegal.toAction a.2⟩ := by
  simpa [observedProgramFOSG] using
    cursorProgramTransition_map_checkedWorld
      (hctx := hctx) w a


/-- Finite-world helper for `observedProgramFOSG`. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeWorld
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) (LF : FiniteValuation L) :
    Fintype (CursorCheckedWorld g) :=
  CursorCheckedWorld.instFintype g LF

/-- Per-player finite action helper for `observedProgramFOSG`. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeAction
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (who : P) :
    Fintype (ProgramAction g.prog who) :=
  ProgramAction.instFintype LF g.prog who

/-- Per-player optional-action finite helper for FOSG execution APIs. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeOptionAction
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    (who : P) :
    Fintype (Option (ProgramAction g.prog who)) := by
  let _ : Fintype (ProgramAction g.prog who) :=
    observedProgramFOSG.instFintypeAction g hctx LF who
  infer_instance

/-- Terminal decidability helper for FOSG execution APIs. -/
@[reducible] noncomputable def observedProgramFOSG.instDecidablePredTerminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    DecidablePred (observedProgramFOSG g hctx).terminal :=
  Classical.decPred _

/-- Project a cursor-world endpoint to the Vegas payoff outcome it represents.

Only `ret` worlds carry a protocol outcome. The nonterminal branch is a
harmless default used to make this a total projection from FOSG histories. -/
def cursorWorldOutcome
    {g : WFProgram P L}
    (w : CursorCheckedWorld g) : Outcome P :=
  match w.1.prog with
  | .ret payoffs => evalPayoffs payoffs w.1.env
  | _ => 0


end Vegas
