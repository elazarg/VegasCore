import Vegas.FOSG.Basic

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}
/-! ## Observation-preserving target -/

/-- Public observation after a Vegas/FOSG transition: the current public
program cursor together with the public environment. The cursor is public
control-flow metadata and is needed to project a fixed Vegas strategy profile
to the current continuation. -/
structure PublicObs (g : WFProgram P L) (hctx : WFCtx g.Γ) where
  Γ : VCtx P L
  prog : VegasCore P L Γ
  suffix : ProgramSuffix g.prog prog
  env : VEnv L (pubVCtx Γ)

/-- Private observation after a Vegas/FOSG transition: the observing player's
current program cursor and view environment. The cursor is public information,
but storing it here makes the player's local observation self-sufficient for
strategy lookup and action-availability proofs. -/
@[ext]
structure PrivateObs (g : WFProgram P L) (who : P) where
  cursor : ProgramCursor g.prog
  env : ViewEnv who cursor.Γ

def publicObsOfCursorWorld {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld g) : PublicObs g hctx where
  Γ := w.1.cursor.Γ
  prog := w.1.prog
  suffix := w.1.suffix
  env := VEnv.toPub w.1.env

noncomputable def privateObsOfCursorWorld {g : WFProgram P L}
    (who : P) (w : CursorCheckedWorld g) :
    PrivateObs g who where
  cursor := w.1.cursor
  env := projectViewEnv who (VEnv.eraseEnv w.1.env)

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
  active := CursorCheckedWorld.active
  availableActions := CursorCheckedWorld.availableProgramActions
  terminal := CursorCheckedWorld.terminal
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
        CursorCheckedWorld.active, CursorCheckedWorld.toWorld, active] using hmem
  | some ai =>
      simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.availableProgramMovesAt,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt, CursorCheckedWorld.active,
        CursorCheckedWorld.availableActions, CursorCheckedWorld.toWorld, active,
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

/-- Per-player action equality helper for `observedProgramFOSG`. -/
@[reducible] noncomputable def observedProgramFOSG.instDecidableEqAction
    (g : WFProgram P L) (_hctx : WFCtx g.Γ) (who : P) :
    DecidableEq (ProgramAction g.prog who) :=
  ProgramAction.instDecidableEq g.prog who

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

/-- Along any chained realized path in `observedProgramFOSG`, elapsed history
length plus remaining syntax steps is constant. -/
theorem observedProgramFOSG_stepChain_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (w : CursorCheckedWorld g)
    {es : List (observedProgramFOSG g hctx).Step}
    (hchain : (observedProgramFOSG g hctx).StepChainFrom w es) :
    ((observedProgramFOSG g hctx).lastStateFrom w es).remainingSyntaxSteps +
        es.length = w.remainingSyntaxSteps := by
  induction es generalizing w with
  | nil =>
      simp [GameTheory.FOSG.lastStateFrom]
  | cons e es ih =>
      rcases hchain with ⟨hsrc, htail⟩
      subst hsrc
      have hdec :
          e.dst.remainingSyntaxSteps + 1 = e.src.remainingSyntaxSteps := by
        simpa [observedProgramFOSG] using
          cursorProgramTransition_remainingSyntaxSteps
            (g := g)
            e.src e.act e.dst e.support
      have htailInv := ih (w := e.dst) htail
      simp [GameTheory.FOSG.lastStateFrom] at htailInv ⊢
      omega

/-- For every realized history of the cursor-world target, elapsed length plus
remaining syntax steps is the source program's syntax-step bound. -/
theorem observedProgramFOSG_history_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    h.lastState.remainingSyntaxSteps + h.steps.length = syntaxSteps g.prog := by
  simpa [GameTheory.FOSG.History.lastState, observedProgramFOSG,
    CursorCheckedWorld.remainingSyntaxSteps, CursorWorldData.prog] using
    observedProgramFOSG_stepChain_remainingSyntaxSteps
      g hctx (CursorCheckedWorld.initial g hctx) h.chain

/-- The cursor-world observed program FOSG is bounded by the number of
operational syntax nodes in the source Vegas program. -/
theorem observedProgramFOSG_boundedHorizon
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (observedProgramFOSG g hctx).BoundedHorizon (syntaxSteps g.prog) := by
  intro h hlen
  have hinv := observedProgramFOSG_history_remainingSyntaxSteps
    g hctx h
  rw [hlen] at hinv
  have hzero : h.lastState.remainingSyntaxSteps = 0 := by
    omega
  exact (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
    (g := g) (w := h.lastState)).2 hzero

/-- Finite-history helper for the cursor-world observed FOSG. -/
@[reducible] noncomputable def observedProgramFOSG.instFintypeHistory
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] :
    Fintype (observedProgramFOSG g hctx).History := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  exact GameTheory.FOSG.historyFintypeOfBoundedHorizon
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_boundedHorizon g hctx)

/-- The terminal-history law of the observed-program FOSG normalizes. -/
noncomputable def observedProgramFOSG.hasNormalizedTerminalLaw
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    (observedProgramFOSG g hctx).HasNormalizedTerminalLaw := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact GameTheory.FOSG.hasNormalizedTerminalLaw_of_boundedHorizon
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_boundedHorizon g hctx)

/-- The terminal-history `KernelGame` induced by the observed-program FOSG.

This is the native FOSG game, whose outcomes are terminal histories and whose
utilities are cumulative transition rewards. Use
`observedProgramOutcomeKernelGame` for the Vegas-outcome projection. -/
noncomputable def observedProgramTerminalHistoryGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : KernelGame P := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact (observedProgramFOSG g hctx).toKernelGame
    (observedProgramFOSG.hasNormalizedTerminalLaw g hctx LF)

/-- The bounded run distribution of the observed-program FOSG, with the finite
execution instances fixed by `FiniteValuation`. -/
noncomputable def observedProgramRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile) :
    PMF (observedProgramFOSG g hctx).History := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact (observedProgramFOSG g hctx).runDist (syntaxSteps g.prog) σ

/-- Project a cursor-world endpoint to the Vegas payoff outcome it represents.

Only `ret` worlds carry a protocol outcome. The nonterminal branch is a
harmless default used to make this a total projection from FOSG histories;
`observedProgramRunDist_support_terminal` below proves the bounded run assigns
mass only to terminal histories. -/
def cursorWorldOutcome
    {g : WFProgram P L}
    (w : CursorCheckedWorld g) : Outcome P :=
  match w.1.prog with
  | .ret payoffs => evalPayoffs payoffs w.1.env
  | _ => 0

/-- Project a terminal-history outcome from the observed-program FOSG back to
the Vegas payoff outcome carried by its final cursor world. -/
noncomputable def observedProgramHistoryOutcome
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) : Outcome P :=
  cursorWorldOutcome h.lastState

/-- Vegas' denotational outcome kernel for the program suffix represented by a
cursor world. This is the state-local right-hand side for the FOSG
outcome-preservation induction. -/
noncomputable def cursorVegasOutcomeKernel
    {g : WFProgram P L}
    (σ : LegalProgramBehavioralProfile g)
    (w : CursorCheckedWorld g) : PMF (Outcome P) :=
  (outcomeDistBehavioral w.1.prog
      (w.1.suffix.behavioralProfile (fun i => (σ i).val)) w.1.env).toPMF
    (outcomeDistBehavioral_totalWeight_eq_one
      (p := w.1.prog)
      (σ := w.1.suffix.behavioralProfile (fun i => (σ i).val))
      w.2.2.2.2.1)

@[simp] theorem cursorVegasOutcomeKernel_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    cursorVegasOutcomeKernel σ
        (CursorCheckedWorld.initial g hctx) =
      (toKernelGame g).outcomeKernel σ := by
  rfl

theorem cursorVegasOutcomeKernel_terminal
    {g : WFProgram P L}
    (σ : LegalProgramBehavioralProfile g)
    (w : CursorCheckedWorld g)
    (hterm : w.terminal) :
    cursorVegasOutcomeKernel σ w =
      PMF.pure (cursorWorldOutcome w) := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          cases hprog : cursor.prog with
          | ret payoffs =>
              have hout :
                  outcomeDistBehavioral cursor.prog
                      (cursor.toSuffix.behavioralProfile (fun i => (σ i).val)) env =
                    FDist.pure (evalPayoffs payoffs env) :=
                outcomeDistBehavioral_of_eq_ret
                  hprog
                  (cursor.toSuffix.behavioralProfile (fun i => (σ i).val)) env
              apply PMF.ext
              intro o
              unfold cursorVegasOutcomeKernel cursorWorldOutcome
              simp only [CursorWorldData.prog, CursorWorldData.suffix, Subtype.coe_mk]
              rw [FDist.toPMF_apply]
              have hpoint :
                  (outcomeDistBehavioral cursor.prog
                      (cursor.toSuffix.behavioralProfile (fun i => (σ i).val)) env) o =
                    (FDist.pure (evalPayoffs payoffs env)) o := by
                rw [hout]
              rw [hpoint]
              by_cases ho : o = evalPayoffs payoffs env
              · subst o
                simp [hprog, FDist.pure_apply, NNRat.toNNReal_one]
              · have hne : evalPayoffs payoffs env ≠ o := fun h => ho h.symm
                simp [hprog, FDist.pure_apply, ho, hne, NNRat.toNNReal_zero]
          | letExpr x e k =>
              simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog] at hterm
          | sample x D k =>
              simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog] at hterm
          | commit x who R k =>
              simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog] at hterm
          | reveal y who x hx k =>
              simp [CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
                CursorWorldData.prog, terminal, hprog] at hterm

/-- The bounded observed-program run distribution supports only terminal
histories, so the default branch in `observedProgramHistoryOutcome` is
irrelevant for realized outcomes. -/
theorem observedProgramRunDist_support_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    {h : (observedProgramFOSG g hctx).History}
    (hh : h ∈ (observedProgramRunDist g hctx LF σ).support) :
    (observedProgramFOSG g hctx).terminal h.lastState := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact GameTheory.FOSG.runDist_support_isTerminal_of_boundedHorizon
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_boundedHorizon g hctx)
    σ h (by simpa [observedProgramRunDist] using hh)

/-- `runDistFrom` for the observed-program FOSG, with the finite execution
instances supplied by `FiniteValuation`. -/
noncomputable def observedProgramRunDistFrom
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (n : Nat) (h : (observedProgramFOSG g hctx).History) :
    PMF (observedProgramFOSG g hctx).History := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact GameTheory.FOSG.History.runDistFrom
    (observedProgramFOSG g hctx) σ n h

@[simp] theorem observedProgramRunDist_eq_runDistFrom_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile) :
    observedProgramRunDist g hctx LF σ =
      observedProgramRunDistFrom g hctx LF σ
        (syntaxSteps g.prog)
        (GameTheory.FOSG.History.nil
          (observedProgramFOSG g hctx)) := by
  rfl

/-- Once an observed-program FOSG history is terminal, any remaining bounded
run horizon maps to the point mass at its projected Vegas outcome. -/
theorem observedProgramRunDistFrom_historyOutcome_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : (observedProgramFOSG g hctx).terminal h.lastState) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDistFrom g hctx LF σ n h) =
      PMF.pure (observedProgramHistoryOutcome g hctx h) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_terminal
    (G := observedProgramFOSG g hctx) σ n h hterm]
  rw [PMF.pure_map]

/-- Projected one-step run equation at empty-active observed-program states.
This is the common FOSG-side reduction for Vegas `let`, `sample`, and
`reveal` nodes. -/
theorem observedProgramRunDistFrom_historyOutcome_succ_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState)
    (hactive : (observedProgramFOSG g hctx).active h.lastState = ∅) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDistFrom g hctx LF σ (n + 1) h) =
      ((observedProgramFOSG g hctx).transition h.lastState
          ⟨GameTheory.FOSG.noopAction
              (fun who : P => ProgramAction g.prog who),
            (observedProgramFOSG g hctx)
              |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩).bind
        (fun dst =>
          PMF.map (observedProgramHistoryOutcome g hctx)
            (observedProgramRunDistFrom g hctx LF σ n
              (h.extendByOutcome
                ⟨GameTheory.FOSG.noopAction
                    (fun who : P => ProgramAction g.prog who),
                  (observedProgramFOSG g hctx)
                    |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩
                dst))) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_succ_active_empty
    (G := observedProgramFOSG g hctx) σ n h hterm hactive]
  rw [PMF.map_bind]

end FOSGBridge
end Vegas
