import GameTheory.Languages.FOSG.OutcomeClosure
import Vegas.Syntax.Cursor.Pure
import Vegas.Syntax.Strategy.PMFSemantics

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## Projected outcome kernel

GameTheory's generic FOSG compiler uses terminal histories as kernel-game
outcomes. For Vegas, the semantic comparison is the pushforward of that
history distribution along `observedProgramHistoryOutcome`. -/

noncomputable def checkedVegasOutcomeKernelPMF
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) : PMF (Outcome P) :=
  behavioralOutcomePMF w.prog w.normalized
    (w.suffix.behavioralProfilePMF (fun i => (σ i).val)) w.env

/-- Vegas' denotational outcome kernel at the finite cursor world. This is the
cursor-native value used by the observed-program FOSG outcome proof. -/
noncomputable def cursorVegasOutcomeKernelPMF
    {g : WFProgram P L}
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CursorCheckedWorld g) : PMF (Outcome P) :=
  behavioralOutcomePMF w.1.prog w.2.2.2.2.1
    (w.1.suffix.behavioralProfilePMF (fun i => (σ i).val)) w.1.env

noncomputable def checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) : PMF (CheckedWorld g hctx) := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact PMF.pure
            { Γ := Γ
              prog := .ret payoffs
              env := env
              suffix := suffix
              wctx := wctx
              fresh := fresh
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }
      | letExpr x e k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                (L.eval e (VEnv.erasePubEnv env)) env
              suffix := .letExpr suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }
      | sample x D k =>
          exact PMF.map
            (fun v =>
              { Γ := _
                prog := k
                env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                  v env
                suffix := .sample suffix
                wctx := WFCtx.cons fresh.1 wctx
                fresh := fresh.2
                viewScoped := viewScoped
                normalized := normalized.2
                legal := legal })
            ((L.evalDist D (VEnv.eraseSampleEnv env)).toPMF (normalized.1 env))
      | commit x who R k =>
          let σp : ProgramBehavioralProfilePMF
              (.commit x who R k) :=
            suffix.behavioralProfilePMF (fun i => (σ i).val)
          exact PMF.map
            (fun v =>
              { Γ := _
                prog := k
                env := VEnv.cons (Player := P) (L := L) (x := x)
                  (τ := .hidden who _) v env
                suffix := .commit suffix
                wctx := WFCtx.cons fresh.1 wctx
                fresh := fresh.2
                viewScoped := viewScoped.2
                normalized := normalized
                legal := legal.2 })
            (ProgramBehavioralStrategyPMF.headKernel (σp who)
             (projectViewEnv who (VEnv.eraseEnv env)))
      | reveal y who x hx k =>
          exact PMF.pure
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub _)
                (env x (.hidden who _) hx) env
              suffix := .reveal suffix
              wctx := WFCtx.cons fresh.1 wctx
              fresh := fresh.2
              viewScoped := viewScoped
              normalized := normalized
              legal := legal }

/-- Checked-world continuation induced by an optional program action at a
concrete Vegas commit node.  Legal FOSG actions always take the `some` branch
with the current commit cursor; the fallback branches make the continuation
total so it can be used under unconstrained PMF binds. -/
noncomputable def checkedCommitContinuation
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (wctx : WFCtx Γ) (fresh : FreshBindings (.commit x who R k))
    (viewScoped : ViewScoped (.commit x who R k))
    (normalized : NormalizedDists (.commit x who R k))
    (legal : Legal (.commit x who R k))
    (oi : Option (ProgramAction g.prog who)) :
    PMF (CheckedWorld g hctx) :=
  match oi with
  | some ai =>
      if hty : CommitCursor.ty ai.cursor = b then
        PMF.pure
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _) (hty ▸ ai.value) env
             suffix := .commit suffix
             wctx := WFCtx.cons fresh.1 wctx
             fresh := fresh.2
             viewScoped := viewScoped.2
             normalized := normalized
             legal := legal.2 } : CheckedWorld g hctx)
      else
        PMF.pure
          ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
             wctx := wctx, fresh := fresh, viewScoped := viewScoped,
             normalized := normalized, legal := legal } : CheckedWorld g hctx)
  | none =>
      PMF.pure
        ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
           wctx := wctx, fresh := fresh, viewScoped := viewScoped,
           normalized := normalized, legal := legal } : CheckedWorld g hctx)

theorem moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (wctx : WFCtx Γ) (fresh : FreshBindings (.commit x who R k))
    (viewScoped : ViewScoped (.commit x who R k))
    (normalized : NormalizedDists (.commit x who R k))
    (legal : Legal (.commit x who R k)) :
    (moveAtProgramCursorPMF g hctx σ who suffix
        (projectViewEnv who (VEnv.eraseEnv env))).bind
      (checkedCommitContinuation g hctx env suffix wctx fresh viewScoped
        normalized legal) =
      checkedProfileStepPMF g hctx σ
        ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
           wctx := wctx, fresh := fresh, viewScoped := viewScoped,
           normalized := normalized, legal := legal } : CheckedWorld g hctx) := by
  rw [moveAtProgramCursorPMF_commit_owner]
  rw [PMF.bind_map]
  simp only [checkedProfileStepPMF, Function.comp_def]
  have hbind := bind_congr (m := PMF)
    (x := (ProgramBehavioralStrategyPMF.headKernel
          ((suffix.behavioralProfilePMF (fun i => ↑(σ i))) who)
          (projectViewEnv who env.eraseEnv)))
    (f := fun v =>
      if hty : (ProgramAction.commitAt suffix v).cursor.ty = b then
        PMF.pure
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _)
               (hty ▸ (ProgramAction.commitAt suffix v).value) env
             suffix := .commit suffix
             wctx := WFCtx.cons fresh.1 wctx
             fresh := fresh.2
             viewScoped := viewScoped.2
             normalized := normalized
             legal := legal.2 } : CheckedWorld g hctx)
      else
        PMF.pure
          ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
             wctx := wctx, fresh := fresh, viewScoped := viewScoped,
             normalized := normalized, legal := legal } : CheckedWorld g hctx))
    (g := fun v => PMF.pure
      ({ Γ := _
         prog := k
         env := VEnv.cons (Player := P) (L := L) (x := x)
           (τ := .hidden who _) v env
         suffix := .commit suffix
         wctx := WFCtx.cons fresh.1 wctx
         fresh := fresh.2
         viewScoped := viewScoped.2
         normalized := normalized
         legal := legal.2 } : CheckedWorld g hctx)) ?_
  · simpa [PMF.bind_pure_comp, Function.comp_def] using hbind
  · intro v
    by_cases hty : (ProgramAction.commitAt suffix v).cursor.ty = b
    · dsimp only
      rw [dif_pos hty]
      have hv :
          hty ▸ (ProgramAction.commitAt suffix v).value = v :=
        ProgramAction.commitAt_value_cast suffix v hty
      have henv :
          VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who _)
              (hty ▸ (ProgramAction.commitAt suffix v).value) env =
            VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who _) v env :=
        VEnv.cons_ext hv rfl
      rw [henv]
    · exact False.elim
        (hty (ProgramSuffix.ty_commitCursor suffix))
theorem checkedTransition_eq_checkedProfileStepPMF_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (hactive : active w.toWorld = ∅) :
    checkedTransition w a =
      checkedProfileStepPMF g hctx σ w := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim
            (a.2.1 (by simp [terminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          simp [checkedTransition, checkedProfileStepPMF]
      | sample x D k =>
          simp [checkedTransition, checkedProfileStepPMF]
      | commit x who R k =>
          simp [active, CheckedWorld.toWorld, active] at hactive
      | reveal y who x hx k =>
          simp [checkedTransition, checkedProfileStepPMF]


/-- If a player is active in the observed-program FOSG, the cursor endpoint is
a commit node owned by that player, and all checked-world projections expose
the same commit data. -/
theorem cursorFOSG_active_mem_commitData
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (w : CursorCheckedWorld g)
    {who : P}
    (hmem : who ∈
      (cursorFOSG g hctx).active w) :
    ∃ (Γ : VCtx P L) (x : VarId) (b : L.Ty)
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (k : VegasCore P L ((x, .hidden who b) :: Γ))
      (env : VEnv L Γ)
      (suffix : ProgramSuffix g.prog
        (.commit x who R k))
      (wctx : WFCtx Γ)
      (fresh : FreshBindings (.commit x who R k))
      (viewScoped : ViewScoped (.commit x who R k))
      (normalized : NormalizedDists (.commit x who R k))
      (legal : Legal (.commit x who R k)),
      CheckedWorld.ofCursorChecked (hctx := hctx) w =
        ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
           wctx := wctx, fresh := fresh, viewScoped := viewScoped,
           normalized := normalized, legal := legal } : CheckedWorld g hctx) ∧
      w.toWorld =
        ({ Γ := Γ, prog := .commit x who R k, env := env } : World P L) ∧
      privateObsOfCursorWorld who w =
        privateObsOfCommitSite suffix
          (projectViewEnv who (VEnv.eraseEnv env)) := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          rcases valid with ⟨wctx, fresh, viewScoped, normalized, legal⟩
          cases hprog : cursor.prog with
          | ret payoffs =>
              simp [cursorFOSG, active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | letExpr x e k =>
              simp [cursorFOSG, active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | sample x D k =>
              simp [cursorFOSG, active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | reveal y owner x hx k =>
              simp [cursorFOSG, active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | commit x owner R k =>
              have hwho : who = owner := by
                simpa [cursorFOSG, active,
                  CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                  hprog] using hmem
              subst who
              let suffix : ProgramSuffix g.prog
                  (VegasCore.commit x owner R k) :=
                hprog ▸ cursor.toSuffix
              refine ⟨cursor.Γ, x, _, R, k, env, suffix, wctx, ?_, ?_,
                ?_, ?_, ?_, ?_⟩
              · simpa [CursorWorldData.prog, hprog] using fresh
              · simpa [CursorWorldData.prog, hprog] using viewScoped
              · simpa [CursorWorldData.prog, hprog] using normalized
              · simpa [CursorWorldData.prog, hprog] using legal
              · simp [CheckedWorld.ofCursorChecked, CursorWorldData.prog,
                  CursorWorldData.suffix, suffix, hprog]
              · constructor
                · simp [CursorCheckedWorld.toWorld, CursorWorldData.prog, hprog]
                · dsimp [privateObsOfCursorWorld, privateObsOfCommitSite,
                    suffix]
                  apply PrivateObs.ext
                  · apply ProgramCursor.eq_of_path_eq
                    have hsuffixPath :
                        suffix.path = cursor.toSuffix.path := by
                      dsimp [suffix]
                      exact ProgramSuffix.path_cast hprog cursor.toSuffix
                    calc
                      cursor.path = cursor.toSuffix.path := by
                        rw [ProgramCursor.path_toSuffix]
                      _ = suffix.path := hsuffixPath.symm
                      _ =
                          (ProgramCursor.CommitCursor.toProgramCursor
                            (ProgramSuffix.commitCursor suffix)).path := by
                            rw [ProgramCursor.path_toProgramCursor_commitCursor]
                  · exact (cast_heq _ _).symm


/-- Project a suffix-based checked world to the Vegas payoff outcome carried at
terminal `ret` worlds. The nonterminal branch is a total-function default;
support lemmas below prove it is irrelevant once the semantic run has enough
horizon. -/
def checkedWorldOutcome
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CheckedWorld g hctx) : Outcome P :=
  match w.prog with
  | .ret payoffs => evalPayoffs payoffs w.env
  | _ => 0

theorem checkedVegasOutcomeKernelPMF_terminal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx)
    (hterm : terminal w.toWorld) :
    checkedVegasOutcomeKernelPMF σ w =
      PMF.pure (checkedWorldOutcome w) := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedVegasOutcomeKernelPMF, checkedWorldOutcome,
            behavioralOutcomePMF]
      | letExpr x e k =>
          simp [terminal, CheckedWorld.toWorld, terminal] at hterm
      | sample x D k =>
          simp [terminal, CheckedWorld.toWorld, terminal] at hterm
      | commit x who R k =>
          simp [terminal, CheckedWorld.toWorld, terminal] at hterm
      | reveal y who x hx k =>
          simp [terminal, CheckedWorld.toWorld, terminal] at hterm

theorem checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) :
    (checkedProfileStepPMF g hctx σ w).bind
        (checkedVegasOutcomeKernelPMF σ) =
      checkedVegasOutcomeKernelPMF σ w := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            behavioralOutcomePMF]
      | letExpr x e k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            behavioralOutcomePMF, PMF.pure_bind]
          rw [show
              (ProgramSuffix.letExpr suffix).behavioralProfilePMF
                  (fun i => (σ i).val) =
                (fun w =>
                  match suffix.behavioralProfilePMF
                      (fun i => (σ i).val) w with
                  | .letExpr tail => tail) by
            funext w
            exact ProgramSuffix.behavioralProfilePMF_letExpr
              suffix (fun i => (σ i).val) w]
          rfl
      | sample x D k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            behavioralOutcomePMF]
          rw [PMF.bind_map]
          rfl
      | commit x who R k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            behavioralOutcomePMF]
          rw [PMF.bind_map]
          rfl
      | reveal y who x hx k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            behavioralOutcomePMF, PMF.pure_bind]
          rw [show
              (ProgramSuffix.reveal suffix).behavioralProfilePMF
                  (fun i => (σ i).val) =
                (fun w =>
                  match suffix.behavioralProfilePMF
                      (fun i => (σ i).val) w with
                  | .reveal tail => tail) by
            funext w
            exact ProgramSuffix.behavioralProfilePMF_reveal
              suffix (fun i => (σ i).val) w]
          simp [VEnv.get]
          rfl

@[simp] theorem checkedVegasOutcomeKernelPMF_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CursorCheckedWorld g) :
    checkedVegasOutcomeKernelPMF (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      cursorVegasOutcomeKernelPMF σ w := rfl

@[simp] theorem checkedWorldOutcome_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld g) :
    checkedWorldOutcome
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      cursorWorldOutcome w := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          cases hprog : cursor.prog <;>
            simp [CheckedWorld.ofCursorChecked, checkedWorldOutcome,
              cursorWorldOutcome, CursorWorldData.prog, hprog]

theorem cursorVegasOutcomeKernelPMF_terminal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : FeasibleProgramBehavioralProfilePMF g)
    (w : CursorCheckedWorld g)
    (hterm : terminal w.toWorld) :
    cursorVegasOutcomeKernelPMF σ w =
      PMF.pure (cursorWorldOutcome w) := by
  have hchecked :
      terminal
        (CheckedWorld.ofCursorChecked (hctx := hctx) w).toWorld := by
    simpa [terminal, CheckedWorld.ofCursorChecked,
      terminal, CursorCheckedWorld.toWorld,
      CheckedWorld.toWorld] using hterm
  rw [← checkedVegasOutcomeKernelPMF_ofCursorChecked (hctx := hctx) σ w]
  rw [← checkedWorldOutcome_ofCursorChecked (hctx := hctx) w]
  exact checkedVegasOutcomeKernelPMF_terminal
    (hctx := hctx) σ (CheckedWorld.ofCursorChecked (hctx := hctx) w)
    hchecked



end Vegas
