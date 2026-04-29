import Vegas.FOSG.Observed.Pure

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed
/-! ## Projected outcome kernel

GameTheory's generic FOSG compiler uses terminal histories as kernel-game
outcomes. For Vegas, the semantic comparison is the pushforward of that
history distribution along `observedProgramHistoryOutcome`. -/

/-- Vegas' denotational outcome kernel at a suffix-based checked world. This
is the natural semantic target for the preservation proof: the current Vegas
program is exposed directly, so the proof proceeds by ordinary cases on
`w.prog` rather than by induction through a finite cursor encoding. -/
noncomputable def checkedVegasOutcomeKernel
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx) : PMF (Outcome P) :=
  (outcomeDistBehavioral w.prog
      (w.suffix.behavioralProfile (fun i => (σ i).val)) w.env).toPMF
    (outcomeDistBehavioral_totalWeight_eq_one
      (p := w.prog)
      (σ := w.suffix.behavioralProfile (fun i => (σ i).val))
      w.normalized)

noncomputable def checkedVegasOutcomeKernelPMF
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) : PMF (Outcome P) :=
  outcomeDistBehavioralPMF w.prog w.normalized
    (w.suffix.behavioralProfilePMF (fun i => (σ i).val)) w.env

/-- Vegas' own profile-induced one-step kernel on suffix-based checked worlds.
This is the semantic small-step machine. It is intentionally independent of
FOSG's joint-action representation; commit nodes bind directly over the active
player's Vegas strategy kernel. -/
noncomputable def checkedProfileStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
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
          let σp : ProgramBehavioralProfile
              (.commit x who R k) :=
            suffix.behavioralProfile (fun i => (σ i).val)
          let d := ProgramBehavioralStrategy.headKernel
            (σp who) (projectViewEnv who (VEnv.eraseEnv env))
          have hd : FDist.totalWeight d = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              (σp who)
              (projectViewEnv who (VEnv.eraseEnv env))
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
            (d.toPMF hd)
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

noncomputable def checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
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

/-- At a commit cursor owned by `who`, binding the transported program-action
kernel through the checked transition's commit continuation is exactly the
Vegas profile step at that checked world. -/
theorem moveAtProgramCursor_bind_commitContinuation_eq_checkedProfileStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (env : VEnv L Γ)
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (wctx : WFCtx Γ) (fresh : FreshBindings (.commit x who R k))
    (viewScoped : ViewScoped (.commit x who R k))
    (normalized : NormalizedDists (.commit x who R k))
    (legal : Legal (.commit x who R k)) :
    (moveAtProgramCursor g hctx σ who suffix
        (projectViewEnv who (VEnv.eraseEnv env))).bind
      (fun oi =>
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
                 normalized := normalized, legal := legal } : CheckedWorld g hctx)) =
      checkedProfileStep g hctx σ
        ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
           wctx := wctx, fresh := fresh, viewScoped := viewScoped,
           normalized := normalized, legal := legal } : CheckedWorld g hctx) := by
  rw [moveAtProgramCursor_commit_owner]
  rw [PMF.bind_map]
  simp only [checkedProfileStep, Function.comp_def]
  have hbind := bind_congr (m := PMF)
    (x := (((suffix.behavioralProfile (fun i => ↑(σ i)) who).headKernel
      (projectViewEnv who env.eraseEnv)).toPMF
        (ProgramBehavioralStrategy.headKernel_normalized
          ((suffix.behavioralProfile (fun i => ↑(σ i))) who)
          (projectViewEnv who env.eraseEnv))))
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

theorem moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
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
      (fun oi =>
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
                 normalized := normalized, legal := legal } : CheckedWorld g hctx)) =
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



theorem checkedTransition_eq_checkedProfileStep_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (hactive : checkedActive w = ∅) :
    checkedTransition w a =
      checkedProfileStep g hctx σ w := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim
            (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          simp [checkedTransition, checkedProfileStep]
      | sample x D k =>
          simp [checkedTransition, checkedProfileStep]
      | commit x who R k =>
          simp [checkedActive, CheckedWorld.toWorld, active] at hactive
      | reveal y who x hx k =>
          simp [checkedTransition, checkedProfileStep]

theorem checkedTransition_eq_checkedProfileStepPMF_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (hactive : checkedActive w = ∅) :
    checkedTransition w a =
      checkedProfileStepPMF g hctx σ w := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          exact False.elim
            (a.2.1 (by simp [checkedTerminal, CheckedWorld.toWorld, terminal]))
      | letExpr x e k =>
          simp [checkedTransition, checkedProfileStepPMF]
      | sample x D k =>
          simp [checkedTransition, checkedProfileStepPMF]
      | commit x who R k =>
          simp [checkedActive, CheckedWorld.toWorld, active] at hactive
      | reveal y who x hx k =>
          simp [checkedTransition, checkedProfileStepPMF]

/-- At an observed-program history with no active players, the FOSG
legal-action law followed by the checked-world transition is the Vegas
small-step kernel. This discharges the `let`, `sample`, and `reveal` one-step
cases; commit states are handled separately by their singleton active player. -/
theorem observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState)
    (hactive :
      (observedProgramFOSG g hctx).active h.lastState = ∅) :
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition
            h.lastState a)) =
      checkedProfileStep g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          h.lastState) := by
  rw [GameTheory.FOSG.legalActionLaw_eq_pure_noop_of_active_empty
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm hactive]
  simp only [PMF.pure_bind]
  rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
    (hctx := hctx)
    (w := h.lastState)
    (a := ⟨GameTheory.FOSG.noopAction
        (fun who : P => ProgramAction g.prog who),
      (observedProgramFOSG g hctx)
        |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩)]
  apply checkedTransition_eq_checkedProfileStep_of_active_empty
  simpa [observedProgramFOSG, checkedActive, CheckedWorld.ofCursorChecked,
    CursorCheckedWorld.active] using hactive

theorem
    observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfilePMF g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState)
    (hactive :
      (observedProgramFOSG g hctx).active h.lastState = ∅) :
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition
            h.lastState a)) =
      checkedProfileStepPMF g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          h.lastState) := by
  rw [GameTheory.FOSG.legalActionLaw_eq_pure_noop_of_active_empty
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm hactive]
  simp only [PMF.pure_bind]
  rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
    (hctx := hctx)
    (w := h.lastState)
    (a := ⟨GameTheory.FOSG.noopAction
        (fun who : P => ProgramAction g.prog who),
      (observedProgramFOSG g hctx)
        |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩)]
  apply checkedTransition_eq_checkedProfileStepPMF_of_active_empty
  simpa [observedProgramFOSG, checkedActive, CheckedWorld.ofCursorChecked,
    CursorCheckedWorld.active] using hactive

/-- If a player is active in the observed-program FOSG, the cursor endpoint is
a commit node owned by that player, and all checked-world projections expose
the same commit data. -/
theorem observedProgram_active_mem_commitData
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (w : CursorCheckedWorld g)
    {who : P}
    (hmem : who ∈
      (observedProgramFOSG g hctx).active w) :
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
        ({ Γ := Γ, prog := .commit x who R k, env := env } : World P L) := by
  cases w with
  | mk data valid =>
      cases data with
      | mk cursor env =>
          rcases valid with ⟨wctx, fresh, viewScoped, normalized, legal⟩
          cases hprog : cursor.prog with
          | ret payoffs =>
              simp [observedProgramFOSG, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | letExpr x e k =>
              simp [observedProgramFOSG, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | sample x D k =>
              simp [observedProgramFOSG, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | reveal y owner x hx k =>
              simp [observedProgramFOSG, CursorCheckedWorld.active,
                CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                hprog] at hmem
          | commit x owner R k =>
              have hwho : who = owner := by
                simpa [observedProgramFOSG, CursorCheckedWorld.active,
                  CursorCheckedWorld.toWorld, CursorWorldData.prog, active,
                  hprog] using hmem
              subst who
              let suffix : ProgramSuffix g.prog
                  (VegasCore.commit x owner R k) :=
                by
                  rw [← hprog]
                  exact cursor.toSuffix
              refine ⟨cursor.Γ, x, _, R, k, env, suffix, wctx, ?_, ?_,
                ?_, ?_, ?_, ?_⟩
              · simpa [CursorWorldData.prog, hprog] using fresh
              · simpa [CursorWorldData.prog, hprog] using viewScoped
              · simpa [CursorWorldData.prog, hprog] using normalized
              · simpa [CursorWorldData.prog, hprog] using legal
              · simp [CheckedWorld.ofCursorChecked, CursorWorldData.prog,
                  CursorWorldData.suffix, suffix, hprog]
              · simp [CursorCheckedWorld.toWorld, CursorWorldData.prog, hprog]

/-- One observed-program FOSG execution step, projected to checked worlds,
coincides with the Vegas semantic one-step kernel. -/
theorem observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition
            h.lastState a)) =
      checkedProfileStep g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          h.lastState) := by
  let G := observedProgramFOSG g hctx
  by_cases hactive : G.active h.lastState = ∅
  · exact observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep_of_active_empty
      g hctx σ h hterm hactive
  · have hne : (G.active h.lastState).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    rcases hne with ⟨who, hmem⟩
    rcases observedProgram_active_mem_commitData
        g hctx h.lastState hmem with
      ⟨Γ, x, b, R, k, env, suffix, wctx, fresh, viewScoped,
        normalized, legal, hchecked, hworld⟩
    let f : Option (ProgramAction g.prog who) →
        PMF (CheckedWorld g hctx) := fun oi =>
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
    have hK : ∀ a : G.LegalAction h.lastState,
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          (G.transition h.lastState a) = f (a.1 who) := by
      intro a
      rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
        (hctx := hctx) (w := h.lastState) (a := a)]
      have haRaw : JointActionLegal
          ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
          (ProgramJointAction.toAction a.1) := by
        have hto := CursorProgramJointActionLegal.toAction a.2
        simpa [hworld] using hto
      rw [checkedTransition_congr_checkedWorld
        (hw := hchecked)
        (a := ProgramJointAction.toAction a.1)
        (ha₂ := by
          simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
            checkedAvailableActions, CheckedWorld.toWorld] using haRaw)]
      simpa [f] using
        checkedTransition_commit_eq_programActionContinuation
          g hctx env suffix wctx fresh viewScoped
          normalized legal a.1 haRaw
    calc
      ((observedProgramFOSG g hctx).legalActionLaw
          (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
        (fun a =>
          PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
            ((observedProgramFOSG g hctx).transition
              h.lastState a))
          = ((observedProgramFOSG g hctx).legalActionLaw
              (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
              (fun a => f (a.1 who)) := by
                congr
                funext a
                exact hK a
      _ = (moveAtCursorWorld g hctx σ who h.lastState).bind f := by
        exact observedProgramLegalActionLaw_bind_coord
          g hctx σ h hterm who f
      _ = checkedProfileStep g hctx σ
          (CheckedWorld.ofCursorChecked (hctx := hctx)
            h.lastState) := by
        rw [← moveAtCheckedWorld_ofCursorChecked
          g hctx σ who h.lastState]
        rw [hchecked]
        exact moveAtProgramCursor_bind_commitContinuation_eq_checkedProfileStep
          g hctx σ env suffix wctx fresh viewScoped
          normalized legal

theorem observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfilePMF g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition
            h.lastState a)) =
      checkedProfileStepPMF g hctx σ
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          h.lastState) := by
  let G := observedProgramFOSG g hctx
  by_cases hactive : G.active h.lastState = ∅
  · exact observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF_empty
      g hctx σ h hterm hactive
  · have hne : (G.active h.lastState).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    rcases hne with ⟨who, hmem⟩
    rcases observedProgram_active_mem_commitData
        g hctx h.lastState hmem with
      ⟨Γ, x, b, R, k, env, suffix, wctx, fresh, viewScoped,
        normalized, legal, hchecked, hworld⟩
    let f : Option (ProgramAction g.prog who) →
        PMF (CheckedWorld g hctx) := fun oi =>
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
    have hK : ∀ a : G.LegalAction h.lastState,
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          (G.transition h.lastState a) = f (a.1 who) := by
      intro a
      rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
        (hctx := hctx) (w := h.lastState) (a := a)]
      have haRaw : JointActionLegal
          ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
          (ProgramJointAction.toAction a.1) := by
        have hto := CursorProgramJointActionLegal.toAction a.2
        simpa [hworld] using hto
      rw [checkedTransition_congr_checkedWorld
        (hw := hchecked)
        (a := ProgramJointAction.toAction a.1)
        (ha₂ := by
          simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
            checkedAvailableActions, CheckedWorld.toWorld] using haRaw)]
      simpa [f] using
        checkedTransition_commit_eq_programActionContinuation
          g hctx env suffix wctx fresh viewScoped
          normalized legal a.1 haRaw
    calc
      ((observedProgramFOSG g hctx).legalActionLaw
          (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm).bind
        (fun a =>
          PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
            ((observedProgramFOSG g hctx).transition
              h.lastState a))
          = ((observedProgramFOSG g hctx).legalActionLaw
              (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm).bind
              (fun a => f (a.1 who)) := by
                congr
                funext a
                exact hK a
      _ = (moveAtCursorWorldPMF g hctx σ who h.lastState).bind f := by
        exact observedProgramLegalActionLawPMF_bind_coord
          g hctx σ h hterm who f
      _ = checkedProfileStepPMF g hctx σ
          (CheckedWorld.ofCursorChecked (hctx := hctx)
            h.lastState) := by
        rw [← moveAtCheckedWorldPMF_ofCursorChecked
          g hctx σ who h.lastState]
        rw [hchecked]
        exact moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
          g hctx σ env suffix wctx fresh viewScoped
          normalized legal

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

/-- At terminal checked worlds, the denotational kernel is exactly the point
mass at the world's payoff outcome. -/
theorem checkedVegasOutcomeKernel_terminal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedVegasOutcomeKernel σ w =
      PMF.pure (checkedWorldOutcome w) := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedVegasOutcomeKernel, checkedWorldOutcome,
            outcomeDistBehavioral, FDist.toPMF_pure]
      | letExpr x e k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | sample x D k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | commit x who R k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | reveal y who x hx k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm

theorem checkedVegasOutcomeKernelPMF_terminal
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedVegasOutcomeKernelPMF σ w =
      PMF.pure (checkedWorldOutcome w) := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedVegasOutcomeKernelPMF, checkedWorldOutcome,
            outcomeDistBehavioralPMF]
      | letExpr x e k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | sample x D k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | commit x who R k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | reveal y who x hx k =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm

/-- One semantic small step preserves the remaining Vegas denotation. This is
the hard preservation equation in the proof architecture; it is proved at the
suffix-based machine level before involving the finite FOSG cursor encoding. -/
theorem checkedProfileStep_bind_checkedVegasOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx) :
    (checkedProfileStep g hctx σ w).bind
        (checkedVegasOutcomeKernel σ) =
      checkedVegasOutcomeKernel σ w := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral]
      | letExpr x e k =>
          simp [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral]
      | sample x D k =>
          simp only [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral]
          rw [PMF.bind_map]
          change
            ((L.evalDist D (VEnv.eraseSampleEnv env)).toPMF
                (normalized.1 env)).bind
              (fun v =>
                (outcomeDistBehavioral k
                    (suffix.behavioralProfile (fun i => (σ i).val))
                    (VEnv.cons (Player := P) (L := L) (x := x)
                      (τ := .pub _) v env)).toPMF
                  (outcomeDistBehavioral_totalWeight_eq_one
                    (p := k)
                    (σ := suffix.behavioralProfile (fun i => (σ i).val))
                    normalized.2)) =
              ((L.evalDist D (VEnv.eraseSampleEnv env)).bind fun v =>
                outcomeDistBehavioral k
                  (suffix.behavioralProfile (fun i => (σ i).val))
                  (VEnv.cons (Player := P) (L := L) (x := x)
                    (τ := .pub _) v env)).toPMF
                (outcomeDistBehavioral_totalWeight_eq_one
                  (p := VegasCore.sample x D k)
                  (σ := suffix.behavioralProfile (fun i => (σ i).val))
                  ⟨normalized.1, normalized.2⟩)
          rw [← FDist.toPMF_bind
            (L.evalDist D (VEnv.eraseSampleEnv env))
            (fun v =>
              outcomeDistBehavioral k
                (suffix.behavioralProfile (fun i => (σ i).val))
                (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                  v env))
            (normalized.1 env)
            (fun v =>
              outcomeDistBehavioral_totalWeight_eq_one
                (p := k)
                (σ := suffix.behavioralProfile (fun i => (σ i).val))
                normalized.2)
            (outcomeDistBehavioral_totalWeight_eq_one
              (p := VegasCore.sample x D k)
              (σ := suffix.behavioralProfile (fun i => (σ i).val))
              ⟨normalized.1, normalized.2⟩)]
      | commit x who R k =>
          simp only [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral]
          rw [PMF.bind_map]
          have hd :
              FDist.totalWeight
                (ProgramBehavioralStrategy.headKernel
                  ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                  (projectViewEnv who
                    (VEnv.eraseEnv env))) = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              ((suffix.behavioralProfile (fun i => (σ i).val)) who)
              (projectViewEnv who (VEnv.eraseEnv env))
          change
            ((ProgramBehavioralStrategy.headKernel
                ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                (projectViewEnv who
                  (VEnv.eraseEnv env))).toPMF hd).bind
              (fun v =>
                (outcomeDistBehavioral k
                    (ProgramBehavioralProfile.tail
                      (suffix.behavioralProfile (fun i => (σ i).val)))
                    (VEnv.cons (Player := P) (L := L) (x := x)
                      (τ := .hidden who _) v env)).toPMF
                  (outcomeDistBehavioral_totalWeight_eq_one
                    (p := k)
                    (σ := ProgramBehavioralProfile.tail
                      (suffix.behavioralProfile (fun i => (σ i).val)))
                    normalized)) =
              ((ProgramBehavioralStrategy.headKernel
                  ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                  (projectViewEnv who
                    (VEnv.eraseEnv env))).bind fun v =>
                outcomeDistBehavioral k
                  (ProgramBehavioralProfile.tail
                    (suffix.behavioralProfile (fun i => (σ i).val)))
                  (VEnv.cons (Player := P) (L := L) (x := x)
                    (τ := .hidden who _) v env)).toPMF
                (outcomeDistBehavioral_totalWeight_eq_one
                  (p := VegasCore.commit x who R k)
                  (σ := suffix.behavioralProfile (fun i => (σ i).val))
                  normalized)
          rw [← FDist.toPMF_bind
            (ProgramBehavioralStrategy.headKernel
              ((suffix.behavioralProfile (fun i => (σ i).val)) who)
              (projectViewEnv who (VEnv.eraseEnv env)))
            (fun v =>
              outcomeDistBehavioral k
                (ProgramBehavioralProfile.tail
                  (suffix.behavioralProfile (fun i => (σ i).val)))
                (VEnv.cons (Player := P) (L := L) (x := x)
                  (τ := .hidden who _) v env))
            hd
            (fun v =>
              outcomeDistBehavioral_totalWeight_eq_one
                (p := k)
                (σ := ProgramBehavioralProfile.tail
                  (suffix.behavioralProfile (fun i => (σ i).val)))
                normalized)
            (outcomeDistBehavioral_totalWeight_eq_one
              (p := VegasCore.commit x who R k)
              (σ := suffix.behavioralProfile (fun i => (σ i).val))
              normalized)]
      | reveal y who x hx k =>
          simp [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral, VEnv.get]

theorem checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) :
    (checkedProfileStepPMF g hctx σ w).bind
        (checkedVegasOutcomeKernelPMF σ) =
      checkedVegasOutcomeKernelPMF σ w := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            outcomeDistBehavioralPMF]
      | letExpr x e k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            outcomeDistBehavioralPMF, PMF.pure_bind]
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
            outcomeDistBehavioralPMF]
          rw [PMF.bind_map]
          rfl
      | commit x who R k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            outcomeDistBehavioralPMF]
          rw [PMF.bind_map]
          rfl
      | reveal y who x hx k =>
          simp only [checkedProfileStepPMF, checkedVegasOutcomeKernelPMF,
            outcomeDistBehavioralPMF, PMF.pure_bind]
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

set_option linter.flexible false in
/-- Every supported nonterminal semantic small step consumes exactly one Vegas
syntax node. -/
theorem checkedProfileStep_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx)
    (hterm : ¬ checkedTerminal w)
    (dst : CheckedWorld g hctx)
    (hsupp : checkedProfileStep g hctx σ w dst ≠ 0) :
    dst.remainingSyntaxSteps + 1 = w.remainingSyntaxSteps := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | letExpr x e k =>
          simp [checkedProfileStep, CheckedWorld.remainingSyntaxSteps,
            syntaxSteps] at hsupp ⊢
          subst dst
          rfl
      | sample x D k =>
          simp [checkedProfileStep, CheckedWorld.remainingSyntaxSteps,
            syntaxSteps] at hsupp ⊢
          rcases hsupp with ⟨v, hdst, _hv⟩
          subst dst
          rfl
      | commit x who R k =>
          simp [checkedProfileStep, CheckedWorld.remainingSyntaxSteps,
            syntaxSteps] at hsupp ⊢
          rcases hsupp with ⟨v, hdst, _hv⟩
          subst dst
          rfl
      | reveal y who x hx k =>
          simp [checkedProfileStep, CheckedWorld.remainingSyntaxSteps,
            syntaxSteps] at hsupp ⊢
          subst dst
          rfl

theorem checkedProfileStepPMF_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx)
    (hterm : ¬ checkedTerminal w)
    (dst : CheckedWorld g hctx)
    (hsupp : checkedProfileStepPMF g hctx σ w dst ≠ 0) :
    dst.remainingSyntaxSteps + 1 = w.remainingSyntaxSteps := by
  cases w with
  | mk Γ prog env suffix wctx fresh viewScoped normalized legal =>
      cases prog with
      | ret payoffs =>
          simp [checkedTerminal, CheckedWorld.toWorld, terminal] at hterm
      | letExpr x e k =>
          simp only [checkedProfileStepPMF, PMF.pure_apply, ne_eq,
            ite_eq_right_iff, one_ne_zero, imp_false, not_not,
            CheckedWorld.remainingSyntaxSteps, syntaxSteps,
            Nat.add_right_cancel_iff] at hsupp ⊢
          subst dst
          rfl
      | sample x D k =>
          simp only [checkedProfileStepPMF, PMF.map_apply, ne_eq,
            ENNReal.tsum_eq_zero, ite_eq_right_iff, not_forall,
            CheckedWorld.remainingSyntaxSteps,
            syntaxSteps, Nat.add_right_cancel_iff] at hsupp ⊢
          rcases hsupp with ⟨v, hdst, _hv⟩
          subst dst
          rfl
      | commit x who R k =>
          simp only [checkedProfileStepPMF, PMF.map_apply, ne_eq,
            ENNReal.tsum_eq_zero, ite_eq_right_iff, not_forall,
            CheckedWorld.remainingSyntaxSteps,
            syntaxSteps, Nat.add_right_cancel_iff] at hsupp ⊢
          rcases hsupp with ⟨v, hdst, _hv⟩
          subst dst
          rfl
      | reveal y who x hx k =>
          simp [checkedProfileStepPMF, CheckedWorld.remainingSyntaxSteps,
            syntaxSteps] at hsupp ⊢
          subst dst
          rfl

open Classical in
/-- Vegas' own finite-horizon run over suffix-based checked worlds. This is
not an FOSG compiler output; it is the semantic small-step machine used as the
proof target for FOSG implementation lemmas. -/
noncomputable def checkedProfileRun
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    Nat → CheckedWorld g hctx → PMF (CheckedWorld g hctx)
  | 0, w => PMF.pure w
  | n + 1, w =>
      if checkedTerminal w then
        PMF.pure w
      else
        (checkedProfileStep g hctx σ w).bind
          (checkedProfileRun g hctx σ n)

@[simp] theorem checkedProfileRun_zero
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx) :
    checkedProfileRun g hctx σ 0 w = PMF.pure w := rfl

@[simp] theorem checkedProfileRun_succ_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedProfileRun g hctx σ (n + 1) w =
      PMF.pure w := by
  simp [checkedProfileRun, hterm]

@[simp] theorem checkedProfileRun_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedProfileRun g hctx σ n w =
      PMF.pure w := by
  cases n with
  | zero => rfl
  | succ n =>
      exact checkedProfileRun_succ_terminal
        g hctx σ n w hterm

theorem checkedProfileRun_succ_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : ¬ checkedTerminal w) :
    checkedProfileRun g hctx σ (n + 1) w =
      (checkedProfileStep g hctx σ w).bind
        (checkedProfileRun g hctx σ n) := by
  simp [checkedProfileRun, hterm]

open Classical in
noncomputable def checkedProfileRunPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    Nat → CheckedWorld g hctx → PMF (CheckedWorld g hctx)
  | 0, w => PMF.pure w
  | n + 1, w =>
      if checkedTerminal w then
        PMF.pure w
      else
        (checkedProfileStepPMF g hctx σ w).bind
          (checkedProfileRunPMF g hctx σ n)

@[simp] theorem checkedProfileRunPMF_zero
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CheckedWorld g hctx) :
    checkedProfileRunPMF g hctx σ 0 w = PMF.pure w := rfl

@[simp] theorem checkedProfileRunPMF_succ_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedProfileRunPMF g hctx σ (n + 1) w =
      PMF.pure w := by
  simp [checkedProfileRunPMF, hterm]

@[simp] theorem checkedProfileRunPMF_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedProfileRunPMF g hctx σ n w =
      PMF.pure w := by
  cases n with
  | zero => rfl
  | succ n =>
      exact checkedProfileRunPMF_succ_terminal
        g hctx σ n w hterm

theorem checkedProfileRunPMF_succ_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : ¬ checkedTerminal w) :
    checkedProfileRunPMF g hctx σ (n + 1) w =
      (checkedProfileStepPMF g hctx σ w).bind
        (checkedProfileRunPMF g hctx σ n) := by
  simp [checkedProfileRunPMF, hterm]

theorem checkedTransition_bind_checkedProfileRun_eq_checkedProfileRun_succ_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (hterm : ¬ checkedTerminal w)
    (hactive : checkedActive w = ∅) :
    (checkedTransition w a).bind
        (checkedProfileRun g hctx σ n) =
      checkedProfileRun g hctx σ (n + 1) w := by
  rw [checkedTransition_eq_checkedProfileStep_of_active_empty
    g hctx σ w a hactive]
  rw [checkedProfileRun_succ_nonterminal
    g hctx σ n w hterm]

/-- Any finite run of the suffix-based Vegas semantic machine preserves the
remaining denotational outcome kernel. -/
theorem checkedProfileRun_bind_checkedVegasOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    ∀ (n : Nat) (w : CheckedWorld g hctx),
      (checkedProfileRun g hctx σ n w).bind
          (checkedVegasOutcomeKernel σ) =
        checkedVegasOutcomeKernel σ w := by
  intro n
  induction n with
  | zero =>
      intro w
      simp
  | succ n ih =>
      intro w
      by_cases hterm : checkedTerminal w
      · rw [checkedProfileRun_succ_terminal
          g hctx σ n w hterm]
        simp
      · rw [checkedProfileRun_succ_nonterminal
          g hctx σ n w hterm]
        rw [PMF.bind_bind]
        conv_lhs =>
          arg 2
          intro w'
          rw [ih w']
        exact checkedProfileStep_bind_checkedVegasOutcomeKernel
          g hctx σ w

theorem checkedProfileRunPMF_bind_checkedVegasOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    ∀ (n : Nat) (w : CheckedWorld g hctx),
      (checkedProfileRunPMF g hctx σ n w).bind
          (checkedVegasOutcomeKernelPMF σ) =
        checkedVegasOutcomeKernelPMF σ w := by
  intro n
  induction n with
  | zero =>
      intro w
      simp
  | succ n ih =>
      intro w
      by_cases hterm : checkedTerminal w
      · rw [checkedProfileRunPMF_succ_terminal
          g hctx σ n w hterm]
        simp
      · rw [checkedProfileRunPMF_succ_nonterminal
          g hctx σ n w hterm]
        rw [PMF.bind_bind]
        conv_lhs =>
          arg 2
          intro w'
          rw [ih w']
        exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
          g hctx σ w

/-- Once the semantic run horizon covers the remaining syntax depth, every
supported destination is terminal. -/
theorem checkedProfileRun_support_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    ∀ (n : Nat) (w dst : CheckedWorld g hctx),
      w.remainingSyntaxSteps ≤ n →
      dst ∈ (checkedProfileRun g hctx σ n w).support →
        checkedTerminal dst := by
  intro n
  induction n with
  | zero =>
      intro w dst hn hdst
      have hzero : w.remainingSyntaxSteps = 0 := by omega
      have hterm : checkedTerminal w :=
        checkedTerminal_iff_remainingSyntaxSteps_eq_zero.mpr hzero
      have hdstEq : dst = w := by
        simpa using hdst
      subst dst
      exact hterm
  | succ n ih =>
      intro w dst hn hdst
      by_cases hterm : checkedTerminal w
      · rw [checkedProfileRun_succ_terminal
          g hctx σ n w hterm] at hdst
        have hdstEq : dst = w := by
          simpa using hdst
        subst dst
        exact hterm
      · rw [checkedProfileRun_succ_nonterminal
          g hctx σ n w hterm] at hdst
        rw [PMF.mem_support_bind_iff] at hdst
        rcases hdst with ⟨mid, hmid, hdst⟩
        have hstep := checkedProfileStep_remainingSyntaxSteps
          g hctx σ w hterm mid
          (by simpa [PMF.mem_support_iff] using hmid)
        have hmidDepth : mid.remainingSyntaxSteps ≤ n := by omega
        exact ih mid dst hmidDepth hdst

theorem checkedProfileRunPMF_support_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    ∀ (n : Nat) (w dst : CheckedWorld g hctx),
      w.remainingSyntaxSteps ≤ n →
      dst ∈ (checkedProfileRunPMF g hctx σ n w).support →
        checkedTerminal dst := by
  intro n
  induction n with
  | zero =>
      intro w dst hn hdst
      have hzero : w.remainingSyntaxSteps = 0 := by omega
      have hterm : checkedTerminal w :=
        checkedTerminal_iff_remainingSyntaxSteps_eq_zero.mpr hzero
      have hdstEq : dst = w := by
        simpa using hdst
      subst dst
      exact hterm
  | succ n ih =>
      intro w dst hn hdst
      by_cases hterm : checkedTerminal w
      · rw [checkedProfileRunPMF_succ_terminal
          g hctx σ n w hterm] at hdst
        have hdstEq : dst = w := by
          simpa using hdst
        subst dst
        exact hterm
      · rw [checkedProfileRunPMF_succ_nonterminal
          g hctx σ n w hterm] at hdst
        rw [PMF.mem_support_bind_iff] at hdst
        rcases hdst with ⟨mid, hmid, hdst⟩
        have hstep := checkedProfileStepPMF_remainingSyntaxSteps
          g hctx σ w hterm mid
          (by simpa [PMF.mem_support_iff] using hmid)
        have hmidDepth : mid.remainingSyntaxSteps ≤ n := by omega
        exact ih mid dst hmidDepth hdst

/-- At sufficient horizon, the suffix-based Vegas semantic run projected to
payoff outcomes is exactly the denotational outcome kernel at the starting
world. -/
theorem checkedProfileRun_map_checkedWorldOutcome_eq_checkedVegasOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hn : w.remainingSyntaxSteps ≤ n) :
    PMF.map (checkedWorldOutcome (P := P) (L := L))
        (checkedProfileRun g hctx σ n w) =
      checkedVegasOutcomeKernel σ w := by
  rw [← PMF.bind_pure_comp]
  rw [Math.ProbabilityMassFunction.bind_congr_on_support
    (checkedProfileRun g hctx σ n w)
    (PMF.pure ∘ checkedWorldOutcome (P := P) (L := L))
    (checkedVegasOutcomeKernel σ)]
  · exact checkedProfileRun_bind_checkedVegasOutcomeKernel
      g hctx σ n w
  · intro dst hdst
    have hterm := checkedProfileRun_support_terminal
      g hctx σ n w dst hn hdst
    rw [checkedVegasOutcomeKernel_terminal
      σ dst hterm]
    rfl

theorem checkedProfileRunPMF_map_checkedWorldOutcome_eq_checkedVegasOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hn : w.remainingSyntaxSteps ≤ n) :
    PMF.map (checkedWorldOutcome (P := P) (L := L))
        (checkedProfileRunPMF g hctx σ n w) =
      checkedVegasOutcomeKernelPMF σ w := by
  rw [← PMF.bind_pure_comp]
  rw [Math.ProbabilityMassFunction.bind_congr_on_support
    (checkedProfileRunPMF g hctx σ n w)
    (PMF.pure ∘ checkedWorldOutcome (P := P) (L := L))
    (checkedVegasOutcomeKernelPMF σ)]
  · exact checkedProfileRunPMF_bind_checkedVegasOutcomeKernelPMF
      g hctx σ n w
  · intro dst hdst
    have hterm := checkedProfileRunPMF_support_terminal
      g hctx σ n w dst hn hdst
    rw [checkedVegasOutcomeKernelPMF_terminal
      σ dst hterm]
    rfl

@[simp] theorem checkedVegasOutcomeKernel_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    checkedVegasOutcomeKernel σ
        (CheckedWorld.initial g hctx) =
      (toKernelGame g).outcomeKernel σ := rfl

@[simp] theorem checkedVegasOutcomeKernelPMF_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    checkedVegasOutcomeKernelPMF σ
        (CheckedWorld.initial g hctx) =
      (toKernelGamePMF g).outcomeKernel σ := rfl

/-- The suffix-based Vegas semantic machine, run for the syntactic horizon
from the initial checked world and projected to payoff outcomes, agrees with
the user-facing kernel-game semantics. -/
theorem checkedProfileRun_initial_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    PMF.map (checkedWorldOutcome (P := P) (L := L))
        (checkedProfileRun g hctx σ
          (syntaxSteps g.prog)
          (CheckedWorld.initial g hctx)) =
      (toKernelGame g).outcomeKernel σ := by
  rw [checkedProfileRun_map_checkedWorldOutcome_eq_checkedVegasOutcomeKernel
    g hctx σ (syntaxSteps g.prog)
    (CheckedWorld.initial g hctx)]
  · rfl
  · rfl

theorem checkedProfileRunPMF_initial_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    PMF.map (checkedWorldOutcome (P := P) (L := L))
        (checkedProfileRunPMF g hctx σ
          (syntaxSteps g.prog)
          (CheckedWorld.initial g hctx)) =
      (toKernelGamePMF g).outcomeKernel σ := by
  rw [checkedProfileRunPMF_map_checkedWorldOutcome_eq_checkedVegasOutcomeKernelPMF
    g hctx σ (syntaxSteps g.prog)
    (CheckedWorld.initial g hctx)]
  · rfl
  · rfl

@[simp] theorem checkedVegasOutcomeKernel_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfile g)
    (w : CursorCheckedWorld g) :
    checkedVegasOutcomeKernel (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      cursorVegasOutcomeKernel σ w := rfl

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

/-- Forget the finite cursor world at the end of an observed-program FOSG
history to the suffix-based checked-world semantic state. -/
noncomputable def observedProgramHistoryCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    CheckedWorld g hctx :=
  CheckedWorld.ofCursorChecked h.lastState

@[simp] theorem checkedWorldOutcome_observedProgramHistoryCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    checkedWorldOutcome
        (observedProgramHistoryCheckedWorld g hctx h) =
      observedProgramHistoryOutcome g hctx h := by
  simp [observedProgramHistoryCheckedWorld, observedProgramHistoryOutcome]

@[simp] theorem checkedTerminal_observedProgramHistoryCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    checkedTerminal
        (observedProgramHistoryCheckedWorld g hctx h) ↔
      (observedProgramFOSG g hctx).terminal h.lastState := by
  simp [observedProgramHistoryCheckedWorld, observedProgramFOSG,
    checkedTerminal, CheckedWorld.ofCursorChecked,
    CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
    CheckedWorld.toWorld]

theorem observedProgramHistoryCheckedWorld_extendByOutcome_of_support
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (hsupp :
      (observedProgramFOSG g hctx).transition
        h.lastState a dst ≠ 0) :
    observedProgramHistoryCheckedWorld g hctx
        (h.extendByOutcome a dst) =
      CheckedWorld.ofCursorChecked (hctx := hctx) dst := by
  rw [GameTheory.FOSG.History.extendByOutcome_of_support
    (h := h) (a := a) (dst := dst) hsupp]
  simp [observedProgramHistoryCheckedWorld]

/-- The Vegas-outcome kernel induced by running the observed-program FOSG and
projecting terminal histories back to Vegas payoff outcomes. This is the
left-hand side of the intended outcome-preservation theorem against
`toKernelGame`. -/
noncomputable def observedProgramOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) : PMF (Outcome P) :=
  PMF.map (observedProgramHistoryOutcome g hctx)
    (observedProgramRunDist g hctx LF
      (toObservedProgramLegalBehavioralProfile g hctx σ))

/-- Re-express the observed-program outcome kernel as the checked-world
outcome projection of the final FOSG history state. This is just projection
bookkeeping; `observedProgramCheckedWorldRunDist_eq_checkedProfileRun` proves
the corresponding checked-world run adequacy. -/
theorem observedProgramOutcomeKernel_eq_checkedWorldProjection
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel g hctx LF σ =
      PMF.map (checkedWorldOutcome (P := P) (L := L))
        (PMF.map
          (observedProgramHistoryCheckedWorld g hctx)
          (observedProgramRunDist g hctx LF
            (toObservedProgramLegalBehavioralProfile g hctx σ))) := by
  rw [PMF.map_comp]
  simp [observedProgramOutcomeKernel, Function.comp_def]

/-- The observed-program FOSG run, with terminal histories forgotten to their
last checked-world semantic state. This is the exact implementation-adequacy
distribution that remains to compare with `checkedProfileRun`. -/
noncomputable def observedProgramCheckedWorldRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) : PMF (CheckedWorld g hctx) :=
  PMF.map (observedProgramHistoryCheckedWorld g hctx)
    (observedProgramRunDist g hctx LF
      (toObservedProgramLegalBehavioralProfile g hctx σ))

/-- Arbitrary-history version of `observedProgramCheckedWorldRunDist`, used for
the induction that the finite FOSG implementation run follows the checked-world
semantic run. -/
noncomputable def observedProgramCheckedWorldRunDistFrom
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History) :
    PMF (CheckedWorld g hctx) :=
  PMF.map (observedProgramHistoryCheckedWorld g hctx)
    (observedProgramRunDistFrom g hctx LF
      (toObservedProgramLegalBehavioralProfile g hctx σ) n h)

@[simp] theorem observedProgramCheckedWorldRunDistFrom_zero
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History) :
    observedProgramCheckedWorldRunDistFrom
        g hctx LF σ 0 h =
      PMF.pure
        (observedProgramHistoryCheckedWorld g hctx h) := by
  simp [observedProgramCheckedWorldRunDistFrom, observedProgramRunDistFrom,
    PMF.pure_map]

theorem observedProgramCheckedWorldRunDist_eq_runDistFrom_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramCheckedWorldRunDist
        g hctx LF σ =
      observedProgramCheckedWorldRunDistFrom
        g hctx LF σ
        (syntaxSteps g.prog)
        (GameTheory.FOSG.History.nil
          (observedProgramFOSG g hctx)) := by
  rfl

theorem observedProgramCheckedWorldRunDistFrom_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFrom
        g hctx LF σ n h =
      PMF.pure
        (observedProgramHistoryCheckedWorld g hctx h) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramCheckedWorldRunDistFrom observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_terminal
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) n h hterm]
  rw [PMF.pure_map]

theorem observedProgramCheckedWorldRunDistFrom_terminal_eq_checkedProfileRun
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFrom
        g hctx LF σ n h =
      checkedProfileRun g hctx σ n
        (observedProgramHistoryCheckedWorld g hctx h) := by
  rw [observedProgramCheckedWorldRunDistFrom_terminal
    g hctx LF σ n h hterm]
  rw [checkedProfileRun_terminal]
  exact (checkedTerminal_observedProgramHistoryCheckedWorld
    g hctx h).2 hterm

/-- The checked-world projection of one nonterminal FOSG execution step followed
by the remaining projected run. The finite action instances are local to this
definition, avoiding heavyweight theorem signatures. -/
noncomputable def observedProgramCheckedWorldRunDistFromSucc
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    PMF (CheckedWorld g hctx) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  exact
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
      (fun a =>
        ((observedProgramFOSG g hctx).transition
            h.lastState a).bind
          (fun dst =>
            observedProgramCheckedWorldRunDistFrom
              g hctx LF σ n
              (h.extendByOutcome a dst)))

/-- Checked-world projection of the generic nonterminal FOSG run equation. -/
theorem observedProgramCheckedWorldRunDistFrom_succ_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFrom
        g hctx LF σ (n + 1) h =
      observedProgramCheckedWorldRunDistFromSucc
        g hctx LF σ n h hterm := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramCheckedWorldRunDistFromSucc
  unfold observedProgramCheckedWorldRunDistFrom observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) n h hterm]
  rw [PMF.map_bind]
  congr
  funext a
  rw [PMF.map_bind]

/-- Checked-world projection of the one-step FOSG run equation at states with
no active players. This is the implementation-side reduction for Vegas `let`,
`sample`, and `reveal` nodes. -/
theorem observedProgramCheckedWorldRunDistFrom_succ_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState)
    (hactive : (observedProgramFOSG g hctx).active h.lastState = ∅) :
    observedProgramCheckedWorldRunDistFrom
        g hctx LF σ (n + 1) h =
      ((observedProgramFOSG g hctx).transition h.lastState
          ⟨GameTheory.FOSG.noopAction
              (fun who : P => ProgramAction g.prog who),
            (observedProgramFOSG g hctx)
              |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩).bind
        (fun dst =>
          observedProgramCheckedWorldRunDistFrom
            g hctx LF σ n
            (h.extendByOutcome
              ⟨GameTheory.FOSG.noopAction
                  (fun who : P => ProgramAction g.prog who),
                (observedProgramFOSG g hctx)
                  |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩
              dst)) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramCheckedWorldRunDistFrom observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_succ_active_empty
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) n h hterm hactive]
  rw [PMF.map_bind]

/-- The observed-program FOSG run, after forgetting histories and cursor
bookkeeping, is the same finite-horizon run as the direct checked-world Vegas
semantics. -/
theorem observedProgramCheckedWorldRunDistFrom_eq_checkedProfileRun
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    ∀ n h,
      observedProgramCheckedWorldRunDistFrom
          g hctx LF σ n h =
        checkedProfileRun g hctx σ n
          (observedProgramHistoryCheckedWorld g hctx h) := by
  intro n
  induction n with
  | zero =>
      intro h
      simp
  | succ n ih =>
      intro h
      by_cases hterm : (observedProgramFOSG g hctx).terminal
          h.lastState
      · exact observedProgramCheckedWorldRunDistFrom_terminal_eq_checkedProfileRun
          g hctx LF σ (n + 1) h hterm
      · letI : ∀ who : P,
            Fintype (Option (ProgramAction g.prog who)) :=
          fun who =>
            observedProgramFOSG.instFintypeOptionAction
              g hctx LF who
        have hcheckedTerm :
            ¬ checkedTerminal
              (observedProgramHistoryCheckedWorld g hctx h) := by
          intro ht
          exact hterm ((checkedTerminal_observedProgramHistoryCheckedWorld
            g hctx h).1 ht)
        rw [observedProgramCheckedWorldRunDistFrom_succ_nonterminal
          g hctx LF σ n h hterm]
        rw [checkedProfileRun_succ_nonterminal
          g hctx σ n
          (observedProgramHistoryCheckedWorld g hctx h)
          hcheckedTerm]
        unfold observedProgramCheckedWorldRunDistFromSucc
        let G := observedProgramFOSG g hctx
        let law := G.legalActionLaw
          (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm
        let step := fun a : G.LegalAction h.lastState =>
          G.transition h.lastState a
        let forget :=
          CheckedWorld.ofCursorChecked (hctx := hctx)
        let run := checkedProfileRun g hctx σ n
        have hstep :
            law.bind (fun a => PMF.map forget (step a)) =
              checkedProfileStep g hctx σ
                (observedProgramHistoryCheckedWorld
                  g hctx h) := by
          simpa [G, law, step, forget, observedProgramHistoryCheckedWorld] using
            observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep
              g hctx σ h hterm
        calc
          law.bind
              (fun a =>
                (step a).bind
                  (fun dst =>
                    observedProgramCheckedWorldRunDistFrom
                      g hctx LF σ n
                      (h.extendByOutcome a dst))) =
            law.bind
              (fun a =>
                (step a).bind
                  (fun dst =>
                    run
                      (observedProgramHistoryCheckedWorld
                        g hctx
                        (h.extendByOutcome a dst)))) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                law _ _ ?_
              intro a _
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (step a) _ _ ?_
              intro dst _
              exact ih (h.extendByOutcome a dst)
          _ =
            law.bind
              (fun a =>
                (step a).bind
                  (fun dst => run (forget dst))) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                law _ _ ?_
              intro a _
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (step a) _ _ ?_
              intro dst hdst
              have hsupp : step a dst ≠ 0 := by
                simpa [step, PMF.mem_support_iff] using hdst
              rw [observedProgramHistoryCheckedWorld_extendByOutcome_of_support
                g hctx h a dst hsupp]
          _ =
            (law.bind (fun a => PMF.map forget (step a))).bind run := by
              rw [PMF.bind_bind]
              congr
              funext a
              simp [PMF.map, PMF.bind_bind]
          _ =
            (checkedProfileStep g hctx σ
              (observedProgramHistoryCheckedWorld
                g hctx h)).bind run := by
              rw [hstep]

noncomputable def observedProgramCheckedWorldRunDistFromPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History) :
    PMF (CheckedWorld g hctx) :=
  PMF.map (observedProgramHistoryCheckedWorld g hctx)
    (observedProgramRunDistFrom g hctx LF
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ) n h)

@[simp] theorem observedProgramCheckedWorldRunDistFromPMF_zero
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g)
    (h : (observedProgramFOSG g hctx).History) :
    observedProgramCheckedWorldRunDistFromPMF
        g hctx LF σ 0 h =
      PMF.pure
        (observedProgramHistoryCheckedWorld g hctx h) := by
  simp [observedProgramCheckedWorldRunDistFromPMF, observedProgramRunDistFrom,
    PMF.pure_map]

theorem observedProgramCheckedWorldRunDistFromPMF_terminal_eq_checkedProfileRunPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFromPMF
        g hctx LF σ n h =
      checkedProfileRunPMF g hctx σ n
        (observedProgramHistoryCheckedWorld g hctx h) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramCheckedWorldRunDistFromPMF observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_terminal
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfilePMF g hctx σ) n h hterm]
  rw [PMF.pure_map]
  rw [checkedProfileRunPMF_terminal]
  exact (checkedTerminal_observedProgramHistoryCheckedWorld
    g hctx h).2 hterm

noncomputable def observedProgramCheckedWorldRunDistFromSuccPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    PMF (CheckedWorld g hctx) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  exact
    ((observedProgramFOSG g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm).bind
      (fun a =>
        ((observedProgramFOSG g hctx).transition
            h.lastState a).bind
          (fun dst =>
            observedProgramCheckedWorldRunDistFromPMF
              g hctx LF σ n
              (h.extendByOutcome a dst)))

theorem observedProgramCheckedWorldRunDistFromPMF_succ_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFromPMF
        g hctx LF σ (n + 1) h =
      observedProgramCheckedWorldRunDistFromSuccPMF
        g hctx LF σ n h hterm := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  unfold observedProgramCheckedWorldRunDistFromSuccPMF
  unfold observedProgramCheckedWorldRunDistFromPMF observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
    (G := observedProgramFOSG g hctx)
    (toObservedProgramLegalBehavioralProfilePMF g hctx σ) n h hterm]
  rw [PMF.map_bind]
  congr
  funext a
  rw [PMF.map_bind]

theorem observedProgramCheckedWorldRunDistFromPMF_eq_checkedProfileRunPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    ∀ n h,
      observedProgramCheckedWorldRunDistFromPMF
          g hctx LF σ n h =
        checkedProfileRunPMF g hctx σ n
          (observedProgramHistoryCheckedWorld g hctx h) := by
  intro n
  induction n with
  | zero =>
      intro h
      simp
  | succ n ih =>
      intro h
      by_cases hterm : (observedProgramFOSG g hctx).terminal
          h.lastState
      · exact observedProgramCheckedWorldRunDistFromPMF_terminal_eq_checkedProfileRunPMF
          g hctx LF σ (n + 1) h hterm
      · letI : ∀ who : P,
            Fintype (Option (ProgramAction g.prog who)) :=
          fun who =>
            observedProgramFOSG.instFintypeOptionAction
              g hctx LF who
        have hcheckedTerm :
            ¬ checkedTerminal
              (observedProgramHistoryCheckedWorld g hctx h) := by
          intro ht
          exact hterm ((checkedTerminal_observedProgramHistoryCheckedWorld
            g hctx h).1 ht)
        rw [observedProgramCheckedWorldRunDistFromPMF_succ_nonterminal
          g hctx LF σ n h hterm]
        rw [checkedProfileRunPMF_succ_nonterminal
          g hctx σ n
          (observedProgramHistoryCheckedWorld g hctx h)
          hcheckedTerm]
        unfold observedProgramCheckedWorldRunDistFromSuccPMF
        let G := observedProgramFOSG g hctx
        let law := G.legalActionLaw
          (toObservedProgramLegalBehavioralProfilePMF g hctx σ) h hterm
        let step := fun a : G.LegalAction h.lastState =>
          G.transition h.lastState a
        let forget :=
          CheckedWorld.ofCursorChecked (hctx := hctx)
        let run := checkedProfileRunPMF g hctx σ n
        have hstep :
            law.bind (fun a => PMF.map forget (step a)) =
              checkedProfileStepPMF g hctx σ
                (observedProgramHistoryCheckedWorld
                  g hctx h) := by
          simpa [G, law, step, forget, observedProgramHistoryCheckedWorld] using
            observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF
              g hctx σ h hterm
        calc
          law.bind
              (fun a =>
                (step a).bind
                  (fun dst =>
                    observedProgramCheckedWorldRunDistFromPMF
                      g hctx LF σ n
                      (h.extendByOutcome a dst))) =
            law.bind
              (fun a =>
                (step a).bind
                  (fun dst =>
                    run
                      (observedProgramHistoryCheckedWorld
                        g hctx
                        (h.extendByOutcome a dst)))) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                law _ _ ?_
              intro a _
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (step a) _ _ ?_
              intro dst _
              exact ih (h.extendByOutcome a dst)
          _ =
            law.bind
              (fun a =>
                (step a).bind
                  (fun dst => run (forget dst))) := by
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                law _ _ ?_
              intro a _
              refine Math.ProbabilityMassFunction.bind_congr_on_support
                (step a) _ _ ?_
              intro dst hdst
              have hsupp : step a dst ≠ 0 := by
                simpa [step, PMF.mem_support_iff] using hdst
              rw [observedProgramHistoryCheckedWorld_extendByOutcome_of_support
                g hctx h a dst hsupp]
          _ =
            (law.bind (fun a => PMF.map forget (step a))).bind run := by
              rw [PMF.bind_bind]
              congr
              funext a
              simp [PMF.map, PMF.bind_bind]
          _ =
            (checkedProfileStepPMF g hctx σ
              (observedProgramHistoryCheckedWorld
                g hctx h)).bind run := by
              rw [hstep]

@[simp] theorem observedProgramHistoryCheckedWorld_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    observedProgramHistoryCheckedWorld g hctx
        (GameTheory.FOSG.History.nil
          (observedProgramFOSG g hctx)) =
      CheckedWorld.initial g hctx := by
  rfl

theorem observedProgramCheckedWorldRunDist_eq_checkedProfileRun
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramCheckedWorldRunDist
        g hctx LF σ =
      checkedProfileRun g hctx σ
        (syntaxSteps g.prog)
        (CheckedWorld.initial g hctx) := by
  rw [observedProgramCheckedWorldRunDist_eq_runDistFrom_initial]
  rw [observedProgramCheckedWorldRunDistFrom_eq_checkedProfileRun]
  simp

noncomputable def observedProgramOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) : PMF (Outcome P) :=
  PMF.map (observedProgramHistoryOutcome g hctx)
    (observedProgramRunDist g hctx LF
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ))

noncomputable def observedProgramCheckedWorldRunDistPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) : PMF (CheckedWorld g hctx) :=
  PMF.map (observedProgramHistoryCheckedWorld g hctx)
    (observedProgramRunDist g hctx LF
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ))

theorem observedProgramCheckedWorldRunDistPMF_eq_runDistFrom_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramCheckedWorldRunDistPMF
        g hctx LF σ =
      observedProgramCheckedWorldRunDistFromPMF
        g hctx LF σ
        (syntaxSteps g.prog)
        (GameTheory.FOSG.History.nil
          (observedProgramFOSG g hctx)) := by
  rfl

theorem observedProgramCheckedWorldRunDistPMF_eq_checkedProfileRunPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramCheckedWorldRunDistPMF
        g hctx LF σ =
      checkedProfileRunPMF g hctx σ
        (syntaxSteps g.prog)
        (CheckedWorld.initial g hctx) := by
  rw [observedProgramCheckedWorldRunDistPMF_eq_runDistFrom_initial]
  rw [observedProgramCheckedWorldRunDistFromPMF_eq_checkedProfileRunPMF]
  simp

theorem observedProgramOutcomeKernelPMF_eq_checkedWorldProjection
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      PMF.map (checkedWorldOutcome (P := P) (L := L))
        (PMF.map
          (observedProgramHistoryCheckedWorld g hctx)
          (observedProgramRunDist g hctx LF
            (toObservedProgramLegalBehavioralProfilePMF g hctx σ))) := by
  rw [PMF.map_comp]
  simp [observedProgramOutcomeKernelPMF, Function.comp_def]

theorem observedProgramOutcomeKernelPMF_eq_checkedWorldRunDistPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      PMF.map (checkedWorldOutcome (P := P) (L := L))
        (observedProgramCheckedWorldRunDistPMF
          g hctx LF σ) := by
  rw [observedProgramOutcomeKernelPMF_eq_checkedWorldProjection]
  rfl

theorem observedProgramOutcomeKernelPMF_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      (toKernelGamePMF g).outcomeKernel σ := by
  rw [observedProgramOutcomeKernelPMF_eq_checkedWorldRunDistPMF]
  rw [observedProgramCheckedWorldRunDistPMF_eq_checkedProfileRunPMF]
  exact checkedProfileRunPMF_initial_outcomeKernel g hctx σ

theorem observedProgramReachableOutcomeKernelPMF_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDist g hctx LF
          (toObservedProgramReachableLegalBehavioralProfilePMF
            g hctx σ).extend) =
      (toKernelGamePMF g).outcomeKernel σ := by
  rw [observedProgramRunDistPMF_reachable_extend_eq g hctx LF σ]
  exact observedProgramOutcomeKernelPMF_eq_toKernelGamePMF g hctx LF σ

theorem observedProgramOutcomeKernel_eq_checkedWorldRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel g hctx LF σ =
      PMF.map (checkedWorldOutcome (P := P) (L := L))
        (observedProgramCheckedWorldRunDist
          g hctx LF σ) := by
  rw [observedProgramOutcomeKernel_eq_checkedWorldProjection]
  rfl

/-- Once the finite FOSG implementation run is shown to equal the suffix-based
Vegas semantic run after forgetting cursor/history structure, outcome
preservation follows from the checked-world semantic theorem. -/
theorem observedProgramOutcomeKernel_eq_toKernelGame_of_checkedWorldRunDist_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (hadequacy :
      observedProgramCheckedWorldRunDist
          g hctx LF σ =
        checkedProfileRun g hctx σ
          (syntaxSteps g.prog)
          (CheckedWorld.initial g hctx)) :
    observedProgramOutcomeKernel g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  rw [observedProgramOutcomeKernel_eq_checkedWorldRunDist]
  rw [hadequacy]
  exact checkedProfileRun_initial_outcomeKernel
    g hctx σ

/-- Outcome preservation for the observed-program FOSG: running the FOSG with
the profile induced by a Vegas legal behavioral profile gives exactly the same
outcome kernel as the direct `toKernelGame` semantics. -/
theorem observedProgramOutcomeKernel_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  exact observedProgramOutcomeKernel_eq_toKernelGame_of_checkedWorldRunDist_eq
    g hctx LF σ
    (observedProgramCheckedWorldRunDist_eq_checkedProfileRun
      g hctx LF σ)

/-- Pure-strategy outcome preservation for the observed-program FOSG.

Transporting a Vegas legal pure profile to the FOSG, running its deterministic
behavioral lift, and projecting terminal histories to Vegas outcomes gives the
same outcome distribution as `toStrategicKernelGame`. -/
theorem observedProgramPureOutcomeKernel_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramPureProfile g) :
    PMF.map (observedProgramHistoryOutcome g hctx)
        (observedProgramRunDist g hctx LF
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramLegalPureProfile g hctx σ))) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  rw [show
      PMF.map (observedProgramHistoryOutcome g hctx)
          (observedProgramRunDist g hctx LF
            ((observedProgramFOSG g hctx).legalPureToBehavioral
              (toObservedProgramLegalPureProfile g hctx σ))) =
        observedProgramOutcomeKernel g hctx LF
          (LegalProgramPureProfile.toBehavioral σ) by
        simp [observedProgramOutcomeKernel,
          toObservedProgramLegalBehavioralProfile_toBehavioral]]
  rw [observedProgramOutcomeKernel_eq_toKernelGame]
  exact toKernelGame_outcomeKernel_eq_toStrategicKernelGame_toBehavioral g σ

/-- Reachable pure-profile outcome preservation for the observed-program FOSG.

The reachable-coordinate FOSG Kuhn theorem states its pure side using
`reachableHistoryOutcomeDistPureProfile`. For Vegas, that distribution is the
same terminal-history law as the native observed-program FOSG run of the
extended pure profile, hence it projects to `toStrategicKernelGame`. -/
theorem observedProgramReachablePureOutcomeKernel_eq_toStrategicKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramPureProfile g) :
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    PMF.map (observedProgramHistoryOutcome g hctx)
        (GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile
          (G := observedProgramFOSG g hctx)
          (observedProgramFOSG_legalObservable g hctx)
          (syntaxSteps g.prog)
          (toObservedProgramReachableLegalPureProfile g hctx σ)) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  rw [GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile_eq_runDist
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_legalObservable g hctx)]
  rw [show
      (observedProgramFOSG g hctx).runDist (syntaxSteps g.prog)
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramReachableLegalPureProfile g hctx σ).extend) =
        observedProgramRunDist g hctx LF
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramLegalPureProfile g hctx σ)) by
        unfold observedProgramRunDist
        exact GameTheory.FOSG.runDist_congr
          (G := observedProgramFOSG g hctx)
          (syntaxSteps g.prog)
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramReachableLegalPureProfile g hctx σ).extend)
          ((observedProgramFOSG g hctx).legalPureToBehavioral
            (toObservedProgramLegalPureProfile g hctx σ))
          (by
            intro h who
            simp [GameTheory.FOSG.legalPureToBehavioral,
              GameTheory.FOSG.pureToBehavioral])]
  exact observedProgramPureOutcomeKernel_eq_toStrategicKernelGame g hctx LF σ

/-- Kernel-game-shaped version of `observedProgramOutcomeKernel`: strategies
are Vegas legal behavioral profiles and outcomes are Vegas payoff outcomes.
`observedProgramOutcomeKernel_eq_toKernelGame` identifies this kernel with
`toKernelGame g`. -/
noncomputable def observedProgramOutcomeKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : KernelGame P where
  Strategy := LegalProgramBehavioralStrategy g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := observedProgramOutcomeKernel g hctx LF

@[simp] theorem observedProgramOutcomeKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramOutcomeKernelGame g hctx LF).outcomeKernel σ =
      observedProgramOutcomeKernel g hctx LF σ := rfl

@[simp] theorem observedProgramOutcomeKernelGame_udist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramOutcomeKernelGame g hctx LF).udist σ =
      (toKernelGame g).udist σ := by
  simp [KernelGame.udist, observedProgramOutcomeKernelGame,
    observedProgramOutcomeKernel_eq_toKernelGame, toKernelGame]

@[simp] theorem observedProgramOutcomeKernelGame_eu
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    (observedProgramOutcomeKernelGame g hctx LF).eu σ who =
      (toKernelGame g).eu σ who := by
  simp [KernelGame.eu, observedProgramOutcomeKernelGame,
    observedProgramOutcomeKernel_eq_toKernelGame, toKernelGame]

theorem observedProgramProjectedPayoff_runDist_eq_toKernelGame_eu
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    ∑ h : (observedProgramFOSG g hctx).History,
      (observedProgramRunDist g hctx LF
        (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
        (observedProgramHistoryOutcome g hctx h who : ℝ) =
      (toKernelGame g).eu σ who := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  calc
    ∑ h : (observedProgramFOSG g hctx).History,
      (observedProgramRunDist g hctx LF
        (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
        (observedProgramHistoryOutcome g hctx h who : ℝ)
      = (observedProgramOutcomeKernelGame
          g hctx LF).eu σ who := by
          symm
          rw [KernelGame.eu]
          change Math.Probability.expect
              (PMF.map (observedProgramHistoryOutcome g hctx)
                (observedProgramRunDist g hctx LF
                  (toObservedProgramLegalBehavioralProfile g hctx σ)))
              (fun o : Outcome P => (o who : ℝ)) =
            ∑ h : (observedProgramFOSG g hctx).History,
              (observedProgramRunDist g hctx LF
                (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
                (observedProgramHistoryOutcome g hctx h who : ℝ)
          rw [Math.Probability.expect_map_fintype_source]
    _ = (toKernelGame g).eu σ who := by
          exact observedProgramOutcomeKernelGame_eu
            g hctx LF σ who

/-- Reachable-coordinate behavioral-to-mixed preservation for Vegas projected
expected payoff.

The left side samples a reachable pure FOSG profile from the behavioral profile
and evaluates each pure profile by the projected Vegas payoff on terminal
histories. The right side is the standard Vegas `toKernelGame` expected
utility. -/
theorem observedProgramProjectedPayoff_behavioral_to_mixed_toKernelGame_eu_reachable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P,
        Fintype (ProgramAction g.prog who) :=
      fun who =>
        ProgramAction.instFintype LF g.prog who
    letI : ∀ who : P,
        Fintype (Option (ProgramAction g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∑ π,
      (GameTheory.FOSG.Kuhn.reachableBehavioralToMixedJoint
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            g hctx σ).toProfile π).toReal *
        (∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              ((observedProgramFOSG g hctx).pureToBehavioral π.extend)
              h).toReal *
            (observedProgramHistoryOutcome g hctx h who : ℝ)) =
      (toKernelGame g).eu σ who := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (ProgramAction g.prog who) :=
    fun who =>
      ProgramAction.instFintype LF g.prog who
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  calc
    ∑ π,
      (GameTheory.FOSG.Kuhn.reachableBehavioralToMixedJoint
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            g hctx σ).toProfile π).toReal *
        (∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              ((observedProgramFOSG g hctx).pureToBehavioral π.extend)
              h).toReal *
            (observedProgramHistoryOutcome g hctx h who : ℝ))
      = ∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              (toObservedProgramReachableLegalBehavioralProfile
                g hctx σ).toProfile.extend
              h).toReal *
            (observedProgramHistoryOutcome g hctx h who : ℝ) := by
          exact observedProgramProjectedPayoff_behavioral_to_mixed_reachable
            g hctx LF σ who
    _ = ∑ h : (observedProgramFOSG g hctx).History,
          (observedProgramRunDist g hctx LF
            (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
            (observedProgramHistoryOutcome g hctx h who : ℝ) := by
          exact observedProgramProjectedPayoff_terminalWeight_reachable_eq_runDist
            g hctx LF σ who
    _ = (toKernelGame g).eu σ who := by
          exact observedProgramProjectedPayoff_runDist_eq_toKernelGame_eu
            g hctx LF σ who

/-- Native-FOSG run-distribution form of reachable-coordinate FOSG M→B.

This is the Vegas-facing distribution theorem: the witness is a legal
reachable FOSG behavioral profile, and the left side is the ordinary FOSG
`runDist` of its global extension. -/
theorem observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [Fintype (CursorCheckedWorld g)]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    [Fintype (observedProgramFOSG g hctx).History]
    [DecidablePred (observedProgramFOSG g hctx).terminal]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := observedProgramFOSG g hctx)) :
    ∃ β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := observedProgramFOSG g hctx) μ).bind
          (fun π =>
            PMF.map (observedProgramHistoryOutcome g hctx)
              (GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile
                (G := observedProgramFOSG g hctx)
                (observedProgramFOSG_legalObservable g hctx)
                (syntaxSteps g.prog) π)) := by
  obtain ⟨β, hdist⟩ :=
    GameTheory.FOSG.Kuhn.reachable_mixed_to_legal_behavioral_runDist
      (G := observedProgramFOSG g hctx)
      (observedProgramFOSG_legalObservable g hctx)
      μ (syntaxSteps g.prog)
  refine ⟨β, ?_⟩
  rw [hdist, PMF.map_bind]
  congr
  funext π
  rw [← GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile_eq_runDist
    (G := observedProgramFOSG g hctx)
    (observedProgramFOSG_legalObservable g hctx)]

/-- Finite-valuation wrapper for
`observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist`. -/
theorem observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist_finite
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := observedProgramFOSG g hctx)) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := observedProgramFOSG g hctx) μ).bind
          (fun π =>
            PMF.map (observedProgramHistoryOutcome g hctx)
              (GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile
                (G := observedProgramFOSG g hctx)
                (observedProgramFOSG_legalObservable g hctx)
                (syntaxSteps g.prog) π)) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  exact observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist
    g hctx μ

/-- Strategic KernelGame collapse of the observed-program FOSG, using legal
reachable behavioral strategies as the strategic choices.

This is the KernelGame view of the sequential FOSG denotation. Its outcome
kernel is the finite-horizon FOSG run distribution, pushed forward to Vegas
payoff outcomes. -/
noncomputable def observedProgramReachableKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P] : GameTheory.KernelGame P where
  Strategy := fun who =>
    (observedProgramFOSG g hctx).ReachableLegalBehavioralStrategy who
  Outcome := Outcome P
  utility := fun o who => (o who : ℝ)
  outcomeKernel := fun β => by
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    exact PMF.map (observedProgramHistoryOutcome g hctx)
      ((observedProgramFOSG g hctx).runDist
        (syntaxSteps g.prog)
        (GameTheory.FOSG.ReachableLegalBehavioralProfile.extend
          (G := observedProgramFOSG g hctx) β))

@[simp] theorem observedProgramReachableKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile) :
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    (observedProgramReachableKernelGame g hctx LF).outcomeKernel β =
      PMF.map (observedProgramHistoryOutcome g hctx)
        ((observedProgramFOSG g hctx).runDist
          (syntaxSteps g.prog) β.extend) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  rfl

/-- Product-mixed Vegas-pure specialization of reachable-coordinate FOSG M→B,
stated over native FOSG execution.

The witness is a legal reachable behavioral profile for the observed-program
FOSG. The preserved object is the pushforward distribution on Vegas outcomes;
expected-utility preservation is a corollary of this distribution statement. -/
theorem observedProgramReachable_vegasMixedPure_runDist_toStrategicKernelGame_finite
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β.extend) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hdist⟩ :=
    observedProgramReachable_mixed_to_legal_behavioral_runDist_outcomeDist
      g hctx (toObservedProgramReachableMixedPureProfile g hctx μ)
  refine ⟨β, ?_⟩
  rw [toObservedProgramReachableMixedPureProfile_joint] at hdist
  rw [PMF.bind_map] at hdist
  rw [hdist]
  apply congrArg
  funext σ
  exact observedProgramReachablePureOutcomeKernel_eq_toStrategicKernelGame
    g hctx LF σ

/-- Product-mixed Vegas-pure specialization of FOSG M→B with a total FOSG
behavioral witness.

The proof still uses the bounded-history reachable theorem internally, then
extends the reachable behavioral profile to a total legal FOSG behavioral
profile. This avoids any finiteness assumption on the full FOSG information
state space. -/
theorem observedProgramFullFOSG_vegasMixedPure_runDist_toStrategicKernelGame_finite
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    letI : Fintype (CursorCheckedWorld g) :=
      observedProgramFOSG.instFintypeWorld g hctx LF
    letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
      fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal g hctx
    ∃ β : (observedProgramFOSG g hctx).LegalBehavioralProfile,
      PMF.map (observedProgramHistoryOutcome g hctx)
          ((observedProgramFOSG g hctx).runDist
            (syntaxSteps g.prog) β) =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hβ⟩ :=
    observedProgramReachable_vegasMixedPure_runDist_toStrategicKernelGame_finite
      g hctx LF μ
  exact ⟨β.extend, hβ⟩

/-- KernelGame-shaped FOSG Kuhn corollary for Vegas.

A product mixed profile over legal Vegas pure strategies is realized by a legal
reachable behavioral profile in the KernelGame collapse of the observed-program
FOSG, with the same distribution over Vegas payoff outcomes. -/
theorem observedProgramReachableKernelGame_mixedPure_realization
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (μ : ∀ who, PMF (LegalProgramPureStrategy g who)) :
    letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
      fun who => LegalProgramPureStrategy.instFintype g LF who
    ∃ β : GameTheory.KernelGame.Profile
        (observedProgramReachableKernelGame g hctx LF),
      (observedProgramReachableKernelGame g hctx LF).outcomeKernel β =
        (Math.PMFProduct.pmfPi μ).bind
          (fun σ => (toStrategicKernelGame g).outcomeKernel σ) := by
  letI : ∀ who, Fintype (LegalProgramPureStrategy g who) :=
    fun who => LegalProgramPureStrategy.instFintype g LF who
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P, Fintype (Option (ProgramAction g.prog who)) :=
    fun who => observedProgramFOSG.instFintypeOptionAction g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  obtain ⟨β, hβ⟩ :=
    observedProgramReachable_vegasMixedPure_runDist_toStrategicKernelGame_finite
      g hctx LF μ
  refine ⟨β, ?_⟩
  simpa using hβ

end Observed

end FOSGBridge
end Vegas
