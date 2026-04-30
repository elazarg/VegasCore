import GameTheory.Languages.FOSG.OutcomeClosure
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

/-- Vegas' denotational outcome kernel at the finite cursor world. This is the
cursor-native value used by the observed-program FOSG outcome proof. -/
noncomputable def cursorVegasOutcomeKernelPMF
    {g : WFProgram P L}
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CursorCheckedWorld g) : PMF (Outcome P) :=
  outcomeDistBehavioralPMF w.1.prog w.2.2.2.2.1
    (w.1.suffix.behavioralProfilePMF (fun i => (σ i).val)) w.1.env

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

@[simp] theorem checkedVegasOutcomeKernel_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfile g)
    (w : CursorCheckedWorld g) :
    checkedVegasOutcomeKernel (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      cursorVegasOutcomeKernel σ w := rfl

@[simp] theorem checkedVegasOutcomeKernelPMF_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CursorCheckedWorld g) :
    checkedVegasOutcomeKernelPMF (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      cursorVegasOutcomeKernelPMF σ w := rfl

@[simp] theorem cursorVegasOutcomeKernelPMF_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    cursorVegasOutcomeKernelPMF σ
        (CursorCheckedWorld.initial g hctx) =
      (toKernelGamePMF g).outcomeKernel σ := rfl

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
    (σ : LegalProgramBehavioralProfilePMF g)
    (w : CursorCheckedWorld g)
    (hterm : w.terminal) :
    cursorVegasOutcomeKernelPMF σ w =
      PMF.pure (cursorWorldOutcome w) := by
  have hchecked :
      checkedTerminal
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) := by
    simpa [checkedTerminal, CheckedWorld.ofCursorChecked,
      CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
      CheckedWorld.toWorld] using hterm
  rw [← checkedVegasOutcomeKernelPMF_ofCursorChecked (hctx := hctx) σ w]
  rw [← checkedWorldOutcome_ofCursorChecked (hctx := hctx) w]
  exact checkedVegasOutcomeKernelPMF_terminal
    (hctx := hctx) σ (CheckedWorld.ofCursorChecked (hctx := hctx) w)
    hchecked

theorem observedProgramFOSG_initial_remainingSyntaxSteps_le
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (observedProgramFOSG g hctx).init.remainingSyntaxSteps ≤
      syntaxSteps g.prog := by
  change
    syntaxSteps ((ProgramCursor.here : ProgramCursor g.prog).prog) ≤
      syntaxSteps g.prog
  change syntaxSteps g.prog ≤ syntaxSteps g.prog
  exact Nat.le_refl (syntaxSteps g.prog)

/-- Build observed-program outcome-value data directly over the finite cursor
world carrier.  Clients supply the cursor-local continuation value and prove
that one observed-program FOSG step preserves it. -/
noncomputable def observedProgramOutcomeValueOfCursorValue
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (cursorValue : CursorCheckedWorld g → PMF (Outcome P))
    (terminal_value :
      ∀ w, (observedProgramFOSG g hctx).terminal w →
        cursorValue w = PMF.pure (cursorWorldOutcome w))
    (step_value :
      ∀ h (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState),
        ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
            (fun a =>
              ((observedProgramFOSG g hctx).transition h.lastState a).bind
                (fun dst => cursorValue (h.extendByOutcome a dst).lastState)) =
          cursorValue h.lastState) :
    GameTheory.FOSG.History.OutcomeValue
      (G := observedProgramFOSG g hctx)
      β
      (Outcome P) where
  rank := fun h => h.lastState.remainingSyntaxSteps
  observe := observedProgramHistoryOutcome g hctx
  value := fun h => cursorValue h.lastState
  terminal_of_rank_zero := by
    intro h hrank
    exact (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
      (g := g) (w := h.lastState)).2 hrank
  terminal_value := by
    intro h hterm
    simpa [observedProgramHistoryOutcome] using
      terminal_value h.lastState hterm
  step_value := step_value
  step_rank := by
    intro h hterm a dst hsupp
    have hcursor :
        dst.remainingSyntaxSteps + 1 =
          h.lastState.remainingSyntaxSteps := by
      simpa [observedProgramFOSG] using
        cursorProgramTransition_remainingSyntaxSteps
          (g := g) h.lastState a dst hsupp
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := h) (a := a) (dst := dst) hsupp]
    simpa using hcursor

/-- Lift a projected checked-world one-step preservation proof to a
cursor-world continuation-value preservation proof.  This keeps checked worlds
as an internal proof device while the observed-program outcome value itself is
defined on the finite cursor carrier. -/
theorem observedProgramCursorStepValue_of_checkedStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (checkedStep : CheckedWorld g hctx → PMF (CheckedWorld g hctx))
    (checkedValue : CheckedWorld g hctx → PMF (Outcome P))
    (cursorValue : CursorCheckedWorld g → PMF (Outcome P))
    (hvalue :
      ∀ w,
        checkedValue (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
          cursorValue w)
    (checked_step_value :
      ∀ w, (checkedStep w).bind checkedValue = checkedValue w)
    (hstep :
      ∀ h (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState),
        ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
            (fun a =>
              PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
                ((observedProgramFOSG g hctx).transition h.lastState a)) =
          checkedStep
            (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)) :
    ∀ h (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState),
      ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
          (fun a =>
            ((observedProgramFOSG g hctx).transition h.lastState a).bind
              (fun dst => cursorValue (h.extendByOutcome a dst).lastState)) =
        cursorValue h.lastState := by
  intro h hterm
  let G := observedProgramFOSG g hctx
  let project : CursorCheckedWorld g → CheckedWorld g hctx :=
    CheckedWorld.ofCursorChecked (hctx := hctx)
  have hproject :
      (G.legalActionLaw β h hterm).bind
          (fun a => (G.transition h.lastState a).bind
            (fun dst => cursorValue (h.extendByOutcome a dst).lastState)) =
        (G.legalActionLaw β h hterm).bind
          (fun a => (G.transition h.lastState a).bind cursorValue) := by
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (G.legalActionLaw β h hterm) _ _ ?_
    intro a _ha
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      (G.transition h.lastState a) _ _ ?_
    intro dst hdst
    have hsupp : G.transition h.lastState a dst ≠ 0 := by
      simpa [PMF.mem_support_iff] using hdst
    rw [GameTheory.FOSG.History.extendByOutcome_of_support
      (h := h) (a := a) (dst := dst) hsupp]
    simp
  have hstep' :
      (G.legalActionLaw β h hterm).bind
          (fun a => PMF.map project (G.transition h.lastState a)) =
        checkedStep
          (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
    simpa [G, project] using hstep h hterm
  calc
    (G.legalActionLaw β h hterm).bind
        (fun a => (G.transition h.lastState a).bind
          (fun dst => cursorValue (h.extendByOutcome a dst).lastState)) =
      (G.legalActionLaw β h hterm).bind
        (fun a => (G.transition h.lastState a).bind cursorValue) := hproject
    _ =
      ((G.legalActionLaw β h hterm).bind
          (fun a => PMF.map project (G.transition h.lastState a))).bind
        checkedValue := by
          rw [PMF.bind_bind]
          congr 1
          funext a
          simp [PMF.map, PMF.bind_bind, project, hvalue]
    _ =
      (checkedStep
          (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)).bind
        checkedValue := by
          rw [hstep']
    _ =
      checkedValue
        (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
          exact checked_step_value
            (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState)
    _ = cursorValue h.lastState := hvalue h.lastState

/-- The Vegas continuation value on observed-program histories. -/
noncomputable def observedProgramOutcomeValue
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfile g) :
    GameTheory.FOSG.History.OutcomeValue
      (G := observedProgramFOSG g hctx)
      (toObservedProgramLegalBehavioralProfile g hctx σ)
      (Outcome P) :=
  observedProgramOutcomeValueOfCursorValue
    g hctx (toObservedProgramLegalBehavioralProfile g hctx σ)
    (cursorVegasOutcomeKernel σ)
    (by
      intro w hterm
      exact cursorVegasOutcomeKernel_terminal σ w hterm)
    (observedProgramCursorStepValue_of_checkedStep
      g hctx
      (toObservedProgramLegalBehavioralProfile g hctx σ)
      (checkedProfileStep g hctx σ)
      (checkedVegasOutcomeKernel (hctx := hctx) σ)
      (cursorVegasOutcomeKernel σ)
      (by intro w; rfl)
      (by
        intro w
        exact checkedProfileStep_bind_checkedVegasOutcomeKernel g hctx σ w)
      (by
        intro h hterm
        exact observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep
          g hctx σ h hterm))

/-- The Vegas PMF continuation value on observed-program histories. -/
noncomputable def observedProgramOutcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (σ : LegalProgramBehavioralProfilePMF g) :
    GameTheory.FOSG.History.OutcomeValue
      (G := observedProgramFOSG g hctx)
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ)
      (Outcome P) :=
  observedProgramOutcomeValueOfCursorValue
    g hctx (toObservedProgramLegalBehavioralProfilePMF g hctx σ)
    (cursorVegasOutcomeKernelPMF σ)
    (by
      intro w hterm
      exact cursorVegasOutcomeKernelPMF_terminal
        (hctx := hctx) σ w hterm)
    (observedProgramCursorStepValue_of_checkedStep
      g hctx
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ)
      (checkedProfileStepPMF g hctx σ)
      (checkedVegasOutcomeKernelPMF (hctx := hctx) σ)
      (cursorVegasOutcomeKernelPMF σ)
      (by intro w; rfl)
      (by
        intro w
        exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
          g hctx σ w)
      (by
        intro h hterm
        exact observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF
          g hctx σ h hterm))

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

theorem observedProgramOutcomeKernel_eq_toKernelGame_by_value
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  let R := observedProgramOutcomeValue g hctx σ
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (by
        change
          (observedProgramFOSG g hctx).init.remainingSyntaxSteps ≤
            syntaxSteps g.prog
        exact observedProgramFOSG_initial_remainingSyntaxSteps_le g hctx)
  simpa [R, observedProgramOutcomeValue, observedProgramOutcomeKernel]
    using hclosure

noncomputable def observedProgramOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) : PMF (Outcome P) :=
  PMF.map (observedProgramHistoryOutcome g hctx)
    (observedProgramRunDist g hctx LF
      (toObservedProgramLegalBehavioralProfilePMF g hctx σ))

theorem observedProgramOutcomeKernelPMF_eq_toKernelGamePMF_by_value
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      (toKernelGamePMF g).outcomeKernel σ := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  let R := observedProgramOutcomeValuePMF g hctx σ
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (by
        change
          (observedProgramFOSG g hctx).init.remainingSyntaxSteps ≤
            syntaxSteps g.prog
        exact observedProgramFOSG_initial_remainingSyntaxSteps_le g hctx)
  simpa [R, observedProgramOutcomeValuePMF, observedProgramOutcomeKernelPMF]
    using hclosure

theorem observedProgramOutcomeKernelPMF_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfilePMF g) :
    observedProgramOutcomeKernelPMF g hctx LF σ =
      (toKernelGamePMF g).outcomeKernel σ := by
  exact observedProgramOutcomeKernelPMF_eq_toKernelGamePMF_by_value
    g hctx LF σ

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

theorem observedProgramOutcomeKernel_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  exact observedProgramOutcomeKernel_eq_toKernelGame_by_value
    g hctx LF σ

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
