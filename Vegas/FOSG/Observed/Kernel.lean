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
      (P := P) (L := L) (p := w.prog)
      (σ := w.suffix.behavioralProfile (fun i => (σ i).val))
      w.normalized)

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
          let σp : ProgramBehavioralProfile (P := P) (L := L)
              (.commit x who R k) :=
            suffix.behavioralProfile (fun i => (σ i).val)
          let d := ProgramBehavioralStrategy.headKernel (P := P) (L := L)
            (σp who) (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
          have hd : FDist.totalWeight d = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              (P := P) (L := L) (σp who)
              (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
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
    (suffix : ProgramSuffix (P := P) (L := L) g.prog (.commit x who R k))
    (wctx : WFCtx Γ) (fresh : FreshBindings (.commit x who R k))
    (viewScoped : ViewScoped (.commit x who R k))
    (normalized : NormalizedDists (.commit x who R k))
    (legal : Legal (.commit x who R k)) :
    (moveAtProgramCursor g hctx σ who suffix
        (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))).bind
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
      checkedProfileStep (P := P) (L := L) g hctx σ
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
          (P := P) (L := L)
          ((suffix.behavioralProfile (fun i => ↑(σ i))) who)
          (projectViewEnv who env.eraseEnv))))
    (f := fun v =>
      if hty : (ProgramAction.commitAt (P := P) (L := L) suffix v).cursor.ty = b then
        PMF.pure
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _)
               (hty ▸ (ProgramAction.commitAt (P := P) (L := L) suffix v).value) env
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
    by_cases hty : (ProgramAction.commitAt (P := P) (L := L) suffix v).cursor.ty = b
    · dsimp only
      rw [dif_pos hty]
      have hv :
          hty ▸ (ProgramAction.commitAt (P := P) (L := L) suffix v).value = v :=
        ProgramAction.commitAt_value_cast (P := P) (L := L) suffix v hty
      have henv :
          VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who _)
              (hty ▸ (ProgramAction.commitAt (P := P) (L := L) suffix v).value) env =
            VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who _) v env :=
        VEnv.cons_ext hv rfl
      rw [henv]
    · exact False.elim
        (hty (ProgramSuffix.ty_commitCursor (P := P) (L := L) suffix))




theorem checkedTransition_eq_checkedProfileStep_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (hactive : checkedActive w = ∅) :
    checkedTransition (P := P) (L := L) w a =
      checkedProfileStep (P := P) (L := L) g hctx σ w := by
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

/-- At an observed-program history with no active players, the FOSG
legal-action law followed by the checked-world transition is the Vegas
small-step kernel. This discharges the `let`, `sample`, and `reveal` one-step
cases; commit states are handled separately by their singleton active player. -/
theorem observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who))]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG (P := P) (L := L) g hctx).History)
    (hterm : ¬ (observedProgramFOSG (P := P) (L := L) g hctx).terminal h.lastState)
    (hactive :
      (observedProgramFOSG (P := P) (L := L) g hctx).active h.lastState = ∅) :
    ((observedProgramFOSG (P := P) (L := L) g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx))
          ((observedProgramFOSG (P := P) (L := L) g hctx).transition
            h.lastState a)) =
      checkedProfileStep (P := P) (L := L) g hctx σ
        (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx)
          h.lastState) := by
  rw [GameTheory.FOSG.legalActionLaw_eq_pure_noop_of_active_empty
    (G := observedProgramFOSG (P := P) (L := L) g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm hactive]
  simp only [PMF.pure_bind]
  rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
    (P := P) (L := L) (hctx := hctx)
    (w := h.lastState)
    (a := ⟨GameTheory.FOSG.noopAction
        (fun who : P => ProgramAction (P := P) (L := L) g.prog who),
      (observedProgramFOSG (P := P) (L := L) g hctx)
        |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩)]
  apply checkedTransition_eq_checkedProfileStep_of_active_empty
  simpa [observedProgramFOSG, checkedActive, CheckedWorld.ofCursorChecked,
    CursorCheckedWorld.active] using hactive

/-- If a player is active in the observed-program FOSG, the cursor endpoint is
a commit node owned by that player, and all checked-world projections expose
the same commit data. -/
theorem observedProgram_active_mem_commitData
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (w : CursorCheckedWorld (P := P) (L := L) g)
    {who : P}
    (hmem : who ∈
      (observedProgramFOSG (P := P) (L := L) g hctx).active w) :
    ∃ (Γ : VCtx P L) (x : VarId) (b : L.Ty)
      (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
      (k : VegasCore P L ((x, .hidden who b) :: Γ))
      (env : VEnv L Γ)
      (suffix : ProgramSuffix (P := P) (L := L) g.prog
        (.commit x who R k))
      (wctx : WFCtx Γ)
      (fresh : FreshBindings (.commit x who R k))
      (viewScoped : ViewScoped (.commit x who R k))
      (normalized : NormalizedDists (.commit x who R k))
      (legal : Legal (.commit x who R k)),
      CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx) w =
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
              let suffix : ProgramSuffix (P := P) (L := L) g.prog
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
    [∀ who : P, Fintype (Option (ProgramAction (P := P) (L := L) g.prog who))]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    ((observedProgramFOSG (P := P) (L := L) g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx))
          ((observedProgramFOSG (P := P) (L := L) g hctx).transition
            h.lastState a)) =
      checkedProfileStep (P := P) (L := L) g hctx σ
        (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx)
          h.lastState) := by
  let G := observedProgramFOSG (P := P) (L := L) g hctx
  by_cases hactive : G.active h.lastState = ∅
  · exact observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep_of_active_empty
      (P := P) (L := L) g hctx σ h hterm hactive
  · have hne : (G.active h.lastState).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    rcases hne with ⟨who, hmem⟩
    rcases observedProgram_active_mem_commitData
        (P := P) (L := L) g hctx h.lastState hmem with
      ⟨Γ, x, b, R, k, env, suffix, wctx, fresh, viewScoped,
        normalized, legal, hchecked, hworld⟩
    let f : Option (ProgramAction (P := P) (L := L) g.prog who) →
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
        PMF.map (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx))
          (G.transition h.lastState a) = f (a.1 who) := by
      intro a
      rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
        (P := P) (L := L) (hctx := hctx) (w := h.lastState) (a := a)]
      have haRaw : JointActionLegal
          ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } : World P L)
          (ProgramJointAction.toAction a.1) := by
        have hto := CursorProgramJointActionLegal.toAction a.2
        simpa [hworld] using hto
      rw [checkedTransition_congr_checkedWorld
        (P := P) (L := L) (hw := hchecked)
        (a := ProgramJointAction.toAction a.1)
        (ha₂ := by
          simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
            checkedAvailableActions, CheckedWorld.toWorld] using haRaw)]
      simpa [f] using
        checkedTransition_commit_eq_programActionContinuation
          (P := P) (L := L) g hctx env suffix wctx fresh viewScoped
          normalized legal a.1 haRaw
    calc
      ((observedProgramFOSG (P := P) (L := L) g hctx).legalActionLaw
          (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
        (fun a =>
          PMF.map (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx))
            ((observedProgramFOSG (P := P) (L := L) g hctx).transition
              h.lastState a))
          = ((observedProgramFOSG (P := P) (L := L) g hctx).legalActionLaw
              (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
              (fun a => f (a.1 who)) := by
                congr
                funext a
                exact hK a
      _ = (moveAtCursorWorld (P := P) (L := L) g hctx σ who h.lastState).bind f := by
        exact observedProgramLegalActionLaw_bind_coord
          (P := P) (L := L) g hctx σ h hterm who f
      _ = checkedProfileStep (P := P) (L := L) g hctx σ
          (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx)
            h.lastState) := by
        rw [← moveAtCheckedWorld_ofCursorChecked
          (P := P) (L := L) g hctx σ who h.lastState]
        rw [hchecked]
        exact moveAtProgramCursor_bind_commitContinuation_eq_checkedProfileStep
          (P := P) (L := L) g hctx σ env suffix wctx fresh viewScoped
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
    checkedVegasOutcomeKernel (P := P) (L := L) σ w =
      PMF.pure (checkedWorldOutcome (P := P) (L := L) w) := by
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

/-- One semantic small step preserves the remaining Vegas denotation. This is
the hard preservation equation in the proof architecture; it is proved at the
suffix-based machine level before involving the finite FOSG cursor encoding. -/
theorem checkedProfileStep_bind_checkedVegasOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx) :
    (checkedProfileStep (P := P) (L := L) g hctx σ w).bind
        (checkedVegasOutcomeKernel (P := P) (L := L) σ) =
      checkedVegasOutcomeKernel (P := P) (L := L) σ w := by
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
                    (P := P) (L := L) (p := k)
                    (σ := suffix.behavioralProfile (fun i => (σ i).val))
                    normalized.2)) =
              ((L.evalDist D (VEnv.eraseSampleEnv env)).bind fun v =>
                outcomeDistBehavioral k
                  (suffix.behavioralProfile (fun i => (σ i).val))
                  (VEnv.cons (Player := P) (L := L) (x := x)
                    (τ := .pub _) v env)).toPMF
                (outcomeDistBehavioral_totalWeight_eq_one
                  (P := P) (L := L) (p := VegasCore.sample x D k)
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
                (P := P) (L := L) (p := k)
                (σ := suffix.behavioralProfile (fun i => (σ i).val))
                normalized.2)
            (outcomeDistBehavioral_totalWeight_eq_one
              (P := P) (L := L) (p := VegasCore.sample x D k)
              (σ := suffix.behavioralProfile (fun i => (σ i).val))
              ⟨normalized.1, normalized.2⟩)]
      | commit x who R k =>
          simp only [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral]
          rw [PMF.bind_map]
          have hd :
              FDist.totalWeight
                (ProgramBehavioralStrategy.headKernel (P := P) (L := L)
                  ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                  (projectViewEnv (P := P) (L := L) who
                    (VEnv.eraseEnv env))) = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              (P := P) (L := L)
              ((suffix.behavioralProfile (fun i => (σ i).val)) who)
              (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
          change
            ((ProgramBehavioralStrategy.headKernel (P := P) (L := L)
                ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                (projectViewEnv (P := P) (L := L) who
                  (VEnv.eraseEnv env))).toPMF hd).bind
              (fun v =>
                (outcomeDistBehavioral k
                    (ProgramBehavioralProfile.tail (P := P) (L := L)
                      (suffix.behavioralProfile (fun i => (σ i).val)))
                    (VEnv.cons (Player := P) (L := L) (x := x)
                      (τ := .hidden who _) v env)).toPMF
                  (outcomeDistBehavioral_totalWeight_eq_one
                    (P := P) (L := L) (p := k)
                    (σ := ProgramBehavioralProfile.tail (P := P) (L := L)
                      (suffix.behavioralProfile (fun i => (σ i).val)))
                    normalized)) =
              ((ProgramBehavioralStrategy.headKernel (P := P) (L := L)
                  ((suffix.behavioralProfile (fun i => (σ i).val)) who)
                  (projectViewEnv (P := P) (L := L) who
                    (VEnv.eraseEnv env))).bind fun v =>
                outcomeDistBehavioral k
                  (ProgramBehavioralProfile.tail (P := P) (L := L)
                    (suffix.behavioralProfile (fun i => (σ i).val)))
                  (VEnv.cons (Player := P) (L := L) (x := x)
                    (τ := .hidden who _) v env)).toPMF
                (outcomeDistBehavioral_totalWeight_eq_one
                  (P := P) (L := L) (p := VegasCore.commit x who R k)
                  (σ := suffix.behavioralProfile (fun i => (σ i).val))
                  normalized)
          rw [← FDist.toPMF_bind
            (ProgramBehavioralStrategy.headKernel (P := P) (L := L)
              ((suffix.behavioralProfile (fun i => (σ i).val)) who)
              (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env)))
            (fun v =>
              outcomeDistBehavioral k
                (ProgramBehavioralProfile.tail (P := P) (L := L)
                  (suffix.behavioralProfile (fun i => (σ i).val)))
                (VEnv.cons (Player := P) (L := L) (x := x)
                  (τ := .hidden who _) v env))
            hd
            (fun v =>
              outcomeDistBehavioral_totalWeight_eq_one
                (P := P) (L := L) (p := k)
                (σ := ProgramBehavioralProfile.tail (P := P) (L := L)
                  (suffix.behavioralProfile (fun i => (σ i).val)))
                normalized)
            (outcomeDistBehavioral_totalWeight_eq_one
              (P := P) (L := L) (p := VegasCore.commit x who R k)
              (σ := suffix.behavioralProfile (fun i => (σ i).val))
              normalized)]
      | reveal y who x hx k =>
          simp [checkedProfileStep, checkedVegasOutcomeKernel,
            outcomeDistBehavioral, VEnv.get]

set_option linter.flexible false in
/-- Every supported nonterminal semantic small step consumes exactly one Vegas
syntax node. -/
theorem checkedProfileStep_remainingSyntaxSteps
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx)
    (hterm : ¬ checkedTerminal w)
    (dst : CheckedWorld g hctx)
    (hsupp : checkedProfileStep (P := P) (L := L) g hctx σ w dst ≠ 0) :
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
        (checkedProfileStep (P := P) (L := L) g hctx σ w).bind
          (checkedProfileRun g hctx σ n)

@[simp] theorem checkedProfileRun_zero
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (w : CheckedWorld g hctx) :
    checkedProfileRun (P := P) (L := L) g hctx σ 0 w = PMF.pure w := rfl

@[simp] theorem checkedProfileRun_succ_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedProfileRun (P := P) (L := L) g hctx σ (n + 1) w =
      PMF.pure w := by
  simp [checkedProfileRun, hterm]

@[simp] theorem checkedProfileRun_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : checkedTerminal w) :
    checkedProfileRun (P := P) (L := L) g hctx σ n w =
      PMF.pure w := by
  cases n with
  | zero => rfl
  | succ n =>
      exact checkedProfileRun_succ_terminal
        (P := P) (L := L) g hctx σ n w hterm

theorem checkedProfileRun_succ_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (hterm : ¬ checkedTerminal w) :
    checkedProfileRun (P := P) (L := L) g hctx σ (n + 1) w =
      (checkedProfileStep (P := P) (L := L) g hctx σ w).bind
        (checkedProfileRun (P := P) (L := L) g hctx σ n) := by
  simp [checkedProfileRun, hterm]

theorem checkedTransition_bind_checkedProfileRun_eq_checkedProfileRun_succ_of_active_empty
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (w : CheckedWorld g hctx)
    (a : {a : JointAction P L // CheckedJointActionLegal w a})
    (hterm : ¬ checkedTerminal w)
    (hactive : checkedActive w = ∅) :
    (checkedTransition (P := P) (L := L) w a).bind
        (checkedProfileRun (P := P) (L := L) g hctx σ n) =
      checkedProfileRun (P := P) (L := L) g hctx σ (n + 1) w := by
  rw [checkedTransition_eq_checkedProfileStep_of_active_empty
    (P := P) (L := L) g hctx σ w a hactive]
  rw [checkedProfileRun_succ_nonterminal
    (P := P) (L := L) g hctx σ n w hterm]

/-- Any finite run of the suffix-based Vegas semantic machine preserves the
remaining denotational outcome kernel. -/
theorem checkedProfileRun_bind_checkedVegasOutcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    ∀ (n : Nat) (w : CheckedWorld g hctx),
      (checkedProfileRun (P := P) (L := L) g hctx σ n w).bind
          (checkedVegasOutcomeKernel (P := P) (L := L) σ) =
        checkedVegasOutcomeKernel (P := P) (L := L) σ w := by
  intro n
  induction n with
  | zero =>
      intro w
      simp
  | succ n ih =>
      intro w
      by_cases hterm : checkedTerminal w
      · rw [checkedProfileRun_succ_terminal
          (P := P) (L := L) g hctx σ n w hterm]
        simp
      · rw [checkedProfileRun_succ_nonterminal
          (P := P) (L := L) g hctx σ n w hterm]
        rw [PMF.bind_bind]
        conv_lhs =>
          arg 2
          intro w'
          rw [ih w']
        exact checkedProfileStep_bind_checkedVegasOutcomeKernel
          (P := P) (L := L) g hctx σ w

/-- Once the semantic run horizon covers the remaining syntax depth, every
supported destination is terminal. -/
theorem checkedProfileRun_support_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    ∀ (n : Nat) (w dst : CheckedWorld g hctx),
      w.remainingSyntaxSteps ≤ n →
      dst ∈ (checkedProfileRun (P := P) (L := L) g hctx σ n w).support →
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
          (P := P) (L := L) g hctx σ n w hterm] at hdst
        have hdstEq : dst = w := by
          simpa using hdst
        subst dst
        exact hterm
      · rw [checkedProfileRun_succ_nonterminal
          (P := P) (L := L) g hctx σ n w hterm] at hdst
        rw [PMF.mem_support_bind_iff] at hdst
        rcases hdst with ⟨mid, hmid, hdst⟩
        have hstep := checkedProfileStep_remainingSyntaxSteps
          (P := P) (L := L) g hctx σ w hterm mid
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
        (checkedProfileRun (P := P) (L := L) g hctx σ n w) =
      checkedVegasOutcomeKernel (P := P) (L := L) σ w := by
  rw [← PMF.bind_pure_comp]
  rw [Math.ProbabilityMassFunction.bind_congr_on_support
    (checkedProfileRun (P := P) (L := L) g hctx σ n w)
    (PMF.pure ∘ checkedWorldOutcome (P := P) (L := L))
    (checkedVegasOutcomeKernel (P := P) (L := L) σ)]
  · exact checkedProfileRun_bind_checkedVegasOutcomeKernel
      (P := P) (L := L) g hctx σ n w
  · intro dst hdst
    have hterm := checkedProfileRun_support_terminal
      (P := P) (L := L) g hctx σ n w dst hn hdst
    rw [checkedVegasOutcomeKernel_terminal
      (P := P) (L := L) σ dst hterm]
    rfl

@[simp] theorem checkedVegasOutcomeKernel_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    checkedVegasOutcomeKernel (P := P) (L := L) σ
        (CheckedWorld.initial (P := P) (L := L) g hctx) =
      (toKernelGame g).outcomeKernel σ := rfl

/-- The suffix-based Vegas semantic machine, run for the syntactic horizon
from the initial checked world and projected to payoff outcomes, agrees with
the user-facing kernel-game semantics. -/
theorem checkedProfileRun_initial_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g) :
    PMF.map (checkedWorldOutcome (P := P) (L := L))
        (checkedProfileRun (P := P) (L := L) g hctx σ
          (syntaxSteps g.prog)
          (CheckedWorld.initial (P := P) (L := L) g hctx)) =
      (toKernelGame g).outcomeKernel σ := by
  rw [checkedProfileRun_map_checkedWorldOutcome_eq_checkedVegasOutcomeKernel
    (P := P) (L := L) g hctx σ (syntaxSteps g.prog)
    (CheckedWorld.initial (P := P) (L := L) g hctx)]
  · rfl
  · rfl

@[simp] theorem checkedVegasOutcomeKernel_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (σ : LegalProgramBehavioralProfile g)
    (w : CursorCheckedWorld (P := P) (L := L) g) :
    checkedVegasOutcomeKernel (P := P) (L := L) (hctx := hctx) σ
        (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx) w) =
      cursorVegasOutcomeKernel (P := P) (L := L) σ w := rfl

@[simp] theorem checkedWorldOutcome_ofCursorChecked
    {g : WFProgram P L} {hctx : WFCtx g.Γ}
    (w : CursorCheckedWorld (P := P) (L := L) g) :
    checkedWorldOutcome (P := P) (L := L)
        (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx) w) =
      cursorWorldOutcome (P := P) (L := L) w := by
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
  CheckedWorld.ofCursorChecked (P := P) (L := L) h.lastState

@[simp] theorem checkedWorldOutcome_observedProgramHistoryCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    checkedWorldOutcome (P := P) (L := L)
        (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) =
      observedProgramHistoryOutcome (P := P) (L := L) g hctx h := by
  simp [observedProgramHistoryCheckedWorld, observedProgramHistoryOutcome]

@[simp] theorem checkedTerminal_observedProgramHistoryCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History) :
    checkedTerminal
        (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) ↔
      (observedProgramFOSG (P := P) (L := L) g hctx).terminal h.lastState := by
  simp [observedProgramHistoryCheckedWorld, observedProgramFOSG,
    checkedTerminal, CheckedWorld.ofCursorChecked,
    CursorCheckedWorld.terminal, CursorCheckedWorld.toWorld,
    CheckedWorld.toWorld]

theorem observedProgramHistoryCheckedWorld_extendByOutcome_of_support
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld (P := P) (L := L) g)
    (hsupp :
      (observedProgramFOSG (P := P) (L := L) g hctx).transition
        h.lastState a dst ≠ 0) :
    observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx
        (h.extendByOutcome a dst) =
      CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx) dst := by
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
  PMF.map (observedProgramHistoryOutcome (P := P) (L := L) g hctx)
    (observedProgramRunDist (P := P) (L := L) g hctx LF
      (toObservedProgramLegalBehavioralProfile g hctx σ))

/-- Re-express the observed-program outcome kernel as the checked-world
outcome projection of the final FOSG history state. This is just projection
bookkeeping; `observedProgramCheckedWorldRunDist_eq_checkedProfileRun` proves
the corresponding checked-world run adequacy. -/
theorem observedProgramOutcomeKernel_eq_checkedWorldProjection
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel (P := P) (L := L) g hctx LF σ =
      PMF.map (checkedWorldOutcome (P := P) (L := L))
        (PMF.map
          (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx)
          (observedProgramRunDist (P := P) (L := L) g hctx LF
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
  PMF.map (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx)
    (observedProgramRunDist (P := P) (L := L) g hctx LF
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
  PMF.map (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx)
    (observedProgramRunDistFrom (P := P) (L := L) g hctx LF
      (toObservedProgramLegalBehavioralProfile g hctx σ) n h)

@[simp] theorem observedProgramCheckedWorldRunDistFrom_zero
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (h : (observedProgramFOSG g hctx).History) :
    observedProgramCheckedWorldRunDistFrom
        (P := P) (L := L) g hctx LF σ 0 h =
      PMF.pure
        (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) := by
  simp [observedProgramCheckedWorldRunDistFrom, observedProgramRunDistFrom,
    PMF.pure_map]

theorem observedProgramCheckedWorldRunDist_eq_runDistFrom_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramCheckedWorldRunDist
        (P := P) (L := L) g hctx LF σ =
      observedProgramCheckedWorldRunDistFrom
        (P := P) (L := L) g hctx LF σ
        (syntaxSteps g.prog)
        (GameTheory.FOSG.History.nil
          (observedProgramFOSG (P := P) (L := L) g hctx)) := by
  rfl

theorem observedProgramCheckedWorldRunDistFrom_terminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFrom
        (P := P) (L := L) g hctx LF σ n h =
      PMF.pure
        (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  unfold observedProgramCheckedWorldRunDistFrom observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_terminal
    (G := observedProgramFOSG (P := P) (L := L) g hctx)
    (toObservedProgramLegalBehavioralProfile g hctx σ) n h hterm]
  rw [PMF.pure_map]

theorem observedProgramCheckedWorldRunDistFrom_terminal_eq_checkedProfileRun
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFrom
        (P := P) (L := L) g hctx LF σ n h =
      checkedProfileRun (P := P) (L := L) g hctx σ n
        (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) := by
  rw [observedProgramCheckedWorldRunDistFrom_terminal
    (P := P) (L := L) g hctx LF σ n h hterm]
  rw [checkedProfileRun_terminal]
  exact (checkedTerminal_observedProgramHistoryCheckedWorld
    (P := P) (L := L) g hctx h).2 hterm

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
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  exact
    ((observedProgramFOSG (P := P) (L := L) g hctx).legalActionLaw
        (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm).bind
      (fun a =>
        ((observedProgramFOSG (P := P) (L := L) g hctx).transition
            h.lastState a).bind
          (fun dst =>
            observedProgramCheckedWorldRunDistFrom
              (P := P) (L := L) g hctx LF σ n
              (h.extendByOutcome a dst)))

/-- Checked-world projection of the generic nonterminal FOSG run equation. -/
theorem observedProgramCheckedWorldRunDistFrom_succ_nonterminal
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g)
    (n : Nat) (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    observedProgramCheckedWorldRunDistFrom
        (P := P) (L := L) g hctx LF σ (n + 1) h =
      observedProgramCheckedWorldRunDistFromSucc
        (P := P) (L := L) g hctx LF σ n h hterm := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  unfold observedProgramCheckedWorldRunDistFromSucc
  unfold observedProgramCheckedWorldRunDistFrom observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_succ_nonterminal
    (G := observedProgramFOSG (P := P) (L := L) g hctx)
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
        (P := P) (L := L) g hctx LF σ (n + 1) h =
      ((observedProgramFOSG (P := P) (L := L) g hctx).transition h.lastState
          ⟨GameTheory.FOSG.noopAction
              (fun who : P => ProgramAction (P := P) (L := L) g.prog who),
            (observedProgramFOSG (P := P) (L := L) g hctx)
              |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩).bind
        (fun dst =>
          observedProgramCheckedWorldRunDistFrom
            (P := P) (L := L) g hctx LF σ n
            (h.extendByOutcome
              ⟨GameTheory.FOSG.noopAction
                  (fun who : P => ProgramAction (P := P) (L := L) g.prog who),
                (observedProgramFOSG (P := P) (L := L) g hctx)
                  |>.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩
              dst)) := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  unfold observedProgramCheckedWorldRunDistFrom observedProgramRunDistFrom
  rw [GameTheory.FOSG.History.runDistFrom_succ_active_empty
    (G := observedProgramFOSG (P := P) (L := L) g hctx)
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
          (P := P) (L := L) g hctx LF σ n h =
        checkedProfileRun (P := P) (L := L) g hctx σ n
          (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) := by
  intro n
  induction n with
  | zero =>
      intro h
      simp
  | succ n ih =>
      intro h
      by_cases hterm : (observedProgramFOSG (P := P) (L := L) g hctx).terminal
          h.lastState
      · exact observedProgramCheckedWorldRunDistFrom_terminal_eq_checkedProfileRun
          (P := P) (L := L) g hctx LF σ (n + 1) h hterm
      · letI : ∀ who : P,
            Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
          fun who =>
            observedProgramFOSG.instFintypeOptionAction
              (P := P) (L := L) g hctx LF who
        have hcheckedTerm :
            ¬ checkedTerminal
              (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h) := by
          intro ht
          exact hterm ((checkedTerminal_observedProgramHistoryCheckedWorld
            (P := P) (L := L) g hctx h).1 ht)
        rw [observedProgramCheckedWorldRunDistFrom_succ_nonterminal
          (P := P) (L := L) g hctx LF σ n h hterm]
        rw [checkedProfileRun_succ_nonterminal
          (P := P) (L := L) g hctx σ n
          (observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx h)
          hcheckedTerm]
        unfold observedProgramCheckedWorldRunDistFromSucc
        let G := observedProgramFOSG (P := P) (L := L) g hctx
        let law := G.legalActionLaw
          (toObservedProgramLegalBehavioralProfile g hctx σ) h hterm
        let step := fun a : G.LegalAction h.lastState =>
          G.transition h.lastState a
        let forget :=
          CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx)
        let run := checkedProfileRun (P := P) (L := L) g hctx σ n
        have hstep :
            law.bind (fun a => PMF.map forget (step a)) =
              checkedProfileStep (P := P) (L := L) g hctx σ
                (observedProgramHistoryCheckedWorld
                  (P := P) (L := L) g hctx h) := by
          simpa [G, law, step, forget, observedProgramHistoryCheckedWorld] using
            observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStep
              (P := P) (L := L) g hctx σ h hterm
        calc
          law.bind
              (fun a =>
                (step a).bind
                  (fun dst =>
                    observedProgramCheckedWorldRunDistFrom
                      (P := P) (L := L) g hctx LF σ n
                      (h.extendByOutcome a dst))) =
            law.bind
              (fun a =>
                (step a).bind
                  (fun dst =>
                    run
                      (observedProgramHistoryCheckedWorld
                        (P := P) (L := L) g hctx
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
                (P := P) (L := L) g hctx h a dst hsupp]
          _ =
            (law.bind (fun a => PMF.map forget (step a))).bind run := by
              rw [PMF.bind_bind]
              congr
              funext a
              simp [PMF.map, PMF.bind_bind]
          _ =
            (checkedProfileStep (P := P) (L := L) g hctx σ
              (observedProgramHistoryCheckedWorld
                (P := P) (L := L) g hctx h)).bind run := by
              rw [hstep]

@[simp] theorem observedProgramHistoryCheckedWorld_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    observedProgramHistoryCheckedWorld (P := P) (L := L) g hctx
        (GameTheory.FOSG.History.nil
          (observedProgramFOSG (P := P) (L := L) g hctx)) =
      CheckedWorld.initial (P := P) (L := L) g hctx := by
  rfl

theorem observedProgramCheckedWorldRunDist_eq_checkedProfileRun
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramCheckedWorldRunDist
        (P := P) (L := L) g hctx LF σ =
      checkedProfileRun (P := P) (L := L) g hctx σ
        (syntaxSteps g.prog)
        (CheckedWorld.initial (P := P) (L := L) g hctx) := by
  rw [observedProgramCheckedWorldRunDist_eq_runDistFrom_initial]
  rw [observedProgramCheckedWorldRunDistFrom_eq_checkedProfileRun]
  simp

theorem observedProgramOutcomeKernel_eq_checkedWorldRunDist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel (P := P) (L := L) g hctx LF σ =
      PMF.map (checkedWorldOutcome (P := P) (L := L))
        (observedProgramCheckedWorldRunDist
          (P := P) (L := L) g hctx LF σ) := by
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
          (P := P) (L := L) g hctx LF σ =
        checkedProfileRun (P := P) (L := L) g hctx σ
          (syntaxSteps g.prog)
          (CheckedWorld.initial (P := P) (L := L) g hctx)) :
    observedProgramOutcomeKernel (P := P) (L := L) g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  rw [observedProgramOutcomeKernel_eq_checkedWorldRunDist]
  rw [hadequacy]
  exact checkedProfileRun_initial_outcomeKernel
    (P := P) (L := L) g hctx σ

/-- Outcome preservation for the observed-program FOSG: running the FOSG with
the profile induced by a Vegas legal behavioral profile gives exactly the same
outcome kernel as the direct `toKernelGame` semantics. -/
theorem observedProgramOutcomeKernel_eq_toKernelGame
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel (P := P) (L := L) g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  exact observedProgramOutcomeKernel_eq_toKernelGame_of_checkedWorldRunDist_eq
    (P := P) (L := L) g hctx LF σ
    (observedProgramCheckedWorldRunDist_eq_checkedProfileRun
      (P := P) (L := L) g hctx LF σ)

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
  outcomeKernel := observedProgramOutcomeKernel (P := P) (L := L) g hctx LF

@[simp] theorem observedProgramOutcomeKernelGame_outcomeKernel
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramOutcomeKernelGame (P := P) (L := L) g hctx LF).outcomeKernel σ =
      observedProgramOutcomeKernel (P := P) (L := L) g hctx LF σ := rfl

@[simp] theorem observedProgramOutcomeKernelGame_udist
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    (observedProgramOutcomeKernelGame (P := P) (L := L) g hctx LF).udist σ =
      (toKernelGame g).udist σ := by
  simp [KernelGame.udist, observedProgramOutcomeKernelGame,
    observedProgramOutcomeKernel_eq_toKernelGame, toKernelGame]

@[simp] theorem observedProgramOutcomeKernelGame_eu
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    (observedProgramOutcomeKernelGame (P := P) (L := L) g hctx LF).eu σ who =
      (toKernelGame g).eu σ who := by
  simp [KernelGame.eu, observedProgramOutcomeKernelGame,
    observedProgramOutcomeKernel_eq_toKernelGame, toKernelGame]

theorem observedProgramProjectedPayoff_runDist_eq_toKernelGame_eu
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) (who : P) :
    letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
      observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
    letI : ∀ who : P,
        Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          (P := P) (L := L) g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory (P := P) (L := L) g hctx LF
    ∑ h : (observedProgramFOSG g hctx).History,
      (observedProgramRunDist (P := P) (L := L) g hctx LF
        (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
        (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ) =
      (toKernelGame g).eu σ who := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory (P := P) (L := L) g hctx LF
  calc
    ∑ h : (observedProgramFOSG g hctx).History,
      (observedProgramRunDist (P := P) (L := L) g hctx LF
        (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
        (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ)
      = (observedProgramOutcomeKernelGame
          (P := P) (L := L) g hctx LF).eu σ who := by
          symm
          rw [KernelGame.eu]
          change Math.Probability.expect
              (PMF.map (observedProgramHistoryOutcome (P := P) (L := L) g hctx)
                (observedProgramRunDist (P := P) (L := L) g hctx LF
                  (toObservedProgramLegalBehavioralProfile g hctx σ)))
              (fun o : Outcome P => (o who : ℝ)) =
            ∑ h : (observedProgramFOSG g hctx).History,
              (observedProgramRunDist (P := P) (L := L) g hctx LF
                (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
                (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ)
          rw [Math.Probability.expect_map_fintype_source]
    _ = (toKernelGame g).eu σ who := by
          exact observedProgramOutcomeKernelGame_eu
            (P := P) (L := L) g hctx LF σ who

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
    letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
      observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
    letI : ∀ who : P,
        Fintype (ProgramAction (P := P) (L := L) g.prog who) :=
      fun who =>
        ProgramAction.instFintype (P := P) (L := L) LF g.prog who
    letI : ∀ who : P,
        Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
      fun who =>
        observedProgramFOSG.instFintypeOptionAction
          (P := P) (L := L) g hctx LF who
    letI : Fintype (observedProgramFOSG g hctx).History :=
      observedProgramFOSG.instFintypeHistory (P := P) (L := L) g hctx LF
    letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
      observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
    ∑ π,
      (GameTheory.FOSG.Kuhn.reachableBehavioralToMixedJoint
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            (P := P) (L := L) g hctx σ).toProfile π).toReal *
        (∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              ((observedProgramFOSG g hctx).pureToBehavioral π.extend)
              h).toReal *
            (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ)) =
      (toKernelGame g).eu σ who := by
  letI : Fintype (CursorCheckedWorld (P := P) (L := L) g) :=
    observedProgramFOSG.instFintypeWorld (P := P) (L := L) g hctx LF
  letI : ∀ who : P,
      Fintype (ProgramAction (P := P) (L := L) g.prog who) :=
    fun who =>
      ProgramAction.instFintype (P := P) (L := L) LF g.prog who
  letI : ∀ who : P,
      Fintype (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        (P := P) (L := L) g hctx LF who
  letI : Fintype (observedProgramFOSG g hctx).History :=
    observedProgramFOSG.instFintypeHistory (P := P) (L := L) g hctx LF
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal (P := P) (L := L) g hctx
  calc
    ∑ π,
      (GameTheory.FOSG.Kuhn.reachableBehavioralToMixedJoint
          (G := observedProgramFOSG g hctx)
          (toObservedProgramReachableLegalBehavioralProfile
            (P := P) (L := L) g hctx σ).toProfile π).toReal *
        (∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              ((observedProgramFOSG g hctx).pureToBehavioral π.extend)
              h).toReal *
            (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ))
      = ∑ h : (observedProgramFOSG g hctx).History,
          (GameTheory.FOSG.History.terminalWeight
              (G := observedProgramFOSG g hctx)
              (toObservedProgramReachableLegalBehavioralProfile
                (P := P) (L := L) g hctx σ).toProfile.extend
              h).toReal *
            (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ) := by
          exact observedProgramProjectedPayoff_behavioral_to_mixed_reachable
            (P := P) (L := L) g hctx LF σ who
    _ = ∑ h : (observedProgramFOSG g hctx).History,
          (observedProgramRunDist (P := P) (L := L) g hctx LF
            (toObservedProgramLegalBehavioralProfile g hctx σ) h).toReal *
            (observedProgramHistoryOutcome (P := P) (L := L) g hctx h who : ℝ) := by
          exact observedProgramProjectedPayoff_terminalWeight_reachable_eq_runDist
            (P := P) (L := L) g hctx LF σ who
    _ = (toKernelGame g).eu σ who := by
          exact observedProgramProjectedPayoff_runDist_eq_toKernelGame_eu
            (P := P) (L := L) g hctx LF σ who

/-- Reachable-coordinate FOSG Kuhn M→B specialized to the observed-program
FOSG, with the remaining posterior-locality condition kept explicit.

This is the first Vegas-facing form of the new bounded-history FOSG M→B theorem.
Step-mass invariance and support factorization are discharged by GameTheory's
legal reachable-history step-determinism theorem. Legal observability is proved
above from the cursor/view observation design and guard view-scoping. -/
theorem observedProgramReachable_mixed_to_legal_behavioral_of_actionPosteriorLocal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction (P := P) (L := L) g.prog who))]
    [Fintype (observedProgramFOSG g hctx).History]
    (hLocal : ∀ who,
      GameTheory.FOSG.Kuhn.ReachableHistoryActionPosteriorLocal
        (G := observedProgramFOSG (P := P) (L := L) g hctx)
        (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx) who)
    (μ : GameTheory.FOSG.Kuhn.ReachableMixedProfile
      (G := observedProgramFOSG (P := P) (L := L) g hctx)) :
    ∃ βcore :
      (GameTheory.FOSG.Kuhn.toReachableHistoryObsModelCore
        (observedProgramFOSG g hctx)
        (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx)).BehavioralProfile,
    ∃ β : (observedProgramFOSG g hctx).ReachableLegalBehavioralProfile,
      β.toProfile =
        GameTheory.FOSG.Kuhn.eraseReachableHistoryBehavioral
          (G := observedProgramFOSG (P := P) (L := L) g hctx)
          (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx)
          βcore ∧
      GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDist
          (G := observedProgramFOSG (P := P) (L := L) g hctx)
          (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx)
          (syntaxSteps g.prog) βcore =
        (GameTheory.FOSG.Kuhn.reachableMixedProfileJoint
          (G := observedProgramFOSG (P := P) (L := L) g hctx) μ).bind
          (fun π =>
            GameTheory.FOSG.Kuhn.reachableHistoryOutcomeDistPureProfile
              (G := observedProgramFOSG (P := P) (L := L) g hctx)
              (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx)
              (syntaxSteps g.prog) π) := by
  exact GameTheory.FOSG.Kuhn.reachable_mixed_to_legal_behavioral
    (G := observedProgramFOSG (P := P) (L := L) g hctx)
    (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx)
    (GameTheory.FOSG.Kuhn.reachableHistory_stepMassInvariant
      (G := observedProgramFOSG (P := P) (L := L) g hctx)
      (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx))
    (GameTheory.FOSG.Kuhn.reachableHistory_stepSupportFactorization
      (G := observedProgramFOSG (P := P) (L := L) g hctx)
      (observedProgramFOSG_legalObservable (P := P) (L := L) g hctx))
    hLocal μ (syntaxSteps g.prog)

end Observed

end FOSGBridge
end Vegas
