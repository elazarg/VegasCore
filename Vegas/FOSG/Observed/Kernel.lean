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

/-- Common bridge from an observed-program FOSG step to any checked-world
semantic step whose only active-state obligation is the commit continuation.

This factors the representation work shared by semantic step proofs:
active-empty states use the no-op action, while singleton active states reduce
the legal joint-action law to the active player's optional program move. -/
theorem observedProgramLegalActionLaw_bind_checkedTransition_eq_semanticStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (semanticStep : CheckedWorld g hctx → PMF (CheckedWorld g hctx))
    (empty_step :
      ∀ (h : (observedProgramFOSG g hctx).History)
        (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState),
        (observedProgramFOSG g hctx).active h.lastState = ∅ →
        ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
          (fun a =>
            PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
              ((observedProgramFOSG g hctx).transition
                h.lastState a)) =
          semanticStep
            (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState))
    (commit_step :
      ∀ (h : (observedProgramFOSG g hctx).History)
        (_hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState)
        {who : P}
        (_hmem : who ∈ (observedProgramFOSG g hctx).active h.lastState)
        (Γ : VCtx P L) (x : VarId) (b : L.Ty)
        (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool)
        (k : VegasCore P L ((x, .hidden who b) :: Γ))
        (env : VEnv L Γ)
        (suffix : ProgramSuffix g.prog (.commit x who R k))
        (wctx : WFCtx Γ)
        (fresh : FreshBindings (.commit x who R k))
        (viewScoped : ViewScoped (.commit x who R k))
        (normalized : NormalizedDists (.commit x who R k))
        (legal : Legal (.commit x who R k)),
        CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState =
          ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
             wctx := wctx, fresh := fresh, viewScoped := viewScoped,
             normalized := normalized, legal := legal } :
            CheckedWorld g hctx) →
        h.lastState.toWorld =
          ({ Γ := Γ, prog := .commit x who R k, env := env } : World P L) →
        privateObsOfCursorWorld who h.lastState =
          privateObsOfCommitSite suffix
            (projectViewEnv who (VEnv.eraseEnv env)) →
        ((β.toProfile who) (h.playerView who)).bind
            (checkedCommitContinuation g hctx env suffix wctx fresh
              viewScoped normalized legal) =
          semanticStep
            ({ Γ := Γ, prog := .commit x who R k, env := env, suffix := suffix,
               wctx := wctx, fresh := fresh, viewScoped := viewScoped,
               normalized := normalized, legal := legal } :
              CheckedWorld g hctx))
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition
            h.lastState a)) =
      semanticStep
        (CheckedWorld.ofCursorChecked (hctx := hctx)
          h.lastState) := by
  let G := observedProgramFOSG g hctx
  by_cases hactive : G.active h.lastState = ∅
  · exact empty_step h hterm hactive
  · have hne : (G.active h.lastState).Nonempty :=
      Finset.nonempty_iff_ne_empty.mpr hactive
    rcases hne with ⟨who, hmem⟩
    rcases observedProgram_active_mem_commitData
        g hctx h.lastState hmem with
      ⟨Γ, x, b, R, k, env, suffix, wctx, fresh, viewScoped,
        normalized, legal, hchecked, hworld, hobs⟩
    have hK : ∀ a : G.LegalAction h.lastState,
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          (G.transition h.lastState a) =
        checkedCommitContinuation g hctx env suffix wctx fresh
          viewScoped normalized legal (a.1 who) := by
      intro a
      rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
        (hctx := hctx) (w := h.lastState) (a := a)]
      have haRaw : JointActionLegal
          ({ Γ := Γ, prog := VegasCore.commit x who R k, env := env } :
            World P L)
          (ProgramJointAction.toAction a.1) := by
        have hto := CursorProgramJointActionLegal.toAction a.2
        simpa [hworld] using hto
      rw [checkedTransition_congr_checkedWorld
        (hw := hchecked)
        (a := ProgramJointAction.toAction a.1)
        (ha₂ := by
          simpa [CheckedJointActionLegal, checkedActive, checkedTerminal,
            checkedAvailableActions, CheckedWorld.toWorld] using haRaw)]
      simpa [checkedCommitContinuation] using
        checkedTransition_commit_eq_programActionContinuation
          g hctx env suffix wctx fresh viewScoped
          normalized legal a.1 haRaw
    calc
      (G.legalActionLaw β h hterm).bind
          (fun a =>
            PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
              (G.transition h.lastState a))
        = (G.legalActionLaw β h hterm).bind
            (fun a =>
              checkedCommitContinuation g hctx env suffix wctx fresh
                viewScoped normalized legal (a.1 who)) := by
              congr
              funext a
              exact hK a
      _ =
        ((β.toProfile who) (h.playerView who)).bind
            (checkedCommitContinuation g hctx env suffix wctx fresh
              viewScoped normalized legal) := by
          exact GameTheory.FOSG.legalActionLaw_bind_coord
            (G := G) β h hterm who
            (checkedCommitContinuation g hctx env suffix wctx fresh
              viewScoped normalized legal)
      _ =
        semanticStep
          (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
          rw [hchecked]
          exact commit_step h hterm hmem Γ x b R k env suffix wctx fresh
            viewScoped normalized legal hchecked hworld hobs

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
  refine observedProgramLegalActionLaw_bind_checkedTransition_eq_semanticStep
    g hctx (toObservedProgramLegalBehavioralProfilePMF g hctx σ)
    (checkedProfileStepPMF g hctx σ) ?_ ?_ h hterm
  · intro h hterm hactive
    exact
      observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF_empty
        g hctx σ h hterm hactive
  · intro h _hterm who _hmem Γ x b R k env suffix wctx fresh viewScoped
      normalized legal hchecked _hworld _hobs
    rw [show
        ((toObservedProgramLegalBehavioralProfilePMF g hctx σ).toProfile who
          (h.playerView who)) =
          moveAtCursorWorldPMF g hctx σ who h.lastState by
        simp [GameTheory.FOSG.LegalBehavioralProfile.toProfile,
          toObservedProgramLegalBehavioralProfilePMF_apply,
          programBehavioralProfilePMFCandidate_history]]
    rw [← moveAtCheckedWorldPMF_ofCursorChecked
      g hctx σ who h.lastState]
    rw [hchecked]
    exact moveAtProgramCursorPMF_bind_commitContinuation_eq_checkedProfileStepPMF
      g hctx σ env suffix wctx fresh viewScoped normalized legal

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

@[simp] theorem checkedVegasOutcomeKernelPMF_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g) :
    checkedVegasOutcomeKernelPMF σ
        (CheckedWorld.initial g hctx) =
      (toKernelGamePMF g).outcomeKernel σ := rfl

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
  GameTheory.FOSG.History.OutcomeValue.ofProjectedLastStateStep
    (G := observedProgramFOSG g hctx)
    (σ := toObservedProgramLegalBehavioralProfilePMF g hctx σ)
    (rankState := fun w => w.remainingSyntaxSteps)
    (observeState := cursorWorldOutcome)
    (project := CheckedWorld.ofCursorChecked (hctx := hctx))
    (semanticStep := checkedProfileStepPMF g hctx σ)
    (semanticValue := checkedVegasOutcomeKernelPMF (hctx := hctx) σ)
    (stateValue := cursorVegasOutcomeKernelPMF σ)
    (by
      intro w hrank
      exact (CursorCheckedWorld.terminal_iff_remainingSyntaxSteps_eq_zero
        (g := g) (w := w)).2 hrank)
    (by
      intro w hterm
      exact cursorVegasOutcomeKernelPMF_terminal
        (hctx := hctx) σ w hterm)
    (by intro w; rfl)
    (by
      intro w
      exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
        g hctx σ w)
    (by
      intro h hterm
      exact observedProgramLegalActionLawPMF_bind_checkedTransition_eq_checkedProfileStepPMF
        g hctx σ h hterm)
    (by
      intro h _hterm a dst hsupp
      simpa [observedProgramFOSG] using
        cursorProgramTransition_remainingSyntaxSteps
          (g := g) h.lastState a dst hsupp)

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

theorem observedProgramOutcomeKernel_eq_toKernelGame_by_pmf
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (σ : LegalProgramBehavioralProfile g) :
    observedProgramOutcomeKernel g hctx LF σ =
      (toKernelGame g).outcomeKernel σ := by
  let σpmf := LegalProgramBehavioralProfile.toPMFProfile σ
  have hobs :
      observedProgramOutcomeKernel g hctx LF σ =
        observedProgramOutcomeKernelPMF g hctx LF σpmf := by
    unfold observedProgramOutcomeKernel observedProgramOutcomeKernelPMF
    rw [toObservedProgramLegalBehavioralProfilePMF_toPMFProfile_eq]
  rw [hobs]
  rw [observedProgramOutcomeKernelPMF_eq_toKernelGamePMF]
  simpa [σpmf] using
    toKernelGamePMF_outcomeKernel_toPMFProfile_eq_toKernelGame g σ

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
  exact observedProgramOutcomeKernel_eq_toKernelGame_by_pmf
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
        simpa [observedProgramRunDist,
          GameTheory.FOSG.Kuhn.legalPureProfileRestrictReachable,
          toObservedProgramReachableLegalPureProfile] using
          GameTheory.FOSG.Kuhn.legalPureProfileRestrictReachable_extend_runDist
          (G := observedProgramFOSG g hctx)
          (toObservedProgramLegalPureProfile g hctx σ)
          (syntaxSteps g.prog)]
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
