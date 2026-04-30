import Vegas.FOSG.Observation

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}
namespace Observed

/-- Last element of a list, as an `Option`. Kept local to avoid depending on
which `List.getLast?` lemmas are imported. -/
def last? {α : Type} : List α → Option α
  | [] => none
  | [x] => some x
  | _ :: xs => last? xs

@[simp] theorem last?_append_singleton {α : Type} (xs : List α) (x : α) :
    last? (xs ++ [x]) = some x := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
      cases ys with
      | nil => rfl
      | cons z zs =>
          simpa [last?] using ih

/-- Observation events extracted from the final program-action FOSG information
state. -/
noncomputable def programObservationEvents
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    List (PrivateObs g who × PublicObs g hctx) :=
  s.filterMap
    (GameTheory.FOSG.PlayerEvent.observationPart
      (G := observedProgramFOSG g hctx) (i := who))

noncomputable def programLatestObservation?
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who) :
    Option (PrivateObs g who × PublicObs g hctx) :=
  last? (programObservationEvents g hctx who s)

@[simp] theorem programObservationEvents_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programObservationEvents g hctx who [] = [] := rfl

@[simp] theorem programLatestObservation?_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programLatestObservation? g hctx who [] = none := rfl

theorem programLatestObservation?_append_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who)
    (priv : PrivateObs g who) (pub : PublicObs g hctx) :
    programLatestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [programLatestObservation?, programObservationEvents]

theorem programLatestObservation?_append_act_obs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (s : (observedProgramFOSG g hctx).InfoState who)
    (a : ProgramAction g.prog who)
    (priv : PrivateObs g who) (pub : PublicObs g hctx) :
    programLatestObservation? g hctx who
      (s ++ [GameTheory.FOSG.PlayerEvent.act a,
        GameTheory.FOSG.PlayerEvent.obs priv pub]) = some (priv, pub) := by
  simp [programLatestObservation?, programObservationEvents]

/-- Extending a program-action FOSG history records the destination cursor
world's Vegas view/public state as the latest information-state observation. -/
theorem programLatestObservation?_history_snoc
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (a : (observedProgramFOSG g hctx).LegalAction h.lastState)
    (dst : CursorCheckedWorld g)
    (support : (observedProgramFOSG g hctx).transition h.lastState a dst ≠ 0) :
    programLatestObservation? g hctx who ((h.snoc a dst support).playerView who) =
      some (privateObsOfCursorWorld who dst, publicObsOfCursorWorld dst) := by
  rw [GameTheory.FOSG.History.playerView_snoc]
  let e : (observedProgramFOSG g hctx).Step :=
    { src := h.lastState, act := a, dst := dst, support := support }
  change programLatestObservation? g hctx who (h.playerView who ++ e.playerView who) =
    some (privateObsOfCursorWorld who dst, publicObsOfCursorWorld dst)
  cases hact : e.ownAction? who with
  | none =>
      rw [GameTheory.FOSG.Step.playerView_of_none e who hact]
      simpa [e, observedProgramFOSG] using
        programLatestObservation?_append_obs g hctx who (h.playerView who)
          (privateObsOfCursorWorld who dst) (publicObsOfCursorWorld dst)
  | some ai =>
      rw [GameTheory.FOSG.Step.playerView_of_some e who hact]
      simpa [e, observedProgramFOSG] using
        programLatestObservation?_append_act_obs g hctx who (h.playerView who) ai
          (privateObsOfCursorWorld who dst) (publicObsOfCursorWorld dst)

/-- Appending one concrete observed-program step records the destination cursor
world's observation as the latest player observation. -/
theorem programLatestObservation?_history_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    programLatestObservation? g hctx who ((h.appendStep e hsrc).playerView who) =
      some (privateObsOfCursorWorld who (h.appendStep e hsrc).lastState,
        publicObsOfCursorWorld (h.appendStep e hsrc).lastState) := by
  rw [GameTheory.FOSG.History.playerView]
  change programLatestObservation? g hctx who
      (GameTheory.FOSG.History.playerViewFrom (G := observedProgramFOSG g hctx)
        who (h.steps ++ [e])) =
    some (privateObsOfCursorWorld who (h.appendStep e hsrc).lastState,
      publicObsOfCursorWorld (h.appendStep e hsrc).lastState)
  rw [GameTheory.FOSG.History.playerViewFrom_append_singleton]
  simp only [GameTheory.FOSG.History.lastState_appendStep]
  cases hact : e.ownAction? who with
  | none =>
      rw [GameTheory.FOSG.Step.playerView_of_none e who hact]
      simpa [GameTheory.FOSG.History.playerView, observedProgramFOSG] using
        programLatestObservation?_append_obs g hctx who (h.playerView who)
          (privateObsOfCursorWorld who e.dst) (publicObsOfCursorWorld e.dst)
  | some ai =>
      rw [GameTheory.FOSG.Step.playerView_of_some e who hact]
      simpa [GameTheory.FOSG.History.playerView, observedProgramFOSG] using
        programLatestObservation?_append_act_obs g hctx who (h.playerView who) ai
          (privateObsOfCursorWorld who e.dst) (publicObsOfCursorWorld e.dst)

/-- The initial observed-program history has no latest program observation. -/
@[simp] theorem programLatestObservation?_history_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    programLatestObservation? g hctx who
        ((GameTheory.FOSG.History.nil (observedProgramFOSG g hctx)).playerView who) =
      none := by
  simp [programLatestObservation?, programObservationEvents, last?]

/-- Any nonempty observed-program history records the final cursor world's
private/public observation as the latest program observation for every player. -/
theorem programLatestObservation?_history_of_ne_nil
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (hne : h.steps ≠ []) :
    programLatestObservation? g hctx who (h.playerView who) =
      some (privateObsOfCursorWorld who h.lastState,
        publicObsOfCursorWorld h.lastState) := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      induction steps using List.reverseRecOn with
      | nil =>
          exact False.elim (hne rfl)
      | append_singleton steps e ih =>
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          rw [hEq]
          exact programLatestObservation?_history_appendStep
            g hctx who hprefix e hsrc

private structure CursorEmbedding (g : WFProgram P L) (who : P)
    {Γ : VCtx P L} (root : VegasCore P L Γ) where
  cursor : ProgramCursor root → ProgramCursor g.prog
  cursor_Γ : (c : ProgramCursor root) → (cursor c).Γ = c.Γ
  suffix : (c : ProgramCursor root) → ProgramSuffix g.prog c.prog
  commit : CommitCursor who root → CommitCursor who g.prog
  commit_ty : (c : CommitCursor who root) →
    CommitCursor.ty (commit c) = CommitCursor.ty c

private def CursorEmbedding.id (g : WFProgram P L) (who : P) :
    CursorEmbedding (P := P) (L := L) g who g.prog where
  cursor := fun c => c
  cursor_Γ := fun _ => rfl
  suffix := fun c => c.toSuffix
  commit := fun c => c
  commit_ty := fun _ => rfl

private def CursorEmbedding.letExpr
    {g : WFProgram P L} {who : P}
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (emb : CursorEmbedding (P := P) (L := L) g who (.letExpr x e k)) :
    CursorEmbedding (P := P) (L := L) g who k where
  cursor := fun c => emb.cursor (.letExpr c)
  cursor_Γ := fun c => by
    simpa [ProgramCursor.Γ] using emb.cursor_Γ (.letExpr c)
  suffix := fun c => emb.suffix (.letExpr c)
  commit := fun c => emb.commit (.letExpr c)
  commit_ty := fun c => by
    simpa [CommitCursor.ty] using emb.commit_ty (.letExpr c)

private def CursorEmbedding.sample
    {g : WFProgram P L} {who : P}
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (emb : CursorEmbedding (P := P) (L := L) g who (.sample x D k)) :
    CursorEmbedding (P := P) (L := L) g who k where
  cursor := fun c => emb.cursor (.sample c)
  cursor_Γ := fun c => by
    simpa [ProgramCursor.Γ] using emb.cursor_Γ (.sample c)
  suffix := fun c => emb.suffix (.sample c)
  commit := fun c => emb.commit (.sample c)
  commit_ty := fun c => by
    simpa [CommitCursor.ty] using emb.commit_ty (.sample c)

private def CursorEmbedding.commitFrame
    {g : WFProgram P L} {who owner : P}
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (emb : CursorEmbedding (P := P) (L := L) g who (.commit x owner R k)) :
    CursorEmbedding (P := P) (L := L) g who k where
  cursor := fun c => emb.cursor (.commit c)
  cursor_Γ := fun c => by
    simpa [ProgramCursor.Γ] using emb.cursor_Γ (.commit c)
  suffix := fun c => emb.suffix (.commit c)
  commit := fun c => emb.commit (.commit c)
  commit_ty := fun c => by
    simpa [CommitCursor.ty] using emb.commit_ty (.commit c)

private def CursorEmbedding.reveal
    {g : WFProgram P L} {who owner : P}
    {Γ : VCtx P L} {y x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden owner b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (emb : CursorEmbedding (P := P) (L := L) g who (.reveal y owner x hx k)) :
    CursorEmbedding (P := P) (L := L) g who k where
  cursor := fun c => emb.cursor (.reveal c)
  cursor_Γ := fun c => by
    simpa [ProgramCursor.Γ] using emb.cursor_Γ (.reveal c)
  suffix := fun c => emb.suffix (.reveal c)
  commit := fun c => emb.commit (.reveal c)
  commit_ty := fun c => by
    simpa [CommitCursor.ty] using emb.commit_ty (.reveal c)

private noncomputable def embeddedPrivateObs
    (g : WFProgram P L) (who : P)
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (emb : CursorEmbedding (P := P) (L := L) g who root)
    (c : ProgramCursor root) (env : VEnv L c.Γ) :
    PrivateObs g who :=
  let gc := emb.cursor c
  let hΓ := emb.cursor_Γ c
  privateObsOfCursorEnv who gc (hΓ.symm ▸ env)

private def embeddedPublicObs
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (emb : CursorEmbedding (P := P) (L := L) g who root)
    (c : ProgramCursor root) (env : VEnv L c.Γ) :
    PublicObs g hctx :=
  let gc := emb.cursor c
  let hΓ := emb.cursor_Γ c
  publicObsOfCursorEnv (hctx := hctx) gc (hΓ.symm ▸ env)

private noncomputable def embeddedOwnCommitEvents
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who owner : P)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (emb : CursorEmbedding (P := P) (L := L) g who (.commit x owner R k))
    (env : VEnv L ((x, .hidden owner b) :: Γ)) :
    (observedProgramFOSG g hctx).InfoState who :=
  if howner : owner = who then
    by
      subst owner
      let suffix : ProgramSuffix g.prog (.commit x who R k) :=
        emb.suffix ProgramCursor.here
      let action : ProgramAction g.prog who :=
        ProgramAction.commitAt suffix
          (env.get (VHasVar.here (Γ := Γ) (x := x)
            (τ := BindTy.hidden who b)))
      exact [GameTheory.FOSG.PlayerEvent.act action]
  else
    []

private noncomputable def cursorPlayerViewFrom
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    {Γ : VCtx P L} → {root : VegasCore P L Γ} →
    (emb : CursorEmbedding (P := P) (L := L) g who root) →
    (c : ProgramCursor root) → VEnv L c.Γ →
      (observedProgramFOSG g hctx).InfoState who
  | _, .ret _payoffs, _emb, .here, _env => []
  | _, .letExpr _x _e _k, _emb, .here, _env => []
  | _, .letExpr _x _e _k, emb, .letExpr c, env =>
      let env₀ := ProgramCursor.rootEnv c env
      [GameTheory.FOSG.PlayerEvent.obs
        (embeddedPrivateObs g who emb (.letExpr ProgramCursor.here) env₀)
        (embeddedPublicObs g hctx who emb (.letExpr ProgramCursor.here) env₀)] ++
      cursorPlayerViewFrom g hctx who (CursorEmbedding.letExpr emb) c env
  | _, .sample _x _D _k, _emb, .here, _env => []
  | _, .sample _x _D _k, emb, .sample c, env =>
      let env₀ := ProgramCursor.rootEnv c env
      [GameTheory.FOSG.PlayerEvent.obs
        (embeddedPrivateObs g who emb (.sample ProgramCursor.here) env₀)
        (embeddedPublicObs g hctx who emb (.sample ProgramCursor.here) env₀)] ++
      cursorPlayerViewFrom g hctx who (CursorEmbedding.sample emb) c env
  | _, .commit _x _owner _R _k, _emb, .here, _env => []
  | _, .commit x owner R k, emb, .commit c, env =>
      let env₀ := ProgramCursor.rootEnv c env
      let obs :=
        GameTheory.FOSG.PlayerEvent.obs
          (embeddedPrivateObs g who emb (.commit ProgramCursor.here) env₀)
          (embeddedPublicObs g hctx who emb (.commit ProgramCursor.here) env₀)
      let rest :=
        cursorPlayerViewFrom g hctx who
          (CursorEmbedding.commitFrame emb) c env
      embeddedOwnCommitEvents g hctx who owner emb env₀ ++ [obs] ++ rest
  | _, .reveal _y _owner _x _hx _k, _emb, .here, _env => []
  | _, .reveal _y _owner _x _hx _k, emb, .reveal c, env =>
      let env₀ := ProgramCursor.rootEnv c env
      [GameTheory.FOSG.PlayerEvent.obs
        (embeddedPrivateObs g who emb (.reveal ProgramCursor.here) env₀)
        (embeddedPublicObs g hctx who emb (.reveal ProgramCursor.here) env₀)] ++
      cursorPlayerViewFrom g hctx who (CursorEmbedding.reveal emb) c env
termination_by _ root _ _ _ => syntaxSteps root
decreasing_by
  all_goals simp_wf

private noncomputable def cursorPlayerView
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (c : ProgramCursor g.prog) (env : VEnv L c.Γ) :
    (observedProgramFOSG g hctx).InfoState who :=
  cursorPlayerViewFrom g hctx who (CursorEmbedding.id g who) c env

private theorem cursorPlayerView_initial
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    cursorPlayerView g hctx who
        (CursorCheckedWorld.initial g hctx).1.cursor
        (CursorCheckedWorld.initial g hctx).1.env = [] := by
  cases g with
  | mk Γ prog env wf normalized legal =>
      cases prog <;>
        simp [cursorPlayerView, cursorPlayerViewFrom,
          CursorCheckedWorld.initial, CursorEmbedding.id]

private theorem programCursor_root_wfctx :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
    (c : ProgramCursor root) → WFCtx c.Γ → WFCtx Γ₀
  | _, _, .here, hctx => hctx
  | _, .letExpr _ _ _, .letExpr c, hctx =>
      WFCtx.tail (programCursor_root_wfctx c hctx)
  | _, .sample _ _ _, .sample c, hctx =>
      WFCtx.tail (programCursor_root_wfctx c hctx)
  | _, .commit _ _ _ _, .commit c, hctx =>
      WFCtx.tail (programCursor_root_wfctx c hctx)
  | _, .reveal _ _ _ _ _, .reveal c, hctx =>
      WFCtx.tail (programCursor_root_wfctx c hctx)

private theorem programCursor_rootEnv_projectViewEnv_eq
    (who : P) :
    {Γ₀ : VCtx P L} → {root : VegasCore P L Γ₀} →
    (c : ProgramCursor root) →
    (env₁ env₂ : VEnv L c.Γ) →
    WFCtx c.Γ →
    projectViewEnv who (VEnv.eraseEnv env₁) =
      projectViewEnv who (VEnv.eraseEnv env₂) →
    projectViewEnv who (VEnv.eraseEnv (ProgramCursor.rootEnv c env₁)) =
      projectViewEnv who (VEnv.eraseEnv (ProgramCursor.rootEnv c env₂))
  | _, _, .here, _env₁, _env₂, _hctx, hview => hview
  | _, .letExpr _ _ _, .letExpr c, env₁, env₂, hctx, hview => by
      have hmid := programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hctx hview
      exact projectViewEnv_cons_eq (programCursor_root_wfctx c hctx) hmid
  | _, .sample _ _ _, .sample c, env₁, env₂, hctx, hview => by
      have hmid := programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hctx hview
      exact projectViewEnv_cons_eq (programCursor_root_wfctx c hctx) hmid
  | _, .commit _ _ _ _, .commit c, env₁, env₂, hctx, hview => by
      have hmid := programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hctx hview
      exact projectViewEnv_cons_eq (programCursor_root_wfctx c hctx) hmid
  | _, .reveal _ _ _ _ _, .reveal c, env₁, env₂, hctx, hview => by
      have hmid := programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hctx hview
      exact projectViewEnv_cons_eq (programCursor_root_wfctx c hctx) hmid

private theorem projectViewEnv_cast_eq
    (who : P) {Γ Δ : VCtx P L} (hΓ : Γ = Δ)
    (env₁ env₂ : VEnv L Γ)
    (hview :
      projectViewEnv who (VEnv.eraseEnv env₁) =
        projectViewEnv who (VEnv.eraseEnv env₂)) :
    projectViewEnv who (VEnv.eraseEnv (hΓ ▸ env₁)) =
      projectViewEnv who (VEnv.eraseEnv (hΓ ▸ env₂)) := by
  cases hΓ
  exact hview

private theorem embeddedPrivateObs_eq_of_projectViewEnv_eq
    (g : WFProgram P L) (who : P)
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (emb : CursorEmbedding (P := P) (L := L) g who root)
    (c : ProgramCursor root) (env₁ env₂ : VEnv L c.Γ)
    (hview :
      projectViewEnv who (VEnv.eraseEnv env₁) =
        projectViewEnv who (VEnv.eraseEnv env₂)) :
    embeddedPrivateObs g who emb c env₁ =
      embeddedPrivateObs g who emb c env₂ := by
  dsimp [embeddedPrivateObs, privateObsOfCursorEnv]
  ext
  · rfl
  · apply heq_of_eq
    exact projectViewEnv_cast_eq who (emb.cursor_Γ c).symm env₁ env₂ hview

private theorem embeddedOwnCommitEvents_eq_of_projectViewEnv_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who owner : P)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (emb : CursorEmbedding (P := P) (L := L) g who (.commit x owner R k))
    (env₁ env₂ : VEnv L ((x, .hidden owner b) :: Γ))
    (hnodup : (((x, .hidden owner b) :: Γ).map Prod.fst).Nodup)
    (hview :
      projectViewEnv who (VEnv.eraseEnv env₁) =
        projectViewEnv who (VEnv.eraseEnv env₂)) :
    embeddedOwnCommitEvents g hctx who owner emb env₁ =
      embeddedOwnCommitEvents g hctx who owner emb env₂ := by
  by_cases howner : owner = who
  · subst owner
    have hhead :
        env₁.get (VHasVar.here (Γ := Γ) (x := x)
          (τ := BindTy.hidden who b)) =
          env₂.get (VHasVar.here (Γ := Γ) (x := x)
            (τ := BindTy.hidden who b)) := by
      exact projectViewEnv_cons_head_eq hnodup (by simp [canSee]) hview
    simp [embeddedOwnCommitEvents, hhead]
  · simp [embeddedOwnCommitEvents, howner]

private theorem cursorPlayerViewFrom_here
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (emb : CursorEmbedding (P := P) (L := L) g who root)
    (env : VEnv L ProgramCursor.here.Γ) :
    cursorPlayerViewFrom g hctx who emb ProgramCursor.here env = [] := by
  cases root <;> simp [cursorPlayerViewFrom]

private theorem cursorPlayerViewFrom_eq_of_projectViewEnv_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    {Γ : VCtx P L} → {root : VegasCore P L Γ} →
    (emb : CursorEmbedding (P := P) (L := L) g who root) →
    (c : ProgramCursor root) →
    (env₁ env₂ : VEnv L c.Γ) →
    WFCtx c.Γ →
    projectViewEnv who (VEnv.eraseEnv env₁) =
      projectViewEnv who (VEnv.eraseEnv env₂) →
    cursorPlayerViewFrom g hctx who emb c env₁ =
      cursorPlayerViewFrom g hctx who emb c env₂
  | _, .ret _payoffs, _emb, .here, _env₁, _env₂, _hcur, _hview => by
      simp [cursorPlayerViewFrom]
  | _, .letExpr _x _e _k, _emb, .here, _env₁, _env₂, _hcur, _hview => by
      simp [cursorPlayerViewFrom]
  | _, .letExpr _x _e _k, emb, .letExpr c, env₁, env₂, hcur, hview => by
      let env₁₀ := ProgramCursor.rootEnv c env₁
      let env₂₀ := ProgramCursor.rootEnv c env₂
      have hroot :
          projectViewEnv who (VEnv.eraseEnv env₁₀) =
            projectViewEnv who (VEnv.eraseEnv env₂₀) :=
        programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hcur hview
      have hpriv := embeddedPrivateObs_eq_of_projectViewEnv_eq
        g who emb (.letExpr ProgramCursor.here) env₁₀ env₂₀ hroot
      have hrec := cursorPlayerViewFrom_eq_of_projectViewEnv_eq
        g hctx who (CursorEmbedding.letExpr emb) c env₁ env₂ hcur hview
      simpa [cursorPlayerViewFrom, env₁₀, env₂₀, hpriv, embeddedPublicObs]
        using hrec
  | _, .sample _x _D _k, _emb, .here, _env₁, _env₂, _hcur, _hview => by
      simp [cursorPlayerViewFrom]
  | _, .sample _x _D _k, emb, .sample c, env₁, env₂, hcur, hview => by
      let env₁₀ := ProgramCursor.rootEnv c env₁
      let env₂₀ := ProgramCursor.rootEnv c env₂
      have hroot :
          projectViewEnv who (VEnv.eraseEnv env₁₀) =
            projectViewEnv who (VEnv.eraseEnv env₂₀) :=
        programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hcur hview
      have hpriv := embeddedPrivateObs_eq_of_projectViewEnv_eq
        g who emb (.sample ProgramCursor.here) env₁₀ env₂₀ hroot
      have hrec := cursorPlayerViewFrom_eq_of_projectViewEnv_eq
        g hctx who (CursorEmbedding.sample emb) c env₁ env₂ hcur hview
      simpa [cursorPlayerViewFrom, env₁₀, env₂₀, hpriv, embeddedPublicObs]
        using hrec
  | _, .commit _x _owner _R _k, _emb, .here, _env₁, _env₂, _hcur, _hview => by
      simp [cursorPlayerViewFrom]
  | _, .commit x owner R k, emb, .commit c, env₁, env₂, hcur, hview => by
      let env₁₀ := ProgramCursor.rootEnv c env₁
      let env₂₀ := ProgramCursor.rootEnv c env₂
      have hroot :
          projectViewEnv who (VEnv.eraseEnv env₁₀) =
            projectViewEnv who (VEnv.eraseEnv env₂₀) :=
        programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hcur hview
      have hpriv := embeddedPrivateObs_eq_of_projectViewEnv_eq
        g who emb (.commit ProgramCursor.here) env₁₀ env₂₀ hroot
      have hown := embeddedOwnCommitEvents_eq_of_projectViewEnv_eq
        g hctx who owner emb env₁₀ env₂₀
        (programCursor_root_wfctx c hcur) hroot
      have hrec := cursorPlayerViewFrom_eq_of_projectViewEnv_eq
        g hctx who (CursorEmbedding.commitFrame emb) c env₁ env₂ hcur hview
      simpa [cursorPlayerViewFrom, env₁₀, env₂₀, hpriv, embeddedPublicObs, hown]
        using hrec
  | _, .reveal _y _owner _x _hx _k, _emb, .here, _env₁, _env₂, _hcur, _hview => by
      simp [cursorPlayerViewFrom]
  | _, .reveal _y _owner _x _hx _k, emb, .reveal c, env₁, env₂, hcur, hview => by
      let env₁₀ := ProgramCursor.rootEnv c env₁
      let env₂₀ := ProgramCursor.rootEnv c env₂
      have hroot :
          projectViewEnv who (VEnv.eraseEnv env₁₀) =
            projectViewEnv who (VEnv.eraseEnv env₂₀) :=
        programCursor_rootEnv_projectViewEnv_eq who c env₁ env₂ hcur hview
      have hpriv := embeddedPrivateObs_eq_of_projectViewEnv_eq
        g who emb (.reveal ProgramCursor.here) env₁₀ env₂₀ hroot
      have hrec := cursorPlayerViewFrom_eq_of_projectViewEnv_eq
        g hctx who (CursorEmbedding.reveal emb) c env₁ env₂ hcur hview
      simpa [cursorPlayerViewFrom, env₁₀, env₂₀, hpriv, embeddedPublicObs]
        using hrec
termination_by _ root _ _ _ _ _ => syntaxSteps root
decreasing_by
  all_goals simp_wf

private theorem cursorPlayerView_eq_of_projectViewEnv_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (c : ProgramCursor g.prog) (env₁ env₂ : VEnv L c.Γ)
    (hcur : WFCtx c.Γ)
    (hview :
      projectViewEnv who (VEnv.eraseEnv env₁) =
        projectViewEnv who (VEnv.eraseEnv env₂)) :
    cursorPlayerView g hctx who c env₁ =
      cursorPlayerView g hctx who c env₂ :=
  cursorPlayerViewFrom_eq_of_projectViewEnv_eq
    g hctx who (CursorEmbedding.id g who) c env₁ env₂ hcur hview

private theorem cursorPlayerView_eq_of_privateObs_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (w₁ w₂ : CursorCheckedWorld g)
    (hpriv :
      privateObsOfCursorWorld who w₁ =
        privateObsOfCursorWorld who w₂) :
    cursorPlayerView g hctx who w₁.1.cursor w₁.1.env =
      cursorPlayerView g hctx who w₂.1.cursor w₂.1.env := by
  rcases w₁ with ⟨⟨c₁, env₁⟩, valid₁⟩
  rcases w₂ with ⟨⟨c₂, env₂⟩, valid₂⟩
  dsimp [privateObsOfCursorWorld] at hpriv ⊢
  injection hpriv with hcursor henv
  cases hcursor
  have hview :
      projectViewEnv who (VEnv.eraseEnv env₁) =
        projectViewEnv who (VEnv.eraseEnv env₂) := eq_of_heq henv
  exact cursorPlayerView_eq_of_projectViewEnv_eq
    g hctx who c₁ env₁ env₂ valid₁.1 hview

private noncomputable def cursorStepPlayerViewFrom
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    {Γ : VCtx P L} {root : VegasCore P L Γ}
    (emb : CursorEmbedding (P := P) (L := L) g who root)
    (pa : ProgramJointAction g)
    (dstC : ProgramCursor root) (dstEnv : VEnv L dstC.Γ) :
    (observedProgramFOSG g hctx).InfoState who :=
  match pa who with
  | some ai =>
      [GameTheory.FOSG.PlayerEvent.act ai,
        GameTheory.FOSG.PlayerEvent.obs
          (embeddedPrivateObs g who emb dstC dstEnv)
          (embeddedPublicObs g hctx who emb dstC dstEnv)]
  | none =>
      [GameTheory.FOSG.PlayerEvent.obs
        (embeddedPrivateObs g who emb dstC dstEnv)
        (embeddedPublicObs g hctx who emb dstC dstEnv)]

private theorem cursorPlayerViewFrom_transition
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P) :
    {Γ : VCtx P L} → {root : VegasCore P L Γ} →
    (emb : CursorEmbedding (P := P) (L := L) g who root) →
    (c : ProgramCursor root) →
    (env : VEnv L c.Γ) →
    (valid : c.EndpointValid) →
    (pa : ProgramJointAction g) →
    (ha : JointActionLegal
      ({ Γ := c.Γ, prog := c.prog, env := env } : World P L)
      (ProgramJointAction.toAction pa)) →
    (hmoves : ∀ i,
      pa i ∈ CursorCheckedWorld.availableProgramMovesAt
        c.prog env (emb.suffix c) i) →
    (dst : CursorRuntimeState root) →
    cursorTransitionState c env valid
      (ProgramJointAction.toAction pa) ha dst ≠ 0 →
      cursorPlayerViewFrom g hctx who emb dst.cursor dst.env =
        cursorPlayerViewFrom g hctx who emb c env ++
          cursorStepPlayerViewFrom g hctx who emb pa dst.cursor dst.env
  | _, .ret _payoffs, emb, .here, env, valid, pa, ha, hmoves, dst, hsupp =>
      False.elim (ha.1 (by simp [ProgramCursor.prog, terminal]))
  | _, .letExpr x e k, emb, .here, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.pure_apply, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at hsupp
      subst dst
      have hnone : pa who = none := by
        specialize hmoves who
        cases hpa : pa who with
        | none => rfl
        | some ai =>
            simp only [hpa, CursorCheckedWorld.availableProgramMovesAt, active,
              ProgramCursor.prog, Set.mem_setOf_eq, Finset.notMem_empty,
              false_and] at hmoves
      simp [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        ProgramCursor.rootEnv, hnone, cursorPlayerViewFrom_here]
  | _, .sample x D k, emb, .here, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.map_apply, ne_eq, ENNReal.tsum_eq_zero,
        ite_eq_right_iff, not_forall] at hsupp
      rcases hsupp with ⟨v, hdst, _hv⟩
      subst dst
      have hnone : pa who = none := by
        specialize hmoves who
        cases hpa : pa who with
        | none => rfl
        | some ai =>
            simp only [hpa, CursorCheckedWorld.availableProgramMovesAt, active,
              ProgramCursor.prog, Set.mem_setOf_eq, Finset.notMem_empty,
              false_and] at hmoves
      simp [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        ProgramCursor.rootEnv, hnone, cursorPlayerViewFrom_here]
  | _, .commit x owner R k, emb, .here, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.pure_apply, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at hsupp
      subst dst
      by_cases howner : owner = who
      · subst owner
        have hsome : ∃ ai, pa who = some ai := by
          specialize hmoves who
          cases hpa : pa who with
          | none =>
              simp only [hpa, CursorCheckedWorld.availableProgramMovesAt, active,
                ProgramCursor.prog, Set.mem_setOf_eq, Finset.mem_singleton,
                not_true_eq_false] at hmoves
          | some ai => exact ⟨ai, rfl⟩
        rcases hsome with ⟨ai, hai⟩
        have haiAvail : ai ∈
            CursorCheckedWorld.availableProgramActionsAt
              (.commit x who R k) env (emb.suffix ProgramCursor.here) who := by
          have hm := hmoves who
          rw [hai] at hm
          simpa [CursorCheckedWorld.availableProgramMovesAt, active,
            ProgramCursor.prog] using hm.2
        let v := commitValueOfLegal (L := L) ha
        let aj : ProgramAction g.prog who :=
          ProgramAction.commitAt (emb.suffix ProgramCursor.here) v
        have hajAvail : aj ∈
            CursorCheckedWorld.availableProgramActionsAt
              (.commit x who R k) env (emb.suffix ProgramCursor.here) who := by
          rw [CursorCheckedWorld.availableProgramActionsAt_commit_owner_iff]
          exact ⟨v, rfl, commitValueOfLegal_guard (L := L) ha⟩
        have hact_ai :
            ProgramAction.toAction ai = Sigma.mk _ v := by
          have h := commitValueOfLegal_action (L := L) ha
          simpa [ProgramJointAction.toAction, hai, v] using h
        have hact_aj :
            ProgramAction.toAction aj = Sigma.mk _ v := by
          dsimp [aj]
          simp [ProgramAction.toAction, ProgramAction.commitAt,
            ProgramSuffix.ty_commitCursor]
        have hact : ProgramAction.toAction ai = ProgramAction.toAction aj := by
          rw [hact_ai, hact_aj]
        have haiEq : ai = aj :=
          CursorCheckedWorld.availableProgramActionsAt_eq_of_toAction_eq
            haiAvail hajAvail hact
        subst ai
        simp [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
          embeddedOwnCommitEvents, ProgramCursor.rootEnv, hai, aj, v,
          cursorPlayerViewFrom_here]
        rfl
      · have hnone : pa who = none := by
          specialize hmoves who
          cases hpa : pa who with
          | none => rfl
          | some ai =>
              simp only [hpa, CursorCheckedWorld.availableProgramMovesAt, active,
                ProgramCursor.prog, Set.mem_setOf_eq, Finset.mem_singleton] at hmoves
              exact False.elim (howner hmoves.1.symm)
        simp [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
          embeddedOwnCommitEvents, ProgramCursor.rootEnv, hnone, howner,
          cursorPlayerViewFrom_here]
  | _, .reveal (b := b) y owner x hx k, emb, .here, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.pure_apply, ne_eq, ite_eq_right_iff,
        one_ne_zero, imp_false, not_not] at hsupp
      subst dst
      have hnone : pa who = none := by
        specialize hmoves who
        cases hpa : pa who with
        | none => rfl
        | some ai =>
            simp only [hpa, CursorCheckedWorld.availableProgramMovesAt, active,
              ProgramCursor.prog, Set.mem_setOf_eq, Finset.notMem_empty,
              false_and] at hmoves
      simp [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        ProgramCursor.rootEnv, hnone, cursorPlayerViewFrom_here]
  | _, .letExpr x e k, emb, .letExpr c, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.map_apply, ne_eq, ENNReal.tsum_eq_zero,
        ite_eq_right_iff, not_forall] at hsupp
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      subst dst
      have hrec := cursorPlayerViewFrom_transition g hctx who
        (CursorEmbedding.letExpr emb) c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        pa
        (by simpa [ProgramCursor.EndpointValid] using ha)
        (by
          intro i
          simpa [CursorCheckedWorld.availableProgramMovesAt, ProgramCursor.prog,
            active, CursorEmbedding.letExpr] using hmoves i)
        s hsuppS
      have hroot := cursorTransitionState_rootEnv_eq c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        (ProgramJointAction.toAction pa)
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      simpa [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        hroot, List.append_assoc]
        using hrec
  | _, .sample x D k, emb, .sample c, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.map_apply, ne_eq, ENNReal.tsum_eq_zero,
        ite_eq_right_iff, not_forall] at hsupp
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      subst dst
      have hrec := cursorPlayerViewFrom_transition g hctx who
        (CursorEmbedding.sample emb) c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        pa
        (by simpa [ProgramCursor.EndpointValid] using ha)
        (by
          intro i
          simpa [CursorCheckedWorld.availableProgramMovesAt, ProgramCursor.prog,
            active, CursorEmbedding.sample] using hmoves i)
        s hsuppS
      have hroot := cursorTransitionState_rootEnv_eq c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        (ProgramJointAction.toAction pa)
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      simpa [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        hroot, List.append_assoc]
        using hrec
  | _, .commit x owner R k, emb, .commit c, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.map_apply, ne_eq, ENNReal.tsum_eq_zero,
        ite_eq_right_iff, not_forall] at hsupp
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      subst dst
      have hrec := cursorPlayerViewFrom_transition g hctx who
        (CursorEmbedding.commitFrame emb) c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        pa
        (by simpa [ProgramCursor.EndpointValid] using ha)
        (by
          intro i
          simpa [CursorCheckedWorld.availableProgramMovesAt, ProgramCursor.prog,
            active, CursorEmbedding.commitFrame] using hmoves i)
        s hsuppS
      have hroot := cursorTransitionState_rootEnv_eq c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        (ProgramJointAction.toAction pa)
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      simpa [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        hroot, List.append_assoc]
        using hrec
  | _, .reveal y owner x hx k, emb, .reveal c, env, valid, pa, ha, hmoves, dst, hsupp => by
      simp only [cursorTransitionState, PMF.map_apply, ne_eq, ENNReal.tsum_eq_zero,
        ite_eq_right_iff, not_forall] at hsupp
      rcases hsupp with ⟨s, hdst, hsuppS⟩
      subst dst
      have hrec := cursorPlayerViewFrom_transition g hctx who
        (CursorEmbedding.reveal emb) c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        pa
        (by simpa [ProgramCursor.EndpointValid] using ha)
        (by
          intro i
          simpa [CursorCheckedWorld.availableProgramMovesAt, ProgramCursor.prog,
            active, CursorEmbedding.reveal] using hmoves i)
        s hsuppS
      have hroot := cursorTransitionState_rootEnv_eq c env
        (by simpa [ProgramCursor.EndpointValid] using valid)
        (ProgramJointAction.toAction pa)
        (by simpa [ProgramCursor.EndpointValid] using ha) s hsuppS
      simpa [cursorPlayerViewFrom, cursorStepPlayerViewFrom,
        hroot, List.append_assoc]
        using hrec

private theorem cursorLegal_mem_availableProgramMovesAt
    {g : WFProgram P L} (w : CursorCheckedWorld g)
    (a : ProgramJointAction g) (ha : CursorProgramJointActionLegal w a)
    (i : P) :
    a i ∈ CursorCheckedWorld.availableProgramMovesAt
      w.1.cursor.prog w.1.env w.1.cursor.toSuffix i := by
  cases w with
  | mk d valid =>
      cases d with
      | mk c env =>
          cases h : a i with
          | none =>
              simpa [CursorProgramJointActionLegal,
                CursorCheckedWorld.availableProgramMovesAt,
                CursorCheckedWorld.availableProgramActions,
                CursorCheckedWorld.active, CursorWorldData.prog,
                CursorWorldData.suffix, h] using ha.2 i
          | some ai =>
              simpa [CursorProgramJointActionLegal,
                CursorCheckedWorld.availableProgramMovesAt,
                CursorCheckedWorld.availableProgramActions,
                CursorCheckedWorld.active, CursorWorldData.prog,
                CursorWorldData.suffix, h] using ha.2 i

private theorem cursorPlayerView_step
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (src dst : CursorCheckedWorld g)
    (a : (observedProgramFOSG g hctx).LegalAction src)
    (hsupp : (observedProgramFOSG g hctx).transition src a dst ≠ 0) :
    cursorPlayerView g hctx who dst.1.cursor dst.1.env =
      cursorPlayerView g hctx who src.1.cursor src.1.env ++
        (GameTheory.FOSG.Step.playerView
          ({ src := src, act := a, dst := dst, support := hsupp } :
            (observedProgramFOSG g hctx).Step) who) := by
  have hmem :
      dst ∈ (cursorProgramTransition src a).support := by
    simpa [observedProgramFOSG, PMF.mem_support_iff] using hsupp
  rw [cursorProgramTransition] at hmem
  rcases (PMF.mem_support_map_iff _ _ _).mp hmem with ⟨s, hs, hdst⟩
  subst hdst
  have hsuppS :
      cursorTransitionState src.1.cursor src.1.env
        (by
          simpa [CursorWorldData.Valid, CursorWorldData.prog,
            ProgramCursor.EndpointValid] using src.2)
        (ProgramJointAction.toAction a.1)
        (CursorProgramJointActionLegal.toAction a.2) s ≠ 0 := by
    simpa [PMF.mem_support_iff] using hs
  have hmoves : ∀ i,
      a.1 i ∈ CursorCheckedWorld.availableProgramMovesAt
        src.1.cursor.prog src.1.env
        ((CursorEmbedding.id g who).suffix src.1.cursor) i := by
    intro i
    simpa [CursorEmbedding.id] using
      cursorLegal_mem_availableProgramMovesAt (g := g) src a.1 a.2 i
  have hbase := cursorPlayerViewFrom_transition g hctx who
    (CursorEmbedding.id g who) src.1.cursor src.1.env
    (by
      simpa [CursorWorldData.Valid, CursorWorldData.prog,
        ProgramCursor.EndpointValid] using src.2)
    a.1
    (CursorProgramJointActionLegal.toAction a.2)
    hmoves
    s
    hsuppS
  have hstep :
      cursorStepPlayerViewFrom g hctx who (CursorEmbedding.id g who)
          a.1 s.cursor s.env =
        (GameTheory.FOSG.Step.playerView
          ({ src := src, act := a, dst := CursorRuntimeState.toChecked s,
             support := hsupp } :
            (observedProgramFOSG g hctx).Step) who) := by
    cases hact : a.1 who with
    | none =>
        simp [cursorStepPlayerViewFrom, GameTheory.FOSG.Step.playerView,
          GameTheory.FOSG.Step.ownAction?, GameTheory.FOSG.Step.privateObs,
          GameTheory.FOSG.Step.publicObs, observedProgramFOSG,
          CursorRuntimeState.toChecked, embeddedPrivateObs, embeddedPublicObs,
          CursorEmbedding.id, privateObsOfCursorEnv, privateObsOfCursorWorld,
          publicObsOfCursorEnv, publicObsOfCursorWorld, hact]
    | some ai =>
        simp [cursorStepPlayerViewFrom, GameTheory.FOSG.Step.playerView,
          GameTheory.FOSG.Step.ownAction?, GameTheory.FOSG.Step.privateObs,
          GameTheory.FOSG.Step.publicObs, observedProgramFOSG,
          CursorRuntimeState.toChecked, embeddedPrivateObs, embeddedPublicObs,
          CursorEmbedding.id, privateObsOfCursorEnv, privateObsOfCursorWorld,
          publicObsOfCursorEnv, publicObsOfCursorWorld, hact]
  unfold cursorPlayerView
  simp only [CursorRuntimeState.toChecked]
  rw [hbase, hstep]
  simp [GameTheory.FOSG.Step.playerView, GameTheory.FOSG.Step.ownAction?,
    GameTheory.FOSG.Step.privateObs, GameTheory.FOSG.Step.publicObs,
    observedProgramFOSG, CursorRuntimeState.toChecked]

private theorem cursorPlayerView_appendStep
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History)
    (e : (observedProgramFOSG g hctx).Step)
    (hsrc : e.src = h.lastState) :
    cursorPlayerView g hctx who
        (h.appendStep e hsrc).lastState.1.cursor
        (h.appendStep e hsrc).lastState.1.env =
      cursorPlayerView g hctx who h.lastState.1.cursor h.lastState.1.env ++
        e.playerView who := by
  cases e with
  | mk src act dst support =>
      dsimp at hsrc ⊢
      subst src
      rw [GameTheory.FOSG.History.lastState_appendStep]
      change cursorPlayerView g hctx who dst.1.cursor dst.1.env =
        cursorPlayerView g hctx who h.lastState.1.cursor h.lastState.1.env ++
          (({ src := h.lastState, act := act, dst := dst, support := support } :
              (observedProgramFOSG g hctx).Step).playerView who)
      exact cursorPlayerView_step g hctx who h.lastState dst act support

private theorem playerView_eq_cursorPlayerView
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h : (observedProgramFOSG g hctx).History) :
    h.playerView who =
      cursorPlayerView g hctx who h.lastState.1.cursor h.lastState.1.env := by
  let G := observedProgramFOSG g hctx
  cases h with
  | mk steps chain =>
      revert chain
      induction steps using List.reverseRecOn with
      | nil =>
          intro chain
          simpa [GameTheory.FOSG.History.playerView,
            GameTheory.FOSG.History.playerViewFrom,
            GameTheory.FOSG.History.lastState,
            GameTheory.FOSG.lastStateFrom] using
            (cursorPlayerView_initial g hctx who).symm
      | append_singleton steps e ih =>
          intro chain
          let hprefix : G.History :=
            { steps := steps
              chain := GameTheory.FOSG.StepChainFrom.left
                (G := G) (es₁ := steps) (es₂ := [e]) chain }
          have hright :
              G.StepChainFrom (G.lastStateFrom G.init steps) [e] :=
            GameTheory.FOSG.StepChainFrom.right
              (G := G) (es₁ := steps) (es₂ := [e]) chain
          have hsrc : e.src = hprefix.lastState := by
            simpa [hprefix, GameTheory.FOSG.History.lastState,
              GameTheory.FOSG.StepChainFrom] using hright.1
          let hfull : G.History := hprefix.appendStep e hsrc
          have hEq : ({ steps := steps ++ [e], chain := chain } : G.History) = hfull := by
            ext
            rfl
          have ihprefix :
              hprefix.playerView who =
                cursorPlayerView g hctx who
                  hprefix.lastState.1.cursor hprefix.lastState.1.env :=
            ih hprefix.chain
          have hcur := cursorPlayerView_appendStep g hctx who hprefix e hsrc
          rw [hEq]
          change hfull.playerView who =
            cursorPlayerView g hctx who
              hfull.lastState.1.cursor hfull.lastState.1.env
          rw [hcur]
          simp only [hfull, GameTheory.FOSG.History.playerView,
            GameTheory.FOSG.History.appendStep]
          rw [GameTheory.FOSG.History.playerViewFrom_append_singleton]
          change hprefix.playerView who ++ e.playerView who =
            cursorPlayerView g hctx who
              hprefix.lastState.1.cursor hprefix.lastState.1.env ++
              e.playerView who
          rw [ihprefix]

/--
History-collapse target for transporting FOSG behavioral strategies back to
syntax-recursive Vegas behavioral strategies.

`privateObsOfCursorWorld who w` is exactly the current program cursor together
with `who`'s current `ViewEnv` at that cursor.  The intended SSA/view-history
invariant is that, on reachable observed-program histories, this current
private observation already determines the player's full FOSG information
state.  Equivalently, two histories that end at the same Vegas program point
with the same current player view are indistinguishable as FOSG histories for
that player.

This is the missing "history collapse" lemma needed to define a
`LegalProgramBehavioralProfilePMF g` from a sequential FOSG behavioral profile:
the sequential profile is indexed by `h.playerView who`, while the Vegas
profile is indexed by the current commit-site cursor and `ViewEnv`.
-/
theorem playerView_eq_of_privateObsOfLastState_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (h h' : (observedProgramFOSG g hctx).History)
    (hobs :
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCursorWorld who h'.lastState) :
    h.playerView who = h'.playerView who := by
  calc
    h.playerView who =
        cursorPlayerView g hctx who h.lastState.1.cursor h.lastState.1.env :=
      playerView_eq_cursorPlayerView g hctx who h
    _ = cursorPlayerView g hctx who h'.lastState.1.cursor h'.lastState.1.env :=
      cursorPlayerView_eq_of_privateObs_eq g hctx who h.lastState h'.lastState hobs
    _ = h'.playerView who :=
      (playerView_eq_cursorPlayerView g hctx who h').symm

/-- A total FOSG behavioral profile is constant on histories with the same
current Vegas private observation.

This is the representative-independence fact needed when a sequential
information-state strategy is read back as a syntax-recursive Vegas strategy:
once the current cursor and player view agree, the history-collapse
lemma identifies the FOSG information states, so the profile lookup is the
same. -/
theorem legalBehavioralProfile_apply_eq_of_privateObsOfLastState_eq
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (who : P)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (h h' : (observedProgramFOSG g hctx).History)
    (hobs :
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCursorWorld who h'.lastState) :
    (β.toProfile who) (h.playerView who) =
      (β.toProfile who) (h'.playerView who) := by
  rw [playerView_eq_of_privateObsOfLastState_eq g hctx who h h' hobs]

theorem observedProgramFOSG_legalObservable
    (g : WFProgram P L) (hctx : WFCtx g.Γ) :
    (observedProgramFOSG g hctx).LegalObservable := by
  intro who h h' hInfo
  by_cases hnil : h.steps = []
  · have h_eq_nil :
        h = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) :=
      GameTheory.FOSG.History.ext hnil
    subst h_eq_nil
    by_cases hnil' : h'.steps = []
    · have h'_eq_nil :
          h' = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) :=
        GameTheory.FOSG.History.ext hnil'
      subst h'_eq_nil
      rfl
    · have hlatest :=
        congrArg (programLatestObservation? g hctx who) hInfo
      rw [programLatestObservation?_history_nil,
        programLatestObservation?_history_of_ne_nil g hctx who h' hnil'] at hlatest
      cases hlatest
  · by_cases hnil' : h'.steps = []
    · have h'_eq_nil :
          h' = GameTheory.FOSG.History.nil (observedProgramFOSG g hctx) :=
        GameTheory.FOSG.History.ext hnil'
      subst h'_eq_nil
      have hlatest :=
        congrArg (programLatestObservation? g hctx who) hInfo
      rw [programLatestObservation?_history_of_ne_nil g hctx who h hnil,
        programLatestObservation?_history_nil] at hlatest
      cases hlatest
    · have hlatest :=
        congrArg (programLatestObservation? g hctx who) hInfo
      rw [programLatestObservation?_history_of_ne_nil g hctx who h hnil,
        programLatestObservation?_history_of_ne_nil g hctx who h' hnil'] at hlatest
      injection hlatest with hobs
      have hpriv :
          privateObsOfCursorWorld who h.lastState =
            privateObsOfCursorWorld who h'.lastState :=
        congrArg Prod.fst hobs
      simpa [GameTheory.FOSG.availableMoves] using
        observedProgram_availableMovesAtState_eq_of_privateObs_eq
          g hctx who h.lastState h'.lastState hpriv

end Observed

end FOSGBridge
end Vegas
