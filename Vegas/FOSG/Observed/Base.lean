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
  commit : CommitCursor who root → CommitCursor who g.prog
  commit_ty : (c : CommitCursor who root) →
    CommitCursor.ty (commit c) = CommitCursor.ty c

private def CursorEmbedding.id (g : WFProgram P L) (who : P) :
    CursorEmbedding (P := P) (L := L) g who g.prog where
  cursor := fun c => c
  cursor_Γ := fun _ => rfl
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
      let localCursor : CommitCursor who (.commit x who R k) := .here
      let action : ProgramAction g.prog who :=
        { cursor := emb.commit localCursor
          value :=
            cast (congrArg L.Val (emb.commit_ty localCursor)).symm
              (env.get (VHasVar.here (Γ := Γ) (x := x)
                (τ := BindTy.hidden who b))) }
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
  sorry

/-- A total FOSG behavioral profile is constant on histories with the same
current Vegas private observation.

This is the representative-independence fact needed when a sequential
information-state strategy is read back as a syntax-recursive Vegas strategy:
once the current cursor and player view agree, the sorry'd history-collapse
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
