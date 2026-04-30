import Vegas.FOSG.Observed.Kernel

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed

/-!
# Collapsing sequential FOSG strategies to Vegas behavioral strategies

The definitions in this file implement the top-down direction of the native
Vegas Kuhn proof: given a total legal behavioral profile for the sequential
FOSG denotation, read it back as a syntax-recursive Vegas PMF behavioral
profile.  The only semantic fact used to make representative choice coherent is
`playerView_eq_of_privateObsOfLastState_eq`.
-/

namespace VEnv

/-- Reattach visibility tags to an erased environment. This is the inverse
direction needed only for proofs that compare FOSG cursor worlds against the
syntax-recursive Vegas strategy key. -/
noncomputable def ofErased
    {Γ : VCtx P L} (ρ : Env L.Val (eraseVCtx Γ)) : VEnv (Player := P) L Γ :=
  fun x τ hx => ρ x τ.base hx.toErased

omit [DecidableEq P] in
theorem eraseEnv_ofErased
    {Γ : VCtx P L} (hctx : WFCtx (L := L) Γ)
    (ρ : Env L.Val (eraseVCtx Γ)) :
    VEnv.eraseEnv (ofErased (P := P) (L := L) (Γ := Γ) ρ) = ρ := by
  induction Γ with
  | nil =>
      funext x τ hx
      nomatch hx
  | cons hd tl ih =>
      obtain ⟨y, σ⟩ := hd
      funext x τ hx
      cases hx with
      | here => rfl
      | there hx' =>
          have hctx_tail : WFCtx (L := L) tl := (List.nodup_cons.mp hctx).2
          have ih' := ih hctx_tail (fun x τ h => ρ x τ (.there h))
          exact congrFun (congrFun (congrFun ih' x) τ) hx'

theorem projectViewEnv_eraseEnv_ofErased
    {Γ : VCtx P L} (hctx : WFCtx (L := L) Γ)
    (who : P) (ρ : Env L.Val (eraseVCtx Γ)) :
    projectViewEnv who
        (VEnv.eraseEnv (ofErased (P := P) (L := L) (Γ := Γ) ρ)) =
      projectViewEnv who ρ := by
  rw [eraseEnv_ofErased (P := P) (L := L) hctx ρ]

end VEnv

theorem projectViewEnv_eraseEnv_cast_heq
    {Γc Γ : VCtx P L} (who : P) (hΓ : Γc = Γ)
    (env : VEnv L Γc) :
    HEq (projectViewEnv who (VEnv.eraseEnv (hΓ ▸ env)))
      (projectViewEnv who (VEnv.eraseEnv env)) := by
  cases hΓ
  rfl

private noncomputable def castBehavioralStrategyPMF
    {who : P} {Γ₁ Γ₂ : VCtx P L}
    {p₁ : VegasCore P L Γ₁} {p₂ : VegasCore P L Γ₂}
    (hΓ : Γ₁ = Γ₂) (hp : hΓ ▸ p₁ = p₂)
    (σ : ProgramBehavioralStrategyPMF who p₁) :
    ProgramBehavioralStrategyPMF who p₂ := by
  cases hΓ
  cases hp
  exact σ

/-- Decode a program-local optional FOSG move into the value chosen at a
particular Vegas commit type, using `default` on impossible branches.

Legality of the FOSG profile at an owned commit site later proves that the
impossible branches have zero mass. -/
noncomputable def valueOfProgramMoveOr
    {g : WFProgram P L} {who : P} {b : L.Ty}
    (default : L.Val b) :
    Option (ProgramAction g.prog who) → L.Val b
  | none => default
  | some ai =>
      match ProgramAction.toAction ai with
      | Sigma.mk τ v =>
          if hτ : τ = b then hτ ▸ v else default

@[simp] theorem valueOfProgramMoveOr_commitAt
    {g : WFProgram P L} {Γ : VCtx P L}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (default v : L.Val b) :
    valueOfProgramMoveOr (g := g) (who := who) (b := b) default
        (some (ProgramAction.commitAt suffix v)) = v := by
  unfold valueOfProgramMoveOr
  simp only [ProgramAction.toAction]
  by_cases hty : (ProgramAction.commitAt suffix v).cursor.ty = b
  · rw [dif_pos hty]
    exact ProgramAction.commitAt_value_cast suffix v hty
  · exact False.elim (hty (by
      simpa [ProgramAction.commitAt_cursor] using
        ProgramSuffix.ty_commitCursor suffix))

theorem valueOfProgramMoveOr_eq_of_toAction
    {g : WFProgram P L} {who : P} {b : L.Ty}
    (default v : L.Val b) (ai : ProgramAction g.prog who)
    (hact : ProgramAction.toAction ai = Sigma.mk b v) :
    valueOfProgramMoveOr (g := g) (who := who) (b := b) default
        (some ai) = v := by
  cases ai with
  | mk cursor value =>
      unfold ProgramAction.toAction at hact
      unfold valueOfProgramMoveOr
      simp only [ProgramAction.toAction]
      simp only [Sigma.mk.injEq] at hact
      rcases hact with ⟨hty, hvalue⟩
      rw [dif_pos hty]
      cases hty
      exact eq_of_heq hvalue

/-- A support value from a fallback Vegas behavioral profile at a commit site.
This avoids any global `Nonempty (L.Val b)` assumption. -/
noncomputable def fallbackValueAtCommit
    (g : WFProgram P L) (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) : L.Val b :=
  Classical.choose <|
    (ProgramBehavioralStrategyPMF.headKernel
      ((suffix.behavioralProfilePMF (fun i => (fallback i).val)) who)
      view).support_nonempty

theorem fallbackValueAtCommit_mem_support
    (g : WFProgram P L) (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) :
    fallbackValueAtCommit g fallback suffix view ∈
      (ProgramBehavioralStrategyPMF.headKernel
        ((suffix.behavioralProfilePMF (fun i => (fallback i).val)) who)
        view).support :=
  Classical.choose_spec <|
    (ProgramBehavioralStrategyPMF.headKernel
      ((suffix.behavioralProfilePMF (fun i => (fallback i).val)) who)
      view).support_nonempty

theorem fallbackValueAtCommit_guard
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ)) :
    evalGuard (Player := P) (L := L) R
      (fallbackValueAtCommit g fallback suffix (projectViewEnv who ρ)) ρ =
        true := by
  exact headKernelPMF_supported_atCursor g hctx fallback suffix ρ
    (fallbackValueAtCommit_mem_support g fallback suffix
      (projectViewEnv who ρ))

/-- The head PMF for an owned Vegas commit site, read from a total sequential
FOSG behavioral profile when the current private observation is reachable, and
from `fallback` otherwise. -/
noncomputable def collapsedHeadKernelAtCommit
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) : PMF (L.Val b) := by
  classical
  let fallbackPMF :=
    ProgramBehavioralStrategyPMF.headKernel
      ((suffix.behavioralProfilePMF (fun i => (fallback i).val)) who)
      view
  exact if hrep : ∃ h : (observedProgramFOSG g hctx).History,
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCommitSite suffix view then
    let h := Classical.choose hrep
    PMF.map
      (valueOfProgramMoveOr
        (fallbackValueAtCommit g fallback suffix view))
      ((β.toProfile who) (h.playerView who))
  else
    fallbackPMF

/-- On a reachable current private observation, `collapsedHeadKernelAtCommit`
can be computed using any representative history for that observation. -/
theorem collapsedHeadKernelAtCommit_eq_of_privateObs
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ)
    (h : (observedProgramFOSG g hctx).History)
    (hobs :
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCommitSite suffix view) :
    collapsedHeadKernelAtCommit g hctx β fallback suffix view =
      PMF.map
        (valueOfProgramMoveOr
          (fallbackValueAtCommit g fallback suffix view))
        ((β.toProfile who) (h.playerView who)) := by
  classical
  unfold collapsedHeadKernelAtCommit
  let hrep : ∃ h : (observedProgramFOSG g hctx).History,
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCommitSite suffix view := ⟨h, hobs⟩
  rw [dif_pos hrep]
  have hchoose :
      privateObsOfCursorWorld who (Classical.choose hrep).lastState =
        privateObsOfCursorWorld who h.lastState := by
    rw [Classical.choose_spec hrep, hobs]
  change PMF.map
      (valueOfProgramMoveOr
        (fallbackValueAtCommit g fallback suffix view))
      ((β.toProfile who) ((Classical.choose hrep).playerView who)) =
    PMF.map
      (valueOfProgramMoveOr
        (fallbackValueAtCommit g fallback suffix view))
      ((β.toProfile who) (h.playerView who))
  rw [legalBehavioralProfile_apply_eq_of_privateObsOfLastState_eq
    g hctx who β (Classical.choose hrep) h hchoose]

theorem collapsedHeadKernelAtCommit_eq_fallback_of_not_exists
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ)
    (hnorep : ¬ ∃ h : (observedProgramFOSG g hctx).History,
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCommitSite suffix view) :
    collapsedHeadKernelAtCommit g hctx β fallback suffix view =
      ProgramBehavioralStrategyPMF.headKernel
        ((suffix.behavioralProfilePMF (fun i => (fallback i).val)) who)
        view := by
  classical
  unfold collapsedHeadKernelAtCommit
  rw [dif_neg hnorep]

theorem collapsedHeadKernelAtCommit_guard_of_not_exists
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ))
    (hnorep : ¬ ∃ h : (observedProgramFOSG g hctx).History,
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCommitSite suffix (projectViewEnv who ρ))
    {v : L.Val b}
    (hv : v ∈
      (collapsedHeadKernelAtCommit g hctx β fallback suffix
        (projectViewEnv who ρ)).support) :
    evalGuard (Player := P) (L := L) R v ρ = true := by
  rw [collapsedHeadKernelAtCommit_eq_fallback_of_not_exists
    g hctx β fallback suffix (projectViewEnv who ρ) hnorep] at hv
  exact headKernelPMF_supported_atCursor g hctx fallback suffix ρ hv

theorem valueOfProgramMoveOr_guard_of_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    {ρ : Env L.Val (eraseVCtx Γ)}
    (h : (observedProgramFOSG g hctx).History)
    (hobs :
      privateObsOfCursorWorld who h.lastState =
        privateObsOfCommitSite suffix (projectViewEnv who ρ))
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈ (observedProgramFOSG g hctx).availableMoves h who)
    {default v : L.Val b}
    (hv : valueOfProgramMoveOr default oi = v) :
    evalGuard (Player := P) (L := L) R v ρ = true := by
  have hlocal0 :
      oi ∈ (observedProgramFOSG g hctx).availableMovesAtState
        h.lastState who := by
    simpa [GameTheory.FOSG.availableMoves] using hoi
  have hvalue : valueOfProgramMoveOr default oi = v := hv
  cases hlast : h.lastState with
  | mk data valid =>
      rcases data with ⟨cursor, env⟩
      rw [hlast] at hlocal0 hobs
      dsimp [privateObsOfCursorWorld, privateObsOfCommitSite] at hobs
      injection hobs with hcursor henv
      change cursor =
        ProgramCursor.CommitCursor.toProgramCursor suffix.commitCursor at hcursor
      cases hcursor
      cases oi with
      | none =>
          have hactive :
              who ∈ CursorCheckedWorld.active
                (⟨{ cursor :=
                    ProgramCursor.CommitCursor.toProgramCursor
                      suffix.commitCursor,
                    env := env }, valid⟩ : CursorCheckedWorld g) := by
            exact active_mem_of_eq_commit
              (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix)
              (ProgramSuffix.commitCursor_toProgramCursor_prog suffix)
              env
          have hnot :
              who ∉ CursorCheckedWorld.active
                (⟨{ cursor :=
                    ProgramCursor.CommitCursor.toProgramCursor
                      suffix.commitCursor,
                    env := env }, valid⟩ : CursorCheckedWorld g) := by
            simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
              GameTheory.FOSG.locallyLegalAtState] using hlocal0
          exact False.elim (hnot hactive)
      | some ai =>
          have hact :
              ProgramAction.toAction ai ∈
                FOSGBridge.availableActions
                  ({ Γ :=
                      (ProgramCursor.CommitCursor.toProgramCursor
                        suffix.commitCursor).Γ,
                     prog :=
                      (ProgramCursor.CommitCursor.toProgramCursor
                        suffix.commitCursor).prog,
                     env := env } : World P L) who := by
            simpa [observedProgramFOSG, GameTheory.FOSG.availableMovesAtState,
              GameTheory.FOSG.locallyLegalAtState,
              CursorCheckedWorld.availableProgramActions,
              CursorCheckedWorld.availableActions,
              CursorCheckedWorld.toWorld] using hlocal0.2.1
          have hbroad :=
            availableActions_of_eq_commit
              (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix)
              (ProgramSuffix.commitCursor_toProgramCursor_prog suffix)
              env hact
          rcases hbroad with ⟨u, huact, hguard_env⟩
          have hdecode :
              valueOfProgramMoveOr default (some ai) = u :=
            valueOfProgramMoveOr_eq_of_toAction default u ai huact
          have huv : u = v := by
            rw [← hdecode]
            exact hvalue
          subst v
          have hview :
              projectViewEnv who
                  (VEnv.eraseEnv
                    ((ProgramSuffix.commitCursor_toProgramCursor_Γ suffix) ▸
                      env)) =
                projectViewEnv who ρ := by
            have hleft := projectViewEnv_eraseEnv_cast_heq who
              (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix) env
            have hright : HEq
                (cast (Eq.symm (privateObsOfCommitSite._proof_1 suffix))
                  (projectViewEnv who ρ))
                (projectViewEnv who ρ) := by
              exact cast_heq _ _
            exact eq_of_heq (hleft.trans (henv.trans hright))
          have hctx_local :
              WFCtx (L := L) Γ :=
            suffix.wfctx hctx g.wf.1
          have hfresh_local :
              Fresh x Γ :=
            (suffix.fresh g.wf.1).1
          have hsc_local :
              GuardUsesOnly (L := L) (Γ := Γ) (x := x)
                (who := who) R :=
            ViewScoped.commit_guard_usesOnly
              (suffix.viewScoped g.wf.2.2)
          rw [← evalGuard_eq_of_projectViewEnv_eq
            hctx_local hfresh_local hsc_local hview]
          simpa [hdecode] using hguard_env

/-- Raw syntax-recursive Vegas behavioral strategy obtained by collapsing a
sequential FOSG behavioral profile.  The legality wrapper is proved separately
so the construction itself stays transparent. -/
noncomputable def collapsedBehavioralStrategyPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      ProgramSuffix g.prog p → ProgramBehavioralStrategyPMF who p
  | _, .ret _, _ => .ret
  | _, .letExpr _ _ k, suffix =>
      .letExpr (collapsedBehavioralStrategyPMF g hctx β fallback who k
        (ProgramSuffix.letExpr suffix))
  | _, .sample _ _ k, suffix =>
      .sample (collapsedBehavioralStrategyPMF g hctx β fallback who k
        (ProgramSuffix.sample suffix))
  | _, .commit x owner (b := b) R k, suffix => by
      by_cases howner : owner = who
      · exact howner ▸
          (.commitOwn
            { run := collapsedHeadKernelAtCommit g hctx β fallback suffix }
            (collapsedBehavioralStrategyPMF g hctx β fallback owner k
              (ProgramSuffix.commit suffix)))
      · exact .commitOther howner
          (collapsedBehavioralStrategyPMF g hctx β fallback who k
            (ProgramSuffix.commit suffix))
  | _, .reveal _ _ _ _ k, suffix =>
      .reveal (collapsedBehavioralStrategyPMF g hctx β fallback who k
        (ProgramSuffix.reveal suffix))
termination_by _ p _ => syntaxSteps p

/-- Raw profile-level version of `collapsedBehavioralStrategyPMF`. -/
noncomputable def collapsedBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g) :
    ProgramBehavioralProfilePMF g.prog :=
  fun who =>
    collapsedBehavioralStrategyPMF g hctx β fallback who g.prog
      ProgramSuffix.here

theorem behavioralProfilePMF_collapsedBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p) (who : P) :
    suffix.behavioralProfilePMF
        (collapsedBehavioralProfilePMF g hctx β fallback) who =
      collapsedBehavioralStrategyPMF g hctx β fallback who p suffix := by
  induction suffix generalizing who with
  | here =>
      rfl
  | letExpr suffix ih =>
      rw [ProgramSuffix.behavioralProfilePMF_letExpr]
      rw [ih]
      simp [collapsedBehavioralStrategyPMF]
  | sample suffix ih =>
      rw [ProgramSuffix.behavioralProfilePMF_sample]
      rw [ih]
      simp [collapsedBehavioralStrategyPMF]
  | commit suffix ih =>
      rw [ProgramSuffix.behavioralProfilePMF_commit]
      rw [show
        suffix.behavioralProfilePMF
            (collapsedBehavioralProfilePMF g hctx β fallback) =
          fun i =>
            collapsedBehavioralStrategyPMF g hctx β fallback i _ suffix
        from funext (ih)]
      simp only [ProgramBehavioralProfilePMF.tail,
        ProgramBehavioralStrategyPMF.tailOwn,
        collapsedBehavioralStrategyPMF, ↓reduceDIte, ne_eq]
      split
      · rename_i howner
        cases howner
        rfl
      · rfl
  | reveal suffix ih =>
      rw [ProgramSuffix.behavioralProfilePMF_reveal]
      rw [ih]
      simp [collapsedBehavioralStrategyPMF]

theorem collapsedBehavioralStrategyPMF_isLegal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    (who : P) :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    (suffix : ProgramSuffix g.prog p) →
      (collapsedBehavioralStrategyPMF
        g hctx β fallback who p suffix).IsLegal p := by
  intro Γ p
  induction p with
  | ret payoffs =>
    intro _suffix
    simp [ProgramBehavioralStrategyPMF.IsLegal]
  | letExpr _x _e k ih =>
    intro suffix
    simpa [collapsedBehavioralStrategyPMF,
      ProgramBehavioralStrategyPMF.IsLegal] using
      ih (ProgramSuffix.letExpr suffix)
  | sample _x _D k ih =>
    intro suffix
    simpa [collapsedBehavioralStrategyPMF,
      ProgramBehavioralStrategyPMF.IsLegal] using
      ih (ProgramSuffix.sample suffix)
  | commit x owner R k ih =>
    intro suffix
    by_cases howner : owner = who
    · subst owner
      dsimp [collapsedBehavioralStrategyPMF,
        ProgramBehavioralStrategyPMF.IsLegal]
      simp only [eq_self, ProgramBehavioralStrategyPMF.headKernel,
        ProgramBehavioralStrategyPMF.tailOwn]
      constructor
      · intro ρ v hv
        have hvHead :
            v ∈ (collapsedHeadKernelAtCommit g hctx β fallback suffix
              (projectViewEnv who ρ)).support := by
          simpa [collapsedBehavioralStrategyPMF,
            ProgramBehavioralStrategyPMF.headKernel] using hv
        by_cases hrep : ∃ h : (observedProgramFOSG g hctx).History,
            privateObsOfCursorWorld who h.lastState =
              privateObsOfCommitSite suffix (projectViewEnv who ρ)
        · rcases hrep with ⟨h, hobs⟩
          rw [collapsedHeadKernelAtCommit_eq_of_privateObs
            g hctx β fallback suffix (projectViewEnv who ρ) h hobs] at hvHead
          rcases (PMF.mem_support_map_iff _ _ _).mp hvHead with
            ⟨oi, hoi, hdecode⟩
          have hoiAvail :
              oi ∈ (observedProgramFOSG g hctx).availableMoves h who :=
            (β who).2 h hoi
          exact valueOfProgramMoveOr_guard_of_available
            g hctx suffix h hobs hoiAvail hdecode
        · exact collapsedHeadKernelAtCommit_guard_of_not_exists
            g hctx β fallback suffix ρ hrep hvHead
      · simpa [collapsedBehavioralStrategyPMF,
          ProgramBehavioralStrategyPMF.tailOwn] using
          ih (ProgramSuffix.commit suffix)
    · simpa [collapsedBehavioralStrategyPMF,
        ProgramBehavioralStrategyPMF.IsLegal, howner,
        ProgramBehavioralStrategyPMF.tail] using
        ih (ProgramSuffix.commit suffix)
  | reveal _y _owner _x _hx k ih =>
    intro suffix
    simpa [collapsedBehavioralStrategyPMF,
      ProgramBehavioralStrategyPMF.IsLegal] using
      ih (ProgramSuffix.reveal suffix)

theorem collapsedBehavioralProfilePMF_isLegal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g) :
    (collapsedBehavioralProfilePMF g hctx β fallback).IsLegal := by
  intro who
  exact collapsedBehavioralStrategyPMF_isLegal
    g hctx β fallback who g.prog ProgramSuffix.here

noncomputable def collapsedLegalBehavioralProfilePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g) :
    LegalProgramBehavioralProfilePMF g :=
  fun who =>
    ⟨collapsedBehavioralProfilePMF g hctx β fallback who,
      collapsedBehavioralProfilePMF_isLegal g hctx β fallback who⟩

theorem observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStepPMF_collapsed
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
      (fun a =>
        PMF.map (CheckedWorld.ofCursorChecked (hctx := hctx))
          ((observedProgramFOSG g hctx).transition
            h.lastState a)) =
      checkedProfileStepPMF g hctx
        (collapsedLegalBehavioralProfilePMF g hctx β fallback)
        (CheckedWorld.ofCursorChecked (hctx := hctx) h.lastState) := by
  let σc := collapsedLegalBehavioralProfilePMF g hctx β fallback
  refine observedProgramLegalActionLaw_bind_checkedTransition_eq_semanticStep
    g hctx β (checkedProfileStepPMF g hctx σc) ?_ ?_ h hterm
  · intro h hterm hactive
    let G := observedProgramFOSG g hctx
    rw [GameTheory.FOSG.legalActionLaw_eq_pure_noop_of_active_empty
      (G := G) β h hterm hactive]
    simp only [PMF.pure_bind]
    rw [observedProgramTransition_map_checkedWorld_eq_checkedTransition
      (hctx := hctx)
      (w := h.lastState)
      (a := ⟨GameTheory.FOSG.noopAction
          (fun who : P => ProgramAction g.prog who),
        G.legal_noopAction_of_active_empty_of_not_terminal hactive hterm⟩)]
    apply checkedTransition_eq_checkedProfileStepPMF_of_active_empty
    simpa [G, observedProgramFOSG, checkedActive, CheckedWorld.ofCursorChecked,
      CursorCheckedWorld.active] using hactive
  · intro h _hterm who _hmem Γ x b R k env suffix wctx fresh viewScoped
      normalized legal _hchecked _hworld hobs
    let G := observedProgramFOSG g hctx
    let default : L.Val b :=
      fallbackValueAtCommit g fallback suffix
        (projectViewEnv who (VEnv.eraseEnv env))
    have hhead :=
      collapsedHeadKernelAtCommit_eq_of_privateObs
        g hctx β fallback suffix
        (projectViewEnv who (VEnv.eraseEnv env)) h hobs
    simp only [σc, collapsedLegalBehavioralProfilePMF,
      checkedProfileStepPMF]
    rw [behavioralProfilePMF_collapsedBehavioralProfilePMF
      g hctx β fallback suffix who]
    simp only [FOSG.legalBehavioralProfile_toProfile_apply,
      ProgramBehavioralStrategyPMF.headKernel,
      collapsedBehavioralStrategyPMF, ↓reduceDIte]
    change (β.toProfile who (h.playerView who)).bind
        (checkedCommitContinuation g hctx env suffix wctx fresh
          viewScoped normalized legal) =
      PMF.map
        (fun v =>
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _) v env
             suffix := .commit suffix
             wctx := WFCtx.cons fresh.1 wctx
             fresh := fresh.2
             viewScoped := viewScoped.2
             normalized := normalized
             legal := legal.2 } : CheckedWorld g hctx))
        (collapsedHeadKernelAtCommit g hctx β fallback suffix
          (projectViewEnv who (VEnv.eraseEnv env)))
    rw [show
      PMF.map
        (fun v =>
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _) v env
             suffix := .commit suffix
             wctx := WFCtx.cons fresh.1 wctx
             fresh := fresh.2
             viewScoped := viewScoped.2
             normalized := normalized
             legal := legal.2 } : CheckedWorld g hctx))
        (collapsedHeadKernelAtCommit g hctx β fallback suffix
          (projectViewEnv who (VEnv.eraseEnv env))) =
      PMF.map
        (fun v =>
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _) v env
             suffix := .commit suffix
             wctx := WFCtx.cons fresh.1 wctx
             fresh := fresh.2
             viewScoped := viewScoped.2
             normalized := normalized
             legal := legal.2 } : CheckedWorld g hctx))
        (PMF.map
          (valueOfProgramMoveOr
            (fallbackValueAtCommit g fallback suffix
              (projectViewEnv who (VEnv.eraseEnv env))))
          (β.toProfile who (h.playerView who))) from
        congrArg
          (PMF.map
            (fun v =>
              ({ Γ := _
                 prog := k
                 env := VEnv.cons (Player := P) (L := L) (x := x)
                   (τ := .hidden who _) v env
                 suffix := .commit suffix
                 wctx := WFCtx.cons fresh.1 wctx
                 fresh := fresh.2
                 viewScoped := viewScoped.2
                 normalized := normalized
                 legal := legal.2 } : CheckedWorld g hctx)))
          hhead]
    rw [PMF.map_comp]
    rw [← PMF.bind_pure_comp]
    refine Math.ProbabilityMassFunction.bind_congr_on_support
      ((β.toProfile who) (h.playerView who))
      (checkedCommitContinuation g hctx env suffix wctx fresh
        viewScoped normalized legal)
      (PMF.pure ∘
        (fun oi =>
          ({ Γ := _
             prog := k
             env := VEnv.cons (Player := P) (L := L) (x := x)
               (τ := .hidden who _)
               (valueOfProgramMoveOr (g := g) (who := who) (b := b)
                 default oi) env
             suffix := .commit suffix
             wctx := WFCtx.cons fresh.1 wctx
             fresh := fresh.2
             viewScoped := viewScoped.2
             normalized := normalized
             legal := legal.2 } : CheckedWorld g hctx)))
      ?_
    intro oi hoi
    have hoiAvail :
        oi ∈ G.availableMoves h who := (β who).2 h hoi
    have hlocal0 :
        oi ∈ G.availableMovesAtState h.lastState who := by
      simpa [G, GameTheory.FOSG.availableMoves] using hoiAvail
    cases hlast : h.lastState with
    | mk data valid =>
        rcases data with ⟨cursor, env'⟩
        rw [hlast] at hlocal0 hobs
        dsimp [privateObsOfCursorWorld, privateObsOfCommitSite] at hobs
        injection hobs with hcursor henv
        change cursor =
          ProgramCursor.CommitCursor.toProgramCursor suffix.commitCursor at hcursor
        cases hcursor
        cases oi with
        | none =>
            have hactiveMem :
                who ∈ CursorCheckedWorld.active
                  (⟨{ cursor :=
                      ProgramCursor.CommitCursor.toProgramCursor
                        suffix.commitCursor,
                      env := env' }, valid⟩ : CursorCheckedWorld g) := by
              exact active_mem_of_eq_commit
                (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix)
                (ProgramSuffix.commitCursor_toProgramCursor_prog suffix)
                env'
            have hnot :
                who ∉ CursorCheckedWorld.active
                  (⟨{ cursor :=
                      ProgramCursor.CommitCursor.toProgramCursor
                        suffix.commitCursor,
                      env := env' }, valid⟩ : CursorCheckedWorld g) := by
              simpa [G, observedProgramFOSG,
                GameTheory.FOSG.availableMovesAtState,
                GameTheory.FOSG.locallyLegalAtState] using hlocal0
            exact False.elim (hnot hactiveMem)
        | some ai =>
            have hact :
                ProgramAction.toAction ai ∈
                  FOSGBridge.availableActions
                    ({ Γ :=
                        (ProgramCursor.CommitCursor.toProgramCursor
                          suffix.commitCursor).Γ,
                       prog :=
                        (ProgramCursor.CommitCursor.toProgramCursor
                          suffix.commitCursor).prog,
                       env := env' } : World P L) who := by
              simpa [G, observedProgramFOSG,
                GameTheory.FOSG.availableMovesAtState,
                GameTheory.FOSG.locallyLegalAtState,
                CursorCheckedWorld.availableProgramActions,
                CursorCheckedWorld.availableActions,
                CursorCheckedWorld.toWorld] using hlocal0.2.1
            have hbroad :=
              availableActions_of_eq_commit
                (ProgramSuffix.commitCursor_toProgramCursor_Γ suffix)
                (ProgramSuffix.commitCursor_toProgramCursor_prog suffix)
                env' hact
            rcases hbroad with ⟨u, huact, _hguard⟩
            have hdecode :
                valueOfProgramMoveOr
                    (g := g) (who := who) (b := b)
                    default (some ai) = u :=
              valueOfProgramMoveOr_eq_of_toAction default u ai huact
            cases ai with
            | mk cursorAi value =>
                unfold ProgramAction.toAction at huact
                simp only [Sigma.mk.injEq] at huact
                rcases huact with ⟨hty, hval⟩
                dsimp [checkedCommitContinuation]
                rw [dif_pos hty]
                have hv :
                    hty ▸ value =
                      valueOfProgramMoveOr
                        (g := g) (who := who) (b := b)
                        default (some (ProgramAction.mk cursorAi value)) := by
                  rw [hdecode]
                  cases hty
                  exact eq_of_heq hval
                have henvEq :
                    VEnv.cons (Player := P) (L := L) (x := x)
                        (τ := .hidden who _) (hty ▸ value) env =
                      VEnv.cons (Player := P) (L := L) (x := x)
                        (τ := .hidden who _)
                        (valueOfProgramMoveOr
                          (g := g) (who := who) (b := b)
                          default
                          (some (ProgramAction.mk cursorAi value))) env :=
                  VEnv.cons_ext hv rfl
                rw [henvEq]

/-- Direct FOSG-step closure for an arbitrary observed-program behavioral
profile after collapsing it back to a Vegas PMF behavioral profile. -/
theorem observedProgramLegalActionLaw_bind_cursorVegasOutcomeKernelPMF_collapsed
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g)
    (h : (observedProgramFOSG g hctx).History)
    (hterm : ¬ (observedProgramFOSG g hctx).terminal h.lastState) :
    let σc := collapsedLegalBehavioralProfilePMF g hctx β fallback
    ((observedProgramFOSG g hctx).legalActionLaw β h hterm).bind
        (fun a =>
          ((observedProgramFOSG g hctx).transition h.lastState a).bind
            (fun dst =>
              cursorVegasOutcomeKernelPMF σc
                (h.extendByOutcome a dst).lastState)) =
      cursorVegasOutcomeKernelPMF σc h.lastState := by
  intro σc
  exact
    observedProgramCursorStepValue_of_checkedStep
      g hctx β
      (checkedProfileStepPMF g hctx σc)
      (checkedVegasOutcomeKernelPMF (hctx := hctx) σc)
      (cursorVegasOutcomeKernelPMF σc)
      (by intro w; rfl)
      (by
        intro w
        exact checkedProfileStepPMF_bind_checkedVegasOutcomeKernelPMF
          g hctx σc w)
      (by
        intro h hterm
        exact
          observedProgramLegalActionLaw_bind_checkedTransition_eq_checkedProfileStepPMF_collapsed
            g hctx β fallback h hterm)
      h hterm

/-- Continuation value for a total observed-program FOSG profile, interpreted
through its collapsed Vegas behavioral profile. -/
noncomputable def observedProgramCollapsedOutcomeValuePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    [Fintype P]
    [∀ who : P, Fintype (Option (ProgramAction g.prog who))]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g) :
    GameTheory.FOSG.History.OutcomeValue
      (G := observedProgramFOSG g hctx)
      β
      (Outcome P) :=
  let σc := collapsedLegalBehavioralProfilePMF g hctx β fallback
  observedProgramOutcomeValueOfCursorValue
    g hctx β
    (cursorVegasOutcomeKernelPMF σc)
    (by
      intro w hterm
      exact cursorVegasOutcomeKernelPMF_terminal
        (hctx := hctx) σc w hterm)
    (by
      intro h hterm
      exact
        observedProgramLegalActionLaw_bind_cursorVegasOutcomeKernelPMF_collapsed
          g hctx β fallback h hterm)

noncomputable def observedProgramCollapsedOutcomeKernelPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (_fallback : LegalProgramBehavioralProfilePMF g) : PMF (Outcome P) :=
  PMF.map (observedProgramHistoryOutcome g hctx)
    (observedProgramRunDist g hctx LF β)

theorem observedProgramCollapsedOutcomeKernelPMF_eq_toKernelGamePMF_by_value
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g) :
    observedProgramCollapsedOutcomeKernelPMF g hctx LF β fallback =
      (toKernelGamePMF g).outcomeKernel
        (collapsedLegalBehavioralProfilePMF g hctx β fallback) := by
  letI : Fintype (CursorCheckedWorld g) :=
    observedProgramFOSG.instFintypeWorld g hctx LF
  letI : ∀ who : P,
      Fintype (Option (ProgramAction g.prog who)) :=
    fun who =>
      observedProgramFOSG.instFintypeOptionAction
        g hctx LF who
  letI : DecidablePred (observedProgramFOSG g hctx).terminal :=
    observedProgramFOSG.instDecidablePredTerminal g hctx
  let R := observedProgramCollapsedOutcomeValuePMF g hctx β fallback
  have hclosure :=
    R.map_observe_runDist_eq_value
      (syntaxSteps g.prog)
      (by
        change
          (observedProgramFOSG g hctx).init.remainingSyntaxSteps ≤
            syntaxSteps g.prog
        exact observedProgramFOSG_initial_remainingSyntaxSteps_le g hctx)
  simpa [R, observedProgramCollapsedOutcomeValuePMF,
    observedProgramCollapsedOutcomeKernelPMF] using hclosure

theorem observedProgramCollapsedOutcomeKernelPMF_eq_toKernelGamePMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ) (LF : FiniteValuation L)
    [Fintype P]
    (β : (observedProgramFOSG g hctx).LegalBehavioralProfile)
    (fallback : LegalProgramBehavioralProfilePMF g) :
    observedProgramCollapsedOutcomeKernelPMF g hctx LF β fallback =
      (toKernelGamePMF g).outcomeKernel
        (collapsedLegalBehavioralProfilePMF g hctx β fallback) := by
  exact observedProgramCollapsedOutcomeKernelPMF_eq_toKernelGamePMF_by_value
    g hctx LF β fallback

end Observed

end FOSGBridge
end Vegas
