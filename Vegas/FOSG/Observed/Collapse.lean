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

end Observed

end FOSGBridge
end Vegas
