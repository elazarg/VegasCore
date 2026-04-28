import Vegas.FOSG.Observed.Base

namespace Vegas
namespace FOSGBridge

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace Observed
/-! ## Behavioral profile candidate

The following definitions build the program-action FOSG behavioral profile
induced by a legal Vegas behavioral profile.
-/

noncomputable def moveAtProgramCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv (P := P) (L := L) who Γ) :
    PMF (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
  match p with
  | .commit x owner (b := b) R k =>
      if howner : owner = who then
        by
          cases howner
          let σp : ProgramBehavioralProfile (P := P) (L := L) (.commit x who R k) :=
            suffix.behavioralProfile (fun i => (σ i).val)
          let d := ProgramBehavioralStrategy.headKernel (P := P) (L := L) (σp who) view
          have hd :
              FDist.totalWeight d = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              (P := P) (L := L) (σp who) view
          exact PMF.map
            (fun v => some
              (ProgramAction.commitAt (P := P) (L := L) suffix v))
            (d.toPMF hd)
      else
        PMF.pure none
  | _ => PMF.pure none

@[simp] theorem moveAtProgramCursor_commit_owner
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix (P := P) (L := L) g.prog (.commit x who R k))
    (view : ViewEnv (P := P) (L := L) who Γ) :
    moveAtProgramCursor g hctx σ who suffix view =
      by
        let σp : ProgramBehavioralProfile (P := P) (L := L) (.commit x who R k) :=
          suffix.behavioralProfile (fun i => (σ i).val)
        let d := ProgramBehavioralStrategy.headKernel (P := P) (L := L) (σp who) view
        have hd : FDist.totalWeight d = 1 :=
          ProgramBehavioralStrategy.headKernel_normalized
            (P := P) (L := L) (σp who) view
        exact PMF.map
          (fun v => some
            (ProgramAction.commitAt (P := P) (L := L) suffix v))
          (d.toPMF hd) := by
  simp [moveAtProgramCursor]

private theorem mem_fdist_support_of_mem_toPMF_support
    {α : Type} [DecidableEq α] {d : FDist α} {h : d.totalWeight = 1} {a : α}
    (ha : a ∈ (d.toPMF h).support) :
    a ∈ d.support := by
  rw [PMF.mem_support_iff, FDist.toPMF_apply] at ha
  rw [Finsupp.mem_support_iff]
  intro hzero
  exact ha (by rw [hzero, NNRat.toNNReal_zero]; rfl)

theorem headKernel_supported_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ)) :
    FDist.Supported
      (ProgramBehavioralStrategy.headKernel (P := P) (L := L)
        ((suffix.behavioralProfile (fun i => (σ i).val)) who)
        (projectViewEnv (P := P) (L := L) who ρ))
      (fun v => evalGuard (Player := P) (L := L) R v ρ = true) := by
  let raw : ProgramBehavioralProfile (P := P) (L := L) g.prog :=
    fun i => (σ i).val
  have hraw : raw.IsLegal := fun i => (σ i).2
  have hcursor : (suffix.behavioralProfile raw).IsLegal :=
    suffix.behavioralProfile_isLegal hraw
  have hsite := hcursor who
  simp [ProgramBehavioralStrategy.IsLegal] at hsite
  simpa [raw] using hsite.1 ρ

noncomputable def moveAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g) :
    PMF (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
  moveAtProgramCursor g hctx σ who w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def moveAtCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CheckedWorld g hctx) :
    PMF (Option (ProgramAction (P := P) (L := L) g.prog who)) :=
  moveAtProgramCursor g hctx σ who w.suffix
    (projectViewEnv who (VEnv.eraseEnv w.env))

@[simp] theorem moveAtCheckedWorld_ofCursorChecked
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g) :
    moveAtCheckedWorld (P := P) (L := L) g hctx σ who
        (CheckedWorld.ofCursorChecked (P := P) (L := L) (hctx := hctx) w) =
      moveAtCursorWorld (P := P) (L := L) g hctx σ who w := rfl

set_option linter.flexible false in
theorem moveAtProgramCursor_support_availableAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix (P := P) (L := L) g.prog p)
    (env : VEnv L Γ)
    {oi : Option (ProgramAction (P := P) (L := L) g.prog who)}
    (hoi : oi ∈
      (moveAtProgramCursor g hctx σ who suffix
        (projectViewEnv who (VEnv.eraseEnv env))).support) :
    oi ∈ CursorCheckedWorld.availableProgramMovesAt
      (P := P) (L := L) p env suffix who := by
  cases p with
  | ret payoffs =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursor] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | letExpr x e k =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursor] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | sample x D k =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursor] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | reveal y owner x hx k =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursor] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        let d :=
          ProgramBehavioralStrategy.headKernel (P := P) (L := L)
            ((suffix.behavioralProfile (fun i => (σ i).val)) who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
        have hd :
            FDist.totalWeight d = 1 :=
          ProgramBehavioralStrategy.headKernel_normalized
            (P := P) (L := L)
            ((suffix.behavioralProfile (fun i => (σ i).val)) who)
            (projectViewEnv (P := P) (L := L) who (VEnv.eraseEnv env))
        have hoi' :
            ∃ v, ¬(d.toPMF hd) v = 0 ∧
              some
                (ProgramAction.commitAt (P := P) (L := L) suffix v) = oi := by
          simpa [moveAtProgramCursor, d, hd] using hoi
        rcases hoi' with ⟨v, hvprob, hvo⟩
        rw [← hvo]
        have hv : v ∈ (d.toPMF hd).support := by
          rw [PMF.mem_support_iff]
          simpa [d] using hvprob
        have hvFD : v ∈ d.support :=
          mem_fdist_support_of_mem_toPMF_support (d := d) (h := hd) hv
        have hguard :
            evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env) = true := by
          exact headKernel_supported_atCursor (P := P) (L := L)
            g hctx σ suffix (VEnv.eraseEnv env) v hvFD
        simp [CursorCheckedWorld.availableProgramMovesAt,
          CursorCheckedWorld.availableProgramActionsAt, active,
          Vegas.FOSGBridge.availableActions, ProgramAction.toAction]
        constructor
        · refine ⟨v, ⟨⟨ProgramSuffix.ty_commitCursor
              (P := P) (L := L) suffix, ?_⟩, hguard⟩⟩
          exact cast_heq _ v
        · refine ⟨x, who, _, R, k, ?_, rfl, ?_⟩
          · exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
          · rfl
      · have hoiNone : oi = none := by
          simpa [moveAtProgramCursor, howner] using hoi
        subst oi
        have hnot : who ≠ owner := fun h => howner h.symm
        simp [CursorCheckedWorld.availableProgramMovesAt, active, hnot]

theorem moveAtCursorWorld_support_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld (P := P) (L := L) g)
    {oi : Option (ProgramAction (P := P) (L := L) g.prog who)}
    (hoi : oi ∈ (moveAtCursorWorld g hctx σ who w).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    moveAtProgramCursor_support_availableAt
      (P := P) (L := L) g hctx σ who w.1.suffix w.1.env hoi
  cases oi with
  | none =>
      simpa [moveAtCursorWorld, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.toWorld] using hlocal
  | some ai =>
      simpa [moveAtCursorWorld, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.availableActions,
        CursorCheckedWorld.toWorld, availableActions] using hlocal

end Observed

end FOSGBridge
end Vegas
