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
    (view : ViewEnv who Γ) :
    PMF (Option (ProgramAction g.prog who)) :=
  match p with
  | .commit x owner (b := b) R k =>
      if howner : owner = who then
        by
          cases howner
          let σp : ProgramBehavioralProfile (.commit x who R k) :=
            suffix.behavioralProfile (fun i => (σ i).val)
          let d := ProgramBehavioralStrategy.headKernel (σp who) view
          have hd :
              FDist.totalWeight d = 1 :=
            ProgramBehavioralStrategy.headKernel_normalized
              (σp who) view
          exact PMF.map
            (fun v => some
              (ProgramAction.commitAt suffix v))
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
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) :
    moveAtProgramCursor g hctx σ who suffix view =
      by
        let σp : ProgramBehavioralProfile (.commit x who R k) :=
          suffix.behavioralProfile (fun i => (σ i).val)
        let d := ProgramBehavioralStrategy.headKernel (σp who) view
        have hd : FDist.totalWeight d = 1 :=
          ProgramBehavioralStrategy.headKernel_normalized
            (σp who) view
        exact PMF.map
          (fun v => some
            (ProgramAction.commitAt suffix v))
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
      (ProgramBehavioralStrategy.headKernel
        ((suffix.behavioralProfile (fun i => (σ i).val)) who)
        (projectViewEnv who ρ))
      (fun v => evalGuard (Player := P) (L := L) R v ρ = true) := by
  let raw : ProgramBehavioralProfile g.prog :=
    fun i => (σ i).val
  have hraw : raw.IsLegal := fun i => (σ i).2
  have hcursor : (suffix.behavioralProfile raw).IsLegal :=
    suffix.behavioralProfile_isLegal hraw
  have hsite := hcursor who
  simp [ProgramBehavioralStrategy.IsLegal] at hsite
  simpa [raw] using hsite.1 ρ

/-! ## PMF behavioral profile candidate

The PMF variant is the target needed for general Kuhn M→B transport. Unlike
the `FDist` transport above, it can represent arbitrary real-valued
behavioural probabilities induced by a mixed pure profile. -/

noncomputable def moveAtProgramCursorPMF
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    PMF (Option (ProgramAction g.prog who)) :=
  match p with
  | .commit x owner (b := b) R k =>
      if howner : owner = who then
        by
          cases howner
          let σp : ProgramBehavioralProfilePMF (.commit x who R k) :=
            suffix.behavioralProfilePMF (fun i => (σ i).val)
          exact PMF.map
            (fun v => some
              (ProgramAction.commitAt suffix v))
            (ProgramBehavioralStrategyPMF.headKernel (σp who) view)
      else
        PMF.pure none
  | _ => PMF.pure none

theorem moveAtProgramCursorPMF_suffix_cast
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P)
    {Γ : VCtx P L} {p q : VegasCore P L Γ}
    (h : p = q)
    (suffix : ProgramSuffix g.prog p)
    (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      moveAtProgramCursorPMF g hctx σ who (h ▸ suffix) view := by
  cases h
  rfl

@[simp] theorem moveAtProgramCursorPMF_ret
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    (suffix : ProgramSuffix g.prog (.ret payoffs))
    (who : P) (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      PMF.pure none := by
  rfl

@[simp] theorem moveAtProgramCursorPMF_letExpr
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.letExpr x e k))
    (who : P) (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      PMF.pure none := by
  rfl

@[simp] theorem moveAtProgramCursorPMF_sample
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.sample x D k))
    (who : P) (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      PMF.pure none := by
  rfl

@[simp] theorem moveAtProgramCursorPMF_commit_owner
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      PMF.map
        (fun v => some
          (ProgramAction.commitAt suffix v))
        (ProgramBehavioralStrategyPMF.headKernel
          ((suffix.behavioralProfilePMF (fun i => (σ i).val)) who) view) := by
  simp [moveAtProgramCursorPMF]

@[simp] theorem moveAtProgramCursorPMF_commit_nonowner
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {owner who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x owner R k))
    (view : ViewEnv who Γ) (howner : owner ≠ who) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      PMF.pure none := by
  simp [moveAtProgramCursorPMF, howner]

@[simp] theorem moveAtProgramCursorPMF_reveal
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {y : VarId} {owner : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden owner b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.reveal y owner x hx k))
    (who : P) (view : ViewEnv who Γ) :
    moveAtProgramCursorPMF g hctx σ who suffix view =
      PMF.pure none := by
  rfl

theorem headKernelPMF_supported_atCursor
    (g : WFProgram P L) (_hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (suffix : ProgramSuffix g.prog (.commit x who R k))
    (ρ : Env L.Val (eraseVCtx Γ))
    {v : L.Val b}
    (hv : v ∈
      (ProgramBehavioralStrategyPMF.headKernel
        ((suffix.behavioralProfilePMF (fun i => (σ i).val)) who)
        (projectViewEnv who ρ)).support) :
    evalGuard (Player := P) (L := L) R v ρ = true := by
  let raw : ProgramBehavioralProfilePMF g.prog :=
    fun i => (σ i).val
  have hraw : raw.IsLegal := fun i => (σ i).2
  have hcursor : (suffix.behavioralProfilePMF raw).IsLegal :=
    suffix.behavioralProfilePMF_isLegal hraw
  have hsite := hcursor who
  have hsite' :
      (∀ (ρ : Env L.Val (eraseVCtx Γ)) {v : L.Val b},
        v ∈ (ProgramBehavioralStrategyPMF.headKernel
          ((suffix.behavioralProfilePMF raw) who)
          (projectViewEnv who ρ)).support →
        evalGuard (Player := P) (L := L) R v ρ = true) ∧
        ProgramBehavioralStrategyPMF.IsLegal
          k (ProgramBehavioralStrategyPMF.tailOwn
            ((suffix.behavioralProfilePMF raw) who)) := by
    simpa [raw, ProgramBehavioralStrategyPMF.IsLegal] using hsite
  exact hsite'.1 ρ hv

noncomputable def moveAtCursorWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    PMF (Option (ProgramAction g.prog who)) :=
  moveAtProgramCursor g hctx σ who w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def moveAtCheckedWorld
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CheckedWorld g hctx) :
    PMF (Option (ProgramAction g.prog who)) :=
  moveAtProgramCursor g hctx σ who w.suffix
    (projectViewEnv who (VEnv.eraseEnv w.env))

noncomputable def moveAtCursorWorldPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P) (w : CursorCheckedWorld g) :
    PMF (Option (ProgramAction g.prog who)) :=
  moveAtProgramCursorPMF g hctx σ who w.1.suffix
    (projectViewEnv who (VEnv.eraseEnv w.1.env))

noncomputable def moveAtCheckedWorldPMF
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P) (w : CheckedWorld g hctx) :
    PMF (Option (ProgramAction g.prog who)) :=
  moveAtProgramCursorPMF g hctx σ who w.suffix
    (projectViewEnv who (VEnv.eraseEnv w.env))

@[simp] theorem moveAtCheckedWorld_ofCursorChecked
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtCheckedWorld g hctx σ who
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      moveAtCursorWorld g hctx σ who w := rfl

@[simp] theorem moveAtCheckedWorldPMF_ofCursorChecked
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P) (w : CursorCheckedWorld g) :
    moveAtCheckedWorldPMF g hctx σ who
        (CheckedWorld.ofCursorChecked (hctx := hctx) w) =
      moveAtCursorWorldPMF g hctx σ who w := rfl

set_option linter.flexible false in
theorem moveAtProgramCursor_support_availableAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfile g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (env : VEnv L Γ)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈
      (moveAtProgramCursor g hctx σ who suffix
        (projectViewEnv who (VEnv.eraseEnv env))).support) :
    oi ∈ CursorCheckedWorld.availableProgramMovesAt
      p env suffix who := by
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
          ProgramBehavioralStrategy.headKernel
            ((suffix.behavioralProfile (fun i => (σ i).val)) who)
            (projectViewEnv who (VEnv.eraseEnv env))
        have hd :
            FDist.totalWeight d = 1 :=
          ProgramBehavioralStrategy.headKernel_normalized
            ((suffix.behavioralProfile (fun i => (σ i).val)) who)
            (projectViewEnv who (VEnv.eraseEnv env))
        have hoi' :
            ∃ v, ¬(d.toPMF hd) v = 0 ∧
              some
                (ProgramAction.commitAt suffix v) = oi := by
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
          exact headKernel_supported_atCursor
            g hctx σ suffix (VEnv.eraseEnv env) v hvFD
        simp only [CursorCheckedWorld.availableProgramMovesAt, active,
          Finset.mem_singleton, CursorCheckedWorld.availableProgramActionsAt,
          availableActions, ↓reduceIte, ProgramAction.toAction,
          Set.mem_setOf_eq, Sigma.mk.injEq, eq_mpr_eq_cast,
          VegasCore.commit.injEq, true_and, not_true_eq_false,
          ProgramAction.commitAt_cursor]
        constructor
        · refine ⟨v, ⟨⟨ProgramSuffix.ty_commitCursor
              suffix, ?_⟩, hguard⟩⟩
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
    (who : P) (w : CursorCheckedWorld g)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈ (moveAtCursorWorld g hctx σ who w).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    moveAtProgramCursor_support_availableAt
      g hctx σ who w.1.suffix w.1.env hoi
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

theorem moveAtProgramCursorPMF_support_availableAt
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P) {Γ : VCtx P L} {p : VegasCore P L Γ}
    (suffix : ProgramSuffix g.prog p)
    (env : VEnv L Γ)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈
      (moveAtProgramCursorPMF g hctx σ who suffix
        (projectViewEnv who (VEnv.eraseEnv env))).support) :
    oi ∈ CursorCheckedWorld.availableProgramMovesAt
      p env suffix who := by
  cases p with
  | ret payoffs =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursorPMF] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | letExpr x e k =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursorPMF] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | sample x D k =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursorPMF] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | reveal y owner x hx k =>
      have hoiNone : oi = none := by
        simpa [moveAtProgramCursorPMF] using hoi
      subst oi
      simp [CursorCheckedWorld.availableProgramMovesAt, active]
  | commit x owner R k =>
      by_cases howner : owner = who
      · cases howner
        let d :=
          ProgramBehavioralStrategyPMF.headKernel
            ((suffix.behavioralProfilePMF (fun i => (σ i).val)) who)
            (projectViewEnv who (VEnv.eraseEnv env))
        have hoi' :
            ∃ v, v ∈ d.support ∧
              some (ProgramAction.commitAt suffix v) = oi := by
          simpa [moveAtProgramCursorPMF, d] using hoi
        rcases hoi' with ⟨v, hv, hvo⟩
        rw [← hvo]
        have hguard :
            evalGuard (Player := P) (L := L) R v (VEnv.eraseEnv env) = true := by
          exact headKernelPMF_supported_atCursor
            g hctx σ suffix (VEnv.eraseEnv env) hv
        simp only [CursorCheckedWorld.availableProgramMovesAt, active,
          Finset.mem_singleton, CursorCheckedWorld.availableProgramActionsAt,
          availableActions, ↓reduceIte, ProgramAction.toAction,
          Set.mem_setOf_eq, Sigma.mk.injEq, eq_mpr_eq_cast,
          VegasCore.commit.injEq, true_and, not_true_eq_false,
          ProgramAction.commitAt_cursor]
        constructor
        · refine ⟨v, ⟨⟨ProgramSuffix.ty_commitCursor
              suffix, ?_⟩, hguard⟩⟩
          exact cast_heq _ v
        · refine ⟨x, who, _, R, k, ?_, rfl, ?_⟩
          · exact ⟨rfl, rfl, rfl, HEq.rfl, HEq.rfl⟩
          · rfl
      · have hoiNone : oi = none := by
          simpa [moveAtProgramCursorPMF, howner] using hoi
        subst oi
        have hnot : who ≠ owner := fun h => howner h.symm
        simp [CursorCheckedWorld.availableProgramMovesAt, active, hnot]

theorem moveAtCursorWorldPMF_support_available
    (g : WFProgram P L) (hctx : WFCtx g.Γ)
    (σ : LegalProgramBehavioralProfilePMF g)
    (who : P) (w : CursorCheckedWorld g)
    {oi : Option (ProgramAction g.prog who)}
    (hoi : oi ∈ (moveAtCursorWorldPMF g hctx σ who w).support) :
    oi ∈ (observedProgramFOSG g hctx).availableMovesAtState w who := by
  have hlocal :=
    moveAtProgramCursorPMF_support_availableAt
      g hctx σ who w.1.suffix w.1.env hoi
  cases oi with
  | none =>
      simpa [moveAtCursorWorldPMF, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.toWorld] using hlocal
  | some ai =>
      simpa [moveAtCursorWorldPMF, observedProgramFOSG,
        GameTheory.FOSG.availableMovesAtState,
        GameTheory.FOSG.locallyLegalAtState, CursorCheckedWorld.active,
        CursorCheckedWorld.availableProgramActions,
        CursorCheckedWorld.availableProgramActionsAt,
        CursorCheckedWorld.availableProgramMovesAt, CursorCheckedWorld.availableActions,
        CursorCheckedWorld.toWorld, availableActions] using hlocal

end Observed

end FOSGBridge
end Vegas
