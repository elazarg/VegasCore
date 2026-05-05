import Vegas.FOSG.Basic
import Vegas.Syntax.Strategy.Conversions

/-!
# Syntax strategy projection along program suffixes

This module contains syntax-recursive strategy operations that project fixed
program profiles from a root program to a suffix. The canonical machine and
FOSG constructions deliberately do not import this layer; it is used by the
syntax-facing cursor/event-law adapters only.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ProgramSuffix

noncomputable def pureProfile
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ProgramPureProfile root →
      ProgramPureProfile p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact ih σ
  | sample s ih => intro σ; exact ih σ
  | commit s ih =>
      intro σ
      exact ProgramPureProfile.tail (ih σ)
  | reveal s ih => intro σ; exact ih σ

noncomputable def pureStrategy
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) (who : P) :
    ProgramPureStrategy who root →
      ProgramPureStrategy who p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact ih σ
  | sample s ih => intro σ; exact ih σ
  | @commit Γ x owner b R k s ih =>
      intro σ
      by_cases h : owner = who
      · cases h
        exact ProgramPureStrategy.tailOwn (ih σ)
      · simpa [ProgramPureStrategy, h] using ih σ
  | reveal s ih => intro σ; exact ih σ

theorem pureStrategy_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) (who : P)
    {σ : ProgramPureStrategy who root}
    (hσ : σ.RespectsGuards root) :
    (s.pureStrategy who σ).RespectsGuards p := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih => simpa [pureStrategy] using ih hσ
  | sample s ih => simpa [pureStrategy] using ih hσ
  | reveal s ih => simpa [pureStrategy] using ih hσ
  | @commit Γ x owner b R k s ih =>
      have hsite := ih hσ
      by_cases h : owner = who
      · cases h
        dsimp [pureStrategy]
        have hsite' :
            (ProgramPureStrategy.headKernel (s.pureStrategy who σ)).RespectsGuard
                (x := x) (who := who) (b := b) R ∧
              (ProgramPureStrategy.tailOwn (s.pureStrategy who σ)).RespectsGuards
                k := by
          simpa [ProgramPureStrategy.RespectsGuards] using hsite
        simpa [pureStrategy] using hsite'.2
      · dsimp [pureStrategy]
        simpa [ProgramPureStrategy.RespectsGuards, h] using hsite

@[simp] theorem pureProfile_letExpr
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.letExpr x e k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.letExpr s).pureProfile σ =
      s.pureProfile σ := rfl

@[simp] theorem pureProfile_sample
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.sample x D k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.sample s).pureProfile σ =
      s.pureProfile σ := rfl

@[simp] theorem pureProfile_commit
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.commit s).pureProfile σ =
      ProgramPureProfile.tail
        (s.pureProfile σ) := rfl

@[simp] theorem pureProfile_reveal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (s : ProgramSuffix root (.reveal y who x hx k))
    (σ : ProgramPureProfile root) :
    (ProgramSuffix.reveal s).pureProfile σ =
      s.pureProfile σ := rfl

theorem pureProfile_apply
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    (σ : ProgramPureProfile root) (who : P) :
    s.pureProfile σ who = s.pureStrategy who (σ who) := by
  induction s generalizing σ with
  | here => rfl
  | letExpr s ih => simpa [pureStrategy] using ih σ
  | sample s ih => simpa [pureStrategy] using ih σ
  | reveal s ih => simpa [pureStrategy] using ih σ
  | @commit Γ x owner b R k s ih =>
      rw [pureProfile_commit]
      by_cases h : owner = who
      · cases h
        simp [pureStrategy, ProgramPureProfile.tail, ih]
      · simp [pureStrategy, h, ProgramPureProfile.tail, ih]

theorem pureProfile_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    {σ : ProgramPureProfile root}
    (hσ : σ.RespectsGuards) :
    (s.pureProfile σ).RespectsGuards := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih => exact ih hσ
  | sample s ih => exact ih hσ
  | commit s ih =>
      exact ProgramPureProfile.tail_isLegal (ih hσ)
  | reveal s ih => exact ih hσ

noncomputable def behavioralProfile
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ProgramBehavioralProfile root →
      ProgramBehavioralProfile p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact ih σ
  | sample s ih => intro σ; exact ih σ
  | commit s ih =>
      intro σ
      exact ProgramBehavioralProfile.tail (ih σ)
  | reveal s ih => intro σ; exact ih σ

@[simp] theorem behavioralProfile_letExpr
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.letExpr x e k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.letExpr s).behavioralProfile σ =
      s.behavioralProfile σ := rfl

@[simp] theorem behavioralProfile_sample
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.sample x D k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.sample s).behavioralProfile σ =
      s.behavioralProfile σ := rfl

@[simp] theorem behavioralProfile_commit
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.commit s).behavioralProfile σ =
      ProgramBehavioralProfile.tail
        (s.behavioralProfile σ) := rfl

@[simp] theorem behavioralProfile_reveal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (s : ProgramSuffix root (.reveal y who x hx k))
    (σ : ProgramBehavioralProfile root) :
    (ProgramSuffix.reveal s).behavioralProfile σ =
      s.behavioralProfile σ := rfl

theorem behavioralProfile_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    {σ : ProgramBehavioralProfile root}
    (hσ : σ.RespectsGuards) :
    (s.behavioralProfile σ).RespectsGuards := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih => exact ih hσ
  | sample s ih => exact ih hσ
  | commit s ih =>
      exact ProgramBehavioralProfile.tail_isLegal (ih hσ)
  | reveal s ih => exact ih hσ

noncomputable def behavioralProfilePMF
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p) :
    ProgramBehavioralProfilePMF root →
      ProgramBehavioralProfilePMF p := by
  induction s with
  | here => intro σ; exact σ
  | letExpr s ih => intro σ; exact (fun who =>
      match ih σ who with
      | .letExpr tail => tail)
  | sample s ih => intro σ; exact (fun who =>
      match ih σ who with
      | .sample tail => tail)
  | commit s ih =>
      intro σ
      exact ProgramBehavioralProfilePMF.tail (ih σ)
  | reveal s ih => intro σ; exact (fun who =>
      match ih σ who with
      | .reveal tail => tail)

theorem behavioralProfilePMF_letExpr
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {e : L.Expr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.letExpr x e k))
    (σ : ProgramBehavioralProfilePMF root) (who : P) :
    (ProgramSuffix.letExpr s).behavioralProfilePMF σ who =
      match s.behavioralProfilePMF σ who with
      | .letExpr tail => tail := by
  simp [behavioralProfilePMF]

theorem behavioralProfilePMF_sample
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {b : L.Ty}
    {D : L.DistExpr (erasePubVCtx Γ) b}
    {k : VegasCore P L ((x, .pub b) :: Γ)}
    (s : ProgramSuffix root (.sample x D k))
    (σ : ProgramBehavioralProfilePMF root) (who : P) :
    (ProgramSuffix.sample s).behavioralProfilePMF σ who =
      match s.behavioralProfilePMF σ who with
      | .sample tail => tail := by
  simp [behavioralProfilePMF]

@[simp] theorem behavioralProfilePMF_commit
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (s : ProgramSuffix root (.commit x who R k))
    (σ : ProgramBehavioralProfilePMF root) :
    (ProgramSuffix.commit s).behavioralProfilePMF σ =
      ProgramBehavioralProfilePMF.tail
        (s.behavioralProfilePMF σ) := by
  simp [behavioralProfilePMF]

theorem behavioralProfilePMF_reveal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀}
    {y : VarId} {who : P} {x : VarId} {b : L.Ty}
    {hx : VHasVar Γ x (.hidden who b)}
    {k : VegasCore P L ((y, .pub b) :: Γ)}
    (s : ProgramSuffix root (.reveal y who x hx k))
    (σ : ProgramBehavioralProfilePMF root) (i : P) :
    (ProgramSuffix.reveal s).behavioralProfilePMF σ i =
      match s.behavioralProfilePMF σ i with
      | .reveal tail => tail := by
  simp [behavioralProfilePMF]

theorem behavioralProfilePMF_isLegal
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    {σ : ProgramBehavioralProfilePMF root}
    (hσ : σ.RespectsGuards) :
    (s.behavioralProfilePMF σ).RespectsGuards := by
  induction s generalizing σ with
  | here => exact hσ
  | letExpr s ih =>
      intro who
      rw [behavioralProfilePMF_letExpr]
      have hsite := ih hσ who
      cases hprof : s.behavioralProfilePMF σ who with
      | letExpr tail =>
          rw [hprof] at hsite
          simpa [hprof, ProgramBehavioralStrategyPMF.RespectsGuards] using hsite
  | sample s ih =>
      intro who
      rw [behavioralProfilePMF_sample]
      have hsite := ih hσ who
      cases hprof : s.behavioralProfilePMF σ who with
      | sample tail =>
          rw [hprof] at hsite
          simpa [hprof, ProgramBehavioralStrategyPMF.RespectsGuards] using hsite
  | commit s ih =>
      exact ProgramBehavioralProfilePMF.tail_isLegal (ih hσ)
  | reveal s ih =>
      intro who
      rw [behavioralProfilePMF_reveal]
      have hsite := ih hσ who
      cases hprof : s.behavioralProfilePMF σ who with
      | reveal tail =>
          rw [hprof] at hsite
          simpa [hprof, ProgramBehavioralStrategyPMF.RespectsGuards] using hsite

theorem behavioralProfilePMF_toBehavioralPMF
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    (σ : ProgramPureProfile root) :
    s.behavioralProfilePMF
        (ProgramPureProfile.toBehavioralPMF root σ) =
      ProgramPureProfile.toBehavioralPMF p (s.pureProfile σ) := by
  induction s generalizing σ with
  | here => rfl
  | @letExpr Γ x b e k s ih =>
      funext who
      change (match s.behavioralProfilePMF
          (ProgramPureProfile.toBehavioralPMF root σ) who with
        | .letExpr tail => tail) =
        ProgramPureProfile.toBehavioralPMF k (s.pureProfile σ) who
      rw [congrFun (ih σ) who]
      rfl
  | @sample Γ x b D k s ih =>
      funext who
      change (match s.behavioralProfilePMF
          (ProgramPureProfile.toBehavioralPMF root σ) who with
        | .sample tail => tail) =
        ProgramPureProfile.toBehavioralPMF k (s.pureProfile σ) who
      rw [congrFun (ih σ) who]
      rfl
  | commit s ih =>
      rw [behavioralProfilePMF_commit, pureProfile_commit, ih,
        ProgramPureProfile.tail_toBehavioralPMF]
  | @reveal Γ y owner x b hx k s ih =>
      funext who
      change (match s.behavioralProfilePMF
          (ProgramPureProfile.toBehavioralPMF root σ) who with
        | .reveal tail => tail) =
        ProgramPureProfile.toBehavioralPMF k (s.pureProfile σ) who
      rw [congrFun (ih σ) who]
      rfl

theorem behavioralProfilePMF_toPMFProfile
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    (σ : ProgramBehavioralProfile root) :
    s.behavioralProfilePMF
        (ProgramBehavioralProfile.toPMFProfile root σ) =
      ProgramBehavioralProfile.toPMFProfile p
        (s.behavioralProfile σ) := by
  induction s generalizing σ with
  | here => rfl
  | @letExpr Γ x b e k s ih =>
      funext who
      change (match s.behavioralProfilePMF
          (ProgramBehavioralProfile.toPMFProfile root σ) who with
        | .letExpr tail => tail) =
        ProgramBehavioralProfile.toPMFProfile k
          (s.behavioralProfile σ) who
      rw [congrFun (ih σ) who]
      rfl
  | @sample Γ x b D k s ih =>
      funext who
      change (match s.behavioralProfilePMF
          (ProgramBehavioralProfile.toPMFProfile root σ) who with
        | .sample tail => tail) =
        ProgramBehavioralProfile.toPMFProfile k
          (s.behavioralProfile σ) who
      rw [congrFun (ih σ) who]
      rfl
  | commit s ih =>
      rw [behavioralProfilePMF_commit, behavioralProfile_commit, ih,
        ProgramBehavioralProfile.tail_toPMFProfile]
  | @reveal Γ y owner x b hx k s ih =>
      funext who
      change (match s.behavioralProfilePMF
          (ProgramBehavioralProfile.toPMFProfile root σ) who with
        | .reveal tail => tail) =
        ProgramBehavioralProfile.toPMFProfile k
          (s.behavioralProfile σ) who
      rw [congrFun (ih σ) who]
      rfl

theorem behavioralProfile_toBehavioral
    {Γ₀ Γ : VCtx P L} {root : VegasCore P L Γ₀} {p : VegasCore P L Γ}
    (s : ProgramSuffix root p)
    (σ : ProgramPureProfile root) :
    s.behavioralProfile
        (ProgramPureProfile.toBehavioral root σ) =
      ProgramPureProfile.toBehavioral p (s.pureProfile σ) := by
  induction s generalizing σ with
  | here => rfl
  | letExpr s ih => exact ih σ
  | sample s ih => exact ih σ
  | commit s ih =>
      rw [behavioralProfile_commit, pureProfile_commit, ih,
        ProgramPureProfile.tail_toBehavioral]
  | reveal s ih => exact ih σ

end ProgramSuffix

end Vegas

