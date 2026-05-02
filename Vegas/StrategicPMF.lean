import Vegas.PureStrategic
import Vegas.Strategic

/-!
# PMF Behavioral Strategic Semantics

This file mirrors `Vegas.Strategic` and `Vegas.PureStrategic` but uses `PMF`
(Mathlib's probability mass functions) instead of `FDist` (rational Finsupp
distributions). The PMF layer is needed for theorem backends that produce
real-valued behavioral strategies.

Key definitions:
* `ProgramBehavioralKernelPMF` — PMF-valued behavioral kernel (no normalization
  witness needed since PMF is inherently normalized)
* `ProgramBehavioralStrategyPMF` — per-player PMF behavioral strategy
* `ProgramBehavioralProfilePMF` — joint PMF behavioral profile
* `outcomeDistBehavioralPMF` — PMF-valued outcome distribution

Key conversions:
* `ProgramBehavioralKernelPMF.ofPure` — pure kernel → PMF kernel (via `PMF.pure`)
* `ProgramBehavioralKernelPMF.ofFDist` — FDist kernel → PMF kernel (via `toPMF`)
* `ProgramPureProfile.toBehavioralPMF` — pure profile → PMF behavioral profile
* `ProgramBehavioralProfile.toPMFProfile` — FDist behavioral → PMF behavioral

Key agreement theorems:
* `outcomeDistBehavioralPMF_toBehavioralPMF_eq` — pure lift through PMF layer
  agrees with `outcomeDistPure.toPMF`
* `outcomeDistBehavioralPMF_toPMFProfile_eq` — FDist behavioral converted to
  PMF agrees with `outcomeDistBehavioral.toPMF`
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-! ## PMF behavioral kernel -/

/-- A PMF behavioral choice rule for one fixed commit site. Unlike
`ProgramBehavioralKernel` (FDist-valued), no explicit normalization witness
is needed because PMF is inherently normalized. -/
@[ext]
structure ProgramBehavioralKernelPMF
    (who : P) (Γ : VCtx P L) (b : L.Ty) where
  run : ViewEnv who Γ → PMF (L.Val b)

namespace ProgramBehavioralKernelPMF

/-- Turn a deterministic local rule into a PMF behavioral local rule. -/
noncomputable def ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b) :
    ProgramBehavioralKernelPMF who Γ b :=
  { run := fun view => PMF.pure (κ view) }

@[simp] theorem run_ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b)
    (view : ViewEnv who Γ) :
    (ofPure κ).run view = PMF.pure (κ view) := rfl

/-- Convert an FDist behavioral kernel to a PMF behavioral kernel. -/
noncomputable def ofFDist
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : ProgramBehavioralKernel who Γ b) :
    ProgramBehavioralKernelPMF who Γ b :=
  { run := fun view => (κ.run view).toPMF (κ.normalized view) }

@[simp] theorem run_ofFDist
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : ProgramBehavioralKernel who Γ b)
    (view : ViewEnv who Γ) :
    (ofFDist κ).run view =
      (κ.run view).toPMF (κ.normalized view) := rfl

end ProgramBehavioralKernelPMF

/-! ## PMF behavioral strategy and profile -/

/-- Player-`who` PMF behavioral strategies for the fixed program `p`: one
PMF choice rule for each commit site of `p` owned by `who`. -/
inductive ProgramBehavioralStrategyPMF (who : P) :
    {Γ : VCtx P L} → VegasCore P L Γ → Type where
  | ret {Γ : VCtx P L} {u} :
      ProgramBehavioralStrategyPMF who (.ret (Γ := Γ) u)
  | letExpr {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {e : L.Expr (erasePubVCtx Γ) b} {k : VegasCore P L ((x, .pub b) :: Γ)} :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.letExpr x e k)
  | sample {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {D' : L.DistExpr (erasePubVCtx Γ) b}
      {k : VegasCore P L ((x, .pub b) :: Γ)} :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.sample x D' k)
  | commitOwn {Γ : VCtx P L} {x : VarId} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden who b) :: Γ)} :
      ProgramBehavioralKernelPMF who Γ b →
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.commit x who R k)
  | commitOther {Γ : VCtx P L} {x : VarId} {owner : P} {b : L.Ty}
      {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
      {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
      (h : owner ≠ who) :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.commit x owner R k)
  | reveal {Γ : VCtx P L} {y : VarId} {owner : P} {x : VarId} {b : L.Ty}
      {hx : VHasVar (L := L) Γ x (.hidden owner b)}
      {k : VegasCore P L ((y, .pub b) :: Γ)} :
      ProgramBehavioralStrategyPMF who k →
      ProgramBehavioralStrategyPMF who (.reveal y owner x hx k)

/-- Joint PMF behavioral strategy profile for the fixed program `p`. -/
abbrev ProgramBehavioralProfilePMF {Γ : VCtx P L} (p : VegasCore P L Γ) : Type :=
  ∀ who, ProgramBehavioralStrategyPMF who p

namespace ProgramBehavioralStrategyPMF

/-- Extract the current player's PMF behavioral rule at the head commit site. -/
def headKernel
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF who (.commit x who R k)) :
    ViewEnv who Γ → PMF (L.Val b) :=
  match σ with
  | .commitOwn kern _ => kern.run

/-- Drop the head commit-site choice rule from the acting player's strategy. -/
def tailOwn
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF who (.commit x who R k)) :
    ProgramBehavioralStrategyPMF who k :=
  match σ with
  | .commitOwn _ tail => tail

/-- Drop the head commit-site wrapper from any player's strategy. For the
owner this removes the owned kernel; for other players it removes the
`commitOther` wrapper. -/
def tail
    {Γ : VCtx P L} {x : VarId} {owner who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden owner b) :: Γ)}
    (σ : ProgramBehavioralStrategyPMF who (.commit x owner R k)) :
    ProgramBehavioralStrategyPMF who k :=
  match σ with
  | .commitOwn _ tail => tail
  | .commitOther _ tail => tail

@[simp] theorem headKernel_mk
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (kern : ProgramBehavioralKernelPMF who Γ b)
    (tail : ProgramBehavioralStrategyPMF who k) :
    headKernel (R := R) (.commitOwn kern tail) = kern.run := rfl

end ProgramBehavioralStrategyPMF

namespace ProgramBehavioralProfilePMF

/-- Drop the head commit site from a PMF behavioral profile. -/
def tail
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfilePMF (.commit x who R k)) :
    ProgramBehavioralProfilePMF k :=
  fun i => by
    by_cases h : who = i
    · subst h
      exact ProgramBehavioralStrategyPMF.tailOwn (σ who)
    · exact match σ i with
      | .commitOther _ tail => tail
      | .commitOwn _ tail => tail

end ProgramBehavioralProfilePMF

/-! ## Guard-legality predicate -/

/-- PMF-valued analogue of `ProgramBehavioralKernel.IsLegalAt`: at every
erased environment, the kernel's support is contained in the guard-satisfying
actions for the current commit site. -/
def ProgramBehavioralKernelPMF.IsLegalAt
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    (κ : ProgramBehavioralKernelPMF who Γ b)
    (R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool) : Prop :=
  ∀ (ρ : Env L.Val (eraseVCtx Γ)) {v : L.Val b},
    v ∈ (κ.run (projectViewEnv who ρ)).support →
      evalGuard (Player := P) (L := L) R v ρ = true

/-- A PMF behavioral strategy is guard-legal when every owned commit-site
kernel is supported on guard-satisfying actions. -/
def ProgramBehavioralStrategyPMF.IsLegal : {who : P} →
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    ProgramBehavioralStrategyPMF who p → Prop
  | _, _, .ret _, _ => True
  | who, _, .letExpr _ _ k, .letExpr σ =>
      ProgramBehavioralStrategyPMF.IsLegal (who := who) k σ
  | who, _, .sample _ _ k, .sample σ =>
      ProgramBehavioralStrategyPMF.IsLegal (who := who) k σ
  | who, _, .commit _x owner R k, σ => by
      by_cases h : owner = who
      · subst h
        exact
          (∀ (ρ : Env L.Val (eraseVCtx _)) {v},
            v ∈ (ProgramBehavioralStrategyPMF.headKernel σ
              (projectViewEnv owner ρ)).support →
              evalGuard (Player := P) (L := L) R v ρ = true) ∧
          ProgramBehavioralStrategyPMF.IsLegal (who := owner) k
            (ProgramBehavioralStrategyPMF.tailOwn σ)
      · exact ProgramBehavioralStrategyPMF.IsLegal (who := who) k
          (ProgramBehavioralStrategyPMF.tail σ)
  | who, _, .reveal _ _ _ _ k, .reveal σ =>
      ProgramBehavioralStrategyPMF.IsLegal (who := who) k σ

/-- A PMF behavioral profile is legal when each player's PMF strategy is
guard-legal. -/
def ProgramBehavioralProfilePMF.IsLegal {Γ : VCtx P L} {p : VegasCore P L Γ}
    (σ : ProgramBehavioralProfilePMF p) : Prop :=
  ∀ who, (σ who).IsLegal p

namespace ProgramBehavioralProfilePMF

theorem tail_isLegal
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    {σ : ProgramBehavioralProfilePMF (.commit x who R k)}
    (hσ : σ.IsLegal) :
    (tail σ).IsLegal := by
  intro i
  by_cases h : who = i
  · subst i
    have hsite := hσ who
    simp [ProgramBehavioralStrategyPMF.IsLegal] at hsite
    simpa [tail, ProgramBehavioralStrategyPMF.tailOwn] using hsite.2
  · have hsite := hσ i
    cases σi : σ i with
    | commitOwn kern tail' =>
        exact False.elim (h rfl)
    | commitOther hne tail' =>
        simpa [ProgramBehavioralStrategyPMF.IsLegal, tail, h, σi] using hsite

end ProgramBehavioralProfilePMF

/-- Guard-legal PMF behavioral strategies over a checked program bundle. -/
abbrev LegalProgramBehavioralStrategyPMF (g : WFProgram P L) (who : P) : Type :=
  { s : ProgramBehavioralStrategyPMF who g.prog //
    s.IsLegal g.prog }

/-- Guard-legal joint PMF behavioral profiles over a checked program bundle. -/
abbrev LegalProgramBehavioralProfilePMF (g : WFProgram P L) : Type :=
  ∀ who, LegalProgramBehavioralStrategyPMF g who

/-! ## PMF behavioral outcome distribution -/

/-- Evaluate a fixed-program PMF behavioral profile directly, threading the
continuation profile through the program structure. At sample nodes, the FDist
from nature is converted to a PMF via `NormalizedDists`. -/
noncomputable def outcomeDistBehavioralPMF :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      NormalizedDists p →
      ProgramBehavioralProfilePMF p →
      VEnv (Player := P) L Γ →
      PMF (Outcome P)
  | _, .ret payoffs, _, _, env =>
      PMF.pure (evalPayoffs payoffs env)
  | _, .letExpr x e k, hd, σ, env =>
      outcomeDistBehavioralPMF k hd (fun w => match σ w with | .letExpr tail => tail) <|
        VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env
  | _, .sample x D' k, hd, σ, env =>
      ((L.evalDist D' (VEnv.eraseSampleEnv env)).toPMF (hd.1 env)).bind
        (fun v =>
          outcomeDistBehavioralPMF k hd.2
            (fun w => match σ w with | .sample tail => tail)
            (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _) v env))
  | _, .commit x who (b := b) _ k, hd, σ, env =>
      (ProgramBehavioralStrategyPMF.headKernel (σ who)
        (projectViewEnv who (VEnv.eraseEnv env))).bind
        (fun v =>
          outcomeDistBehavioralPMF k hd
            (ProgramBehavioralProfilePMF.tail σ)
            (VEnv.cons (Player := P) (L := L) (x := x)
              (τ := .hidden who b) v env))
  | _, .reveal y _who _x (b := b) hx k, hd, σ, env =>
      let v : L.Val b := VEnv.get (Player := P) (L := L) env hx
      outcomeDistBehavioralPMF k hd (fun w => match σ w with | .reveal tail => tail)
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b) v env)

/-- At a commit node, `outcomeDistBehavioralPMF` depends only on `headKernel` at
the current view and the tail's outcome distribution. -/
theorem outcomeDistBehavioralPMF_commit_congr
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (hd : NormalizedDists (.commit x who R k))
    (σ₁ σ₂ : ProgramBehavioralProfilePMF (.commit x who R k))
    (env : VEnv (Player := P) L Γ)
    (hkernel :
      ProgramBehavioralStrategyPMF.headKernel (σ₁ who)
        (projectViewEnv who (VEnv.eraseEnv env)) =
      ProgramBehavioralStrategyPMF.headKernel (σ₂ who)
        (projectViewEnv who (VEnv.eraseEnv env)))
    (htail : ∀ v,
      outcomeDistBehavioralPMF k hd
        (ProgramBehavioralProfilePMF.tail σ₁)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who b) v env) =
      outcomeDistBehavioralPMF k hd
        (ProgramBehavioralProfilePMF.tail σ₂)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who b) v env)) :
    outcomeDistBehavioralPMF (.commit x who R k) hd σ₁ env =
      outcomeDistBehavioralPMF (.commit x who R k) hd σ₂ env := by
  simp only [outcomeDistBehavioralPMF]
  rw [hkernel]; congr 1; funext v; exact htail v

/-! ## Pure → PMF behavioral lift -/

namespace ProgramPureProfile

/-- Lift a fixed-program pure profile to a PMF behavioral profile. -/
noncomputable def toBehavioralPMF :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile p →
      ProgramBehavioralProfilePMF p
  | _, .ret _, _ => fun _ => .ret
  | _, .letExpr _ _ k, σ => fun w => .letExpr (toBehavioralPMF k σ w)
  | _, .sample _ _ k, σ => fun w => ProgramBehavioralStrategyPMF.sample (toBehavioralPMF k σ w)
  | _, .commit _ who _R k, σ =>
      fun i =>
        if h : who = i then
          h ▸ .commitOwn
            (ProgramBehavioralKernelPMF.ofPure
              (ProgramPureStrategy.headKernel (σ who)))
            (toBehavioralPMF k (tail σ) who)
        else
          .commitOther h (toBehavioralPMF k (tail σ) i)
  | _, .reveal _ _ _ _ k, σ => fun w => .reveal (toBehavioralPMF k σ w)

@[simp] theorem tail_toBehavioralPMF
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureProfile (.commit x who R k)) :
    ProgramBehavioralProfilePMF.tail
      (toBehavioralPMF (.commit x who R k) σ) =
      toBehavioralPMF k (tail σ) := by
  funext i
  by_cases h : who = i
  · subst h
    simp [toBehavioralPMF, ProgramBehavioralProfilePMF.tail,
      ProgramBehavioralStrategyPMF.tailOwn]
  · simp [toBehavioralPMF, ProgramBehavioralProfilePMF.tail, h]

theorem toBehavioralPMF_IsLegal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    (σ : ProgramPureProfile p) →
    σ.IsLegal →
    (ProgramPureProfile.toBehavioralPMF p σ).IsLegal
  | _, .ret _, _, _ => fun _ => trivial
  | _, .letExpr _ _ k, σ, hσ =>
      toBehavioralPMF_IsLegal k σ hσ
  | _, .sample _ _ k, σ, hσ =>
      toBehavioralPMF_IsLegal k σ hσ
  | _, .reveal _ _ _ _ k, σ, hσ =>
      toBehavioralPMF_IsLegal k σ hσ
  | _, .commit x who_c (b := b) R k, σ, hσ => by
      have htail : (ProgramPureProfile.tail σ).IsLegal := by
        intro j
        by_cases hj : who_c = j
        · subst hj
          have hσ_who : (σ who_c).IsLegal (.commit x who_c R k) := hσ who_c
          dsimp [ProgramPureStrategy.IsLegal] at hσ_who
          dsimp [ProgramPureProfile.tail]
          split at hσ_who
          · split
            · exact hσ_who.2
            · exact absurd rfl ‹_›
          · exact absurd rfl ‹_›
        · have hσ_j : (σ j).IsLegal (.commit x who_c R k) := hσ j
          dsimp [ProgramPureStrategy.IsLegal] at hσ_j
          dsimp [ProgramPureProfile.tail]
          split at hσ_j
          · rename_i h
            exact absurd h hj
          · split
            · rename_i h
              exact absurd h hj
            · exact hσ_j
      intro i
      by_cases hi : who_c = i
      · subst hi
        have hσ_who : (σ who_c).IsLegal (.commit x who_c R k) := hσ who_c
        dsimp [ProgramPureProfile.toBehavioralPMF, ProgramPureStrategy.IsLegal,
          ProgramBehavioralStrategyPMF.IsLegal] at hσ_who ⊢
        split at hσ_who
        · split
          · refine ⟨?_, ?_⟩
            · intro ρ v hv
              have hv_eq :
                  v = ProgramPureStrategy.headKernel (σ who_c)
                    (projectViewEnv who_c ρ) := by
                simpa only [ProgramBehavioralStrategyPMF.headKernel,
                  ProgramBehavioralKernelPMF.ofPure, PMF.support_pure,
                  Set.mem_singleton_iff] using hv
              rw [hv_eq]
              exact hσ_who.1 ρ
            · exact toBehavioralPMF_IsLegal k _ htail who_c
          · exact absurd rfl ‹_›
        · exact absurd rfl ‹_›
      · dsimp [ProgramPureProfile.toBehavioralPMF,
          ProgramBehavioralStrategyPMF.IsLegal]
        split
        · rename_i h
          exact absurd h hi
        · exact toBehavioralPMF_IsLegal k _ htail i

end ProgramPureProfile

/-- Lift a legal pure profile to a legal PMF behavioral profile. -/
noncomputable def LegalProgramPureProfile.toBehavioralPMF
    {g : WFProgram P L} (σ : LegalProgramPureProfile g) :
    LegalProgramBehavioralProfilePMF g :=
  let rawPure : ProgramPureProfile g.prog := fun i => (σ i).val
  let rawPureLegal : ProgramPureProfile.IsLegal rawPure := fun i => (σ i).2
  let rawBeh : ProgramBehavioralProfilePMF g.prog :=
    ProgramPureProfile.toBehavioralPMF g.prog rawPure
  let rawBehLegal : ProgramBehavioralProfilePMF.IsLegal rawBeh :=
    ProgramPureProfile.toBehavioralPMF_IsLegal g.prog rawPure rawPureLegal
  fun i => ⟨rawBeh i, rawBehLegal i⟩

/-! ## FDist behavioral → PMF behavioral conversion -/

namespace ProgramBehavioralProfile

/-- Convert an FDist behavioral profile to a PMF behavioral profile. -/
noncomputable def toPMFProfile :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramBehavioralProfile p →
      ProgramBehavioralProfilePMF p
  | _, .ret _, _ => fun _ => .ret
  | _, .letExpr _ _ k, σ => fun w => .letExpr (toPMFProfile k σ w)
  | _, .sample _ _ k, σ => fun w => ProgramBehavioralStrategyPMF.sample (toPMFProfile k σ w)
  | _, .commit _ who R k, σ =>
      fun i => by
        by_cases h : who = i
        · subst h
          let σ_pair : ProgramBehavioralKernel who _ _ ×
              ProgramBehavioralStrategy who k := by
            simpa [ProgramBehavioralStrategy] using σ who
          exact .commitOwn
            (ProgramBehavioralKernelPMF.ofFDist σ_pair.1)
            (toPMFProfile k (ProgramBehavioralProfile.tail σ) who)
        · exact .commitOther h
            (toPMFProfile k (ProgramBehavioralProfile.tail σ) i)
  | _, .reveal _ _ _ _ k, σ => fun w => .reveal (toPMFProfile k σ w)

@[simp] theorem tail_toPMFProfile
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramBehavioralProfile (.commit x who R k)) :
    ProgramBehavioralProfilePMF.tail (toPMFProfile (.commit x who R k) σ) =
      toPMFProfile k (ProgramBehavioralProfile.tail σ) := by
  funext i
  by_cases h : who = i
  · subst h
    simp [toPMFProfile, ProgramBehavioralProfilePMF.tail,
      ProgramBehavioralStrategyPMF.tailOwn]
  · simp [toPMFProfile, ProgramBehavioralProfilePMF.tail, h]

end ProgramBehavioralProfile

private theorem mem_fdist_support_of_mem_toPMF_support
    {α : Type} [DecidableEq α] {d : FDist α} {h : d.totalWeight = 1} {a : α}
    (ha : a ∈ (d.toPMF h).support) :
    a ∈ d.support := by
  rw [PMF.mem_support_iff, FDist.toPMF_apply] at ha
  rw [Finsupp.mem_support_iff]
  intro hzero
  exact ha (by rw [hzero, NNRat.toNNReal_zero]; rfl)

theorem ProgramBehavioralKernelPMF.ofFDist_IsLegalAt
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (κ : ProgramBehavioralKernel who Γ b)
    (hκ : κ.IsLegalAt R) :
    (ProgramBehavioralKernelPMF.ofFDist κ).IsLegalAt R := by
  intro ρ v hv
  exact hκ ρ v
    (mem_fdist_support_of_mem_toPMF_support
      (d := κ.run (projectViewEnv who ρ))
      (h := κ.normalized (projectViewEnv who ρ)) hv)

namespace ProgramBehavioralProfile

/-- Converting an FDist behavioral profile to PMF preserves guard-legality. -/
theorem toPMFProfile_isLegal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      {σ : ProgramBehavioralProfile p} →
      σ.IsLegal →
      (toPMFProfile p σ).IsLegal
  | _, .ret _, σ, hσ => by
      intro who
      simp [ProgramBehavioralStrategyPMF.IsLegal]
  | _, .letExpr _ _ k, σ, hσ => by
      intro who
      exact toPMFProfile_isLegal k (σ := fun i => σ i) hσ who
  | _, .sample _ _ k, σ, hσ => by
      intro who
      exact toPMFProfile_isLegal k (σ := fun i => σ i) hσ who
  | _, .commit _ who R k, σ, hσ => by
      intro i
      by_cases h : who = i
      · subst i
        let σpair : ProgramBehavioralKernel who _ _ ×
            ProgramBehavioralStrategy who k := by
          simpa [ProgramBehavioralStrategy] using σ who
        have hsite :
            σpair.1.IsLegalAt R ∧
              ProgramBehavioralStrategy.IsLegal (who := who) k σpair.2 := by
          have hraw := hσ who
          simpa [ProgramBehavioralStrategy.IsLegal, σpair] using hraw
        have htail :=
          toPMFProfile_isLegal k
            (σ := ProgramBehavioralProfile.tail σ)
            (ProgramBehavioralProfile.tail_isLegal hσ) who
        simpa [toPMFProfile, ProgramBehavioralStrategyPMF.IsLegal, σpair]
          using And.intro
            (ProgramBehavioralKernelPMF.ofFDist_IsLegalAt σpair.1 hsite.1)
            htail
      · have htail :=
          toPMFProfile_isLegal k
            (σ := ProgramBehavioralProfile.tail σ)
            (ProgramBehavioralProfile.tail_isLegal hσ) i
        simpa [toPMFProfile, h, ProgramBehavioralStrategyPMF.IsLegal]
          using htail
  | _, .reveal _ _ _ _ k, σ, hσ => by
      intro who
      exact toPMFProfile_isLegal k (σ := fun i => σ i) hσ who

end ProgramBehavioralProfile

namespace LegalProgramBehavioralProfile

/-- Convert a legal FDist behavioral profile to the corresponding legal PMF
behavioral profile. -/
noncomputable def toPMFProfile
    {g : WFProgram P L}
    (σ : LegalProgramBehavioralProfile g) :
    LegalProgramBehavioralProfilePMF g :=
  let raw : ProgramBehavioralProfile g.prog := fun i => (σ i).val
  let hraw : raw.IsLegal := fun i => (σ i).2
  fun i =>
    ⟨ProgramBehavioralProfile.toPMFProfile g.prog raw i,
      ProgramBehavioralProfile.toPMFProfile_isLegal g.prog hraw i⟩

end LegalProgramBehavioralProfile

/-! ## Agreement: pure lift through PMF = outcomeDistPure.toPMF -/

/-- Running the PMF behavioral lift of a pure profile yields the same outcome
distribution as `outcomeDistPure.toPMF`. -/
theorem outcomeDistBehavioralPMF_toBehavioralPMF_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramPureProfile p)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) :
    outcomeDistBehavioralPMF p hd
      (ProgramPureProfile.toBehavioralPMF p σ) env =
      (outcomeDistPure p σ env).toPMF
        (outcomeDistPure_totalWeight_eq_one hd) := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioralPMF, outcomeDistPure, FDist.toPMF_pure]
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistPure,
        ProgramPureProfile.toBehavioralPMF] using ih σ _ hd
  | sample x D' k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistPure]
      rw [FDist.toPMF_bind (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v => outcomeDistPure k σ (VEnv.cons (Player := P) (L := L)
          (x := x) (τ := .pub _) v env))
        (hd.1 env)
        (fun v => outcomeDistPure_totalWeight_eq_one hd.2)]
      congr 1; funext v
      exact ih σ _ hd.2
  | commit x who R k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistPure]
      have hhead :
          ProgramBehavioralStrategyPMF.headKernel
            ((ProgramPureProfile.toBehavioralPMF
              (.commit x who R k) σ) who)
            (projectViewEnv who (VEnv.eraseEnv env)) =
          PMF.pure
            ((ProgramPureStrategy.headKernel (σ who))
              (projectViewEnv who (VEnv.eraseEnv env))) := by
        simp [ProgramPureProfile.toBehavioralPMF, ProgramBehavioralStrategyPMF.headKernel,
          ProgramBehavioralKernelPMF.ofPure, ProgramPureStrategy.headKernel]
      rw [hhead, PMF.pure_bind]
      rw [ProgramPureProfile.tail_toBehavioralPMF]
      exact ih (ProgramPureProfile.tail σ)
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _)
          ((ProgramPureStrategy.headKernel (σ who))
            (projectViewEnv who (VEnv.eraseEnv env))) env) hd
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistPure,
        ProgramPureProfile.toBehavioralPMF] using ih σ _ hd

/-! ## Agreement: FDist behavioral converted to PMF = outcomeDistBehavioral.toPMF -/

/-- Running the PMF conversion of an FDist behavioral profile yields the same
outcome distribution as `outcomeDistBehavioral.toPMF`. -/
theorem outcomeDistBehavioralPMF_toPMFProfile_eq
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    (σ : ProgramBehavioralProfile p)
    (env : VEnv (Player := P) L Γ)
    (hd : NormalizedDists p) :
    outcomeDistBehavioralPMF p hd
      (ProgramBehavioralProfile.toPMFProfile p σ) env =
      (outcomeDistBehavioral p σ env).toPMF
        (outcomeDistBehavioral_totalWeight_eq_one hd) := by
  induction p with
  | ret u =>
      simp [outcomeDistBehavioralPMF, outcomeDistBehavioral, FDist.toPMF_pure]
  | letExpr x e k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistBehavioral,
        ProgramBehavioralProfile.toPMFProfile] using ih σ _ hd
  | sample x D' k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistBehavioral]
      rw [FDist.toPMF_bind (L.evalDist D' (VEnv.eraseSampleEnv env))
        (fun v => outcomeDistBehavioral k σ (VEnv.cons (Player := P) (L := L)
          (x := x) (τ := .pub _) v env))
        (hd.1 env)
        (fun v => outcomeDistBehavioral_totalWeight_eq_one hd.2)]
      congr 1; funext v
      exact ih σ _ hd.2
  | commit x who R k ih =>
      simp only [outcomeDistBehavioralPMF, outcomeDistBehavioral]
      -- The head kernel of the PMF profile is toPMF of the FDist head kernel
      have hhead :
          ProgramBehavioralStrategyPMF.headKernel
            ((ProgramBehavioralProfile.toPMFProfile
              (.commit x who R k) σ) who)
            (projectViewEnv who (VEnv.eraseEnv env)) =
          (ProgramBehavioralStrategy.headKernel (σ who)
            (projectViewEnv who (VEnv.eraseEnv env))).toPMF
          (ProgramBehavioralStrategy.headKernel_normalized (σ who)
            (projectViewEnv who (VEnv.eraseEnv env))) := by
        simp [ProgramBehavioralProfile.toPMFProfile,
          ProgramBehavioralStrategyPMF.headKernel,
          ProgramBehavioralKernelPMF.ofFDist,
          ProgramBehavioralStrategy.headKernel]
      rw [hhead]
      rw [FDist.toPMF_bind
        (ProgramBehavioralStrategy.headKernel (σ who)
          (projectViewEnv who (VEnv.eraseEnv env)))
        (fun v => outcomeDistBehavioral k
          (ProgramBehavioralProfile.tail σ)
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .hidden who _) v env))
        (ProgramBehavioralStrategy.headKernel_normalized (σ who)
          (projectViewEnv who (VEnv.eraseEnv env)))
        (fun v => outcomeDistBehavioral_totalWeight_eq_one
          (σ := ProgramBehavioralProfile.tail σ) hd)]
      congr 1; funext v
      rw [ProgramBehavioralProfile.tail_toPMFProfile]
      exact ih (ProgramBehavioralProfile.tail σ) _ hd
  | reveal y who x hx k ih =>
      simpa [outcomeDistBehavioralPMF, outcomeDistBehavioral,
        ProgramBehavioralProfile.toPMFProfile] using ih σ _ hd

/-! ## Checked PMF behavioral kernel game -/

/-- PMF-valued behavioral kernel game for a checked Vegas program.

Unlike `toKernelGame`, this game uses `PMF` behavioral strategies directly.
That matters for Kuhn mixed-to-behavioral results: an arbitrary mixed strategy
over pure profiles can induce real-valued behavioral probabilities, which need
not be representable by Vegas' rational `FDist` kernels. -/
noncomputable def toKernelGamePMF (g : WFProgram P L) : GameTheory.KernelGame P where
  Strategy := LegalProgramBehavioralStrategyPMF g
  Outcome := Outcome P
  utility := fun o i => (o i : ℝ)
  outcomeKernel := fun σ =>
    outcomeDistBehavioralPMF g.prog g.normalized (fun i => (σ i).val) g.env

@[simp] theorem toKernelGamePMF_outcomeKernel
    (g : WFProgram P L) (σ : LegalProgramBehavioralProfilePMF g) :
    (toKernelGamePMF g).outcomeKernel σ =
      outcomeDistBehavioralPMF g.prog g.normalized (fun i => (σ i).val) g.env := rfl

@[simp] theorem toKernelGamePMF_udist
    (g : WFProgram P L) (σ : LegalProgramBehavioralProfilePMF g) :
    (toKernelGamePMF g).udist σ =
      PMF.map (fun o : Outcome P => fun i => (o i : ℝ))
        (outcomeDistBehavioralPMF g.prog g.normalized
          (fun i => (σ i).val) g.env) := by
  rfl

/-- The PMF conversion of an FDist behavioral profile has the same outcome
kernel as the original FDist-valued kernel game profile. -/
theorem toKernelGamePMF_outcomeKernel_toPMFProfile_eq_toKernelGame
    (g : WFProgram P L)
    (σ : LegalProgramBehavioralProfile g) :
    (toKernelGamePMF g).outcomeKernel
        (LegalProgramBehavioralProfile.toPMFProfile σ) =
      (toKernelGame g).outcomeKernel σ := by
  let raw : ProgramBehavioralProfile g.prog := fun i => (σ i).val
  have heq :
      outcomeDistBehavioralPMF g.prog g.normalized
          (fun i =>
            ((LegalProgramBehavioralProfile.toPMFProfile σ) i).val)
          g.env =
        (outcomeDistBehavioral g.prog raw g.env).toPMF
          (outcomeDistBehavioral_totalWeight_eq_one
            (p := g.prog) (σ := raw) g.normalized) := by
    simpa [raw, LegalProgramBehavioralProfile.toPMFProfile] using
      outcomeDistBehavioralPMF_toPMFProfile_eq
        (p := g.prog) (σ := raw) (env := g.env) (hd := g.normalized)
  simpa [toKernelGamePMF_outcomeKernel, toKernelGame_outcomeKernel, raw]
    using heq

/-- The PMF behavioral lift of a legal pure profile has the same outcome
kernel as the fixed-program pure strategic form. -/
theorem toKernelGamePMF_outcomeKernel_eq_toStrategicKernelGame_toBehavioralPMF
    (g : WFProgram P L)
    (σ : LegalProgramPureProfile g) :
    (toKernelGamePMF g).outcomeKernel
        (LegalProgramPureProfile.toBehavioralPMF σ) =
      (toStrategicKernelGame g).outcomeKernel σ := by
  have heq :
      outcomeDistBehavioralPMF g.prog g.normalized
          (fun i => ((LegalProgramPureProfile.toBehavioralPMF (g := g) σ) i).val)
          g.env =
        (outcomeDistPure g.prog (fun i => (σ i).val) g.env).toPMF
          (outcomeDistPure_totalWeight_eq_one
            (p := g.prog) (σ := fun i => (σ i).val)
            g.normalized) :=
    outcomeDistBehavioralPMF_toBehavioralPMF_eq
      (p := g.prog)
      (σ := fun i => (σ i).val) (env := g.env) (hd := g.normalized)
  simp only [toKernelGamePMF_outcomeKernel, toStrategicKernelGame_outcomeKernel,
    heq]

end Vegas
