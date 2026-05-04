import Vegas.Strategy.PMF
import Vegas.Strategy.Pure

/-!
# Fixed-program strategy carrier conversions

This module contains conversions between syntax-recursive strategy carriers:
pure profiles to FDist/PMF behavioral profiles, and FDist behavioral profiles
to PMF behavioral profiles. It stays below all legacy outcome evaluators and
kernel-game packaging.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

namespace ProgramPureProfile

/-- Lift a fixed-program pure profile to the corresponding fixed-program
behavioral profile. -/
noncomputable def toBehavioral :
    {Γ : VCtx P L} →
      (p : VegasCore P L Γ) →
      ProgramPureProfile p →
      ProgramBehavioralProfile p
  | _, .ret _, _ => fun _ => PUnit.unit
  | _, .letExpr _ _ k, σ => toBehavioral k σ
  | _, .sample _ _ k, σ => toBehavioral k σ
  | _, .commit _ who R k, σ =>
      fun i =>
        by
          by_cases h : who = i
          · subst h
            simpa [ProgramBehavioralStrategy] using
              (ProgramBehavioralKernel.ofPure
                (ProgramPureStrategy.headKernel (σ who)),
               toBehavioral k (tail σ) who)
          · simpa [ProgramBehavioralStrategy, h] using
              toBehavioral k (tail σ) i
  | _, .reveal _ _ _ _ k, σ => toBehavioral k σ

@[simp] theorem tail_toBehavioral
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    {k : VegasCore P L ((x, .hidden who b) :: Γ)}
    (σ : ProgramPureProfile (.commit x who R k)) :
    ProgramBehavioralProfile.tail (toBehavioral (.commit x who R k) σ) =
      toBehavioral k (tail σ) := by
  funext i
  by_cases h : who = i
  · subst h
    simp [toBehavioral, ProgramBehavioralProfile.tail, ProgramBehavioralStrategy.tailOwn]
  · simp [toBehavioral, ProgramBehavioralProfile.tail, h]

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

/-- Lifting a legal pure profile through `toBehavioral` yields a legal
behavioral profile. -/
theorem toBehavioral_IsLegal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
    (σ : ProgramPureProfile p) →
    σ.IsLegal →
    (ProgramPureProfile.toBehavioral p σ).IsLegal
  | _, .ret _, _, _ => fun _ => trivial
  | _, .letExpr _ _ k, σ, hσ =>
      toBehavioral_IsLegal k σ hσ
  | _, .sample _ _ k, σ, hσ =>
      toBehavioral_IsLegal k σ hσ
  | _, .reveal _ _ _ _ k, σ, hσ =>
      toBehavioral_IsLegal k σ hσ
  | _, .commit x who_c (b := b) R k, σ, hσ => by
      have htail : (ProgramPureProfile.tail σ).IsLegal := by
        intro j
        by_cases hj : who_c = j
        · subst hj
          have hσ_who : (σ who_c).IsLegal (.commit x who_c R k) := hσ who_c
          dsimp [ProgramPureStrategy.IsLegal] at hσ_who
          dsimp [ProgramPureProfile.tail]
          split at hσ_who
          · rename_i h
            split
            · rename_i h2
              exact hσ_who.2
            · exact absurd rfl ‹_›
          · exact absurd rfl ‹_›
        · have hσ_j : (σ j).IsLegal (.commit x who_c R k) := hσ j
          dsimp [ProgramPureStrategy.IsLegal] at hσ_j
          dsimp [ProgramPureProfile.tail]
          split at hσ_j
          · rename_i h
            exact absurd h hj
          · split
            · rename_i h2
              exact absurd h2 hj
            · exact hσ_j
      intro i
      by_cases hi : who_c = i
      · subst hi
        have hσ_who : (σ who_c).IsLegal (.commit x who_c R k) := hσ who_c
        dsimp [ProgramPureProfile.toBehavioral, ProgramPureStrategy.IsLegal,
          ProgramBehavioralStrategy.IsLegal] at hσ_who ⊢
        split at hσ_who
        · rename_i h_owner_eq
          split
          · rename_i h_owner_eq2
            refine ⟨?_, ?_⟩
            · intro ρ
              simp only [cast_cast, cast_eq, ProgramBehavioralKernel.run_ofPure,
                FDist.Supported_pure]
              exact hσ_who.1 ρ
            · have hrec := toBehavioral_IsLegal k _ htail who_c
              simpa using hrec
          · exact absurd rfl ‹_›
        · exact absurd rfl ‹_›
      · dsimp [ProgramPureProfile.toBehavioral, ProgramBehavioralStrategy.IsLegal]
        split
        · rename_i h_who_c_eq_i
          exact absurd h_who_c_eq_i hi
        · have hrec := toBehavioral_IsLegal k _ htail i
          simpa using hrec

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

/-- Lift a legal pure profile to a legal behavioral profile. -/
noncomputable def LegalProgramPureProfile.toBehavioral
    {g : WFProgram P L} (σ : LegalProgramPureProfile g) :
    LegalProgramBehavioralProfile g :=
  let rawPure : ProgramPureProfile g.prog := fun i => (σ i).val
  let rawPureLegal : ProgramPureProfile.IsLegal rawPure := fun i => (σ i).2
  let rawBeh : ProgramBehavioralProfile g.prog :=
    ProgramPureProfile.toBehavioral g.prog rawPure
  let rawBehLegal : ProgramBehavioralProfile.IsLegal rawBeh :=
    ProgramPureProfile.toBehavioral_IsLegal g.prog rawPure rawPureLegal
  fun i => ⟨rawBeh i, rawBehLegal i⟩

/-- Lift a legal pure profile to a legal PMF behavioral profile. -/
noncomputable def LegalProgramPureProfile.toBehavioralPMF
    {g : WFProgram P L} (σ : LegalProgramPureProfile g) :
    SyntaxLegalProgramBehavioralProfilePMF g :=
  let rawPure : ProgramPureProfile g.prog := fun i => (σ i).val
  let rawPureLegal : ProgramPureProfile.IsLegal rawPure := fun i => (σ i).2
  let rawBeh : ProgramBehavioralProfilePMF g.prog :=
    ProgramPureProfile.toBehavioralPMF g.prog rawPure
  let rawBehLegal : ProgramBehavioralProfilePMF.IsLegal rawBeh :=
    ProgramPureProfile.toBehavioralPMF_IsLegal g.prog rawPure rawPureLegal
  fun i => ⟨rawBeh i, rawBehLegal i⟩

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

@[simp] theorem ProgramBehavioralKernelPMF.ofFDist_ofPure
    {who : P} {Γ : VCtx P L} {b : L.Ty}
    (κ : PureKernel who Γ b) :
    ProgramBehavioralKernelPMF.ofFDist
        (ProgramBehavioralKernel.ofPure κ) =
      ProgramBehavioralKernelPMF.ofPure κ := by
  ext view
  simp [ProgramBehavioralKernelPMF.ofFDist, ProgramBehavioralKernelPMF.ofPure,
    ProgramBehavioralKernel.ofPure, FDist.toPMF_pure]

namespace ProgramBehavioralProfile

/-- Converting the deterministic behavioral lift of a pure profile to PMF is
the same PMF profile as the direct pure-to-PMF lift. -/
theorem toPMFProfile_toBehavioral_eq_toBehavioralPMF :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (σ : ProgramPureProfile p) →
      toPMFProfile p (ProgramPureProfile.toBehavioral p σ) =
        ProgramPureProfile.toBehavioralPMF p σ
  | _, .ret _, σ => by
      funext who
      rfl
  | _, .letExpr _ _ k, σ => by
      funext who
      simp [toPMFProfile, ProgramPureProfile.toBehavioral,
        ProgramPureProfile.toBehavioralPMF,
        toPMFProfile_toBehavioral_eq_toBehavioralPMF k σ]
  | _, .sample _ _ k, σ => by
      funext who
      simp [toPMFProfile, ProgramPureProfile.toBehavioral,
        ProgramPureProfile.toBehavioralPMF,
        toPMFProfile_toBehavioral_eq_toBehavioralPMF k σ]
  | _, .commit _ who R k, σ => by
      funext i
      by_cases h : who = i
      · subst i
        simp only [toPMFProfile, ProgramPureProfile.toBehavioralPMF, dite_true]
        rw [ProgramPureProfile.tail_toBehavioral]
        simp [ProgramPureProfile.toBehavioral,
          toPMFProfile_toBehavioral_eq_toBehavioralPMF k
            (ProgramPureProfile.tail σ)]
      · simp only [toPMFProfile, ProgramPureProfile.toBehavioralPMF, h, dite_false]
        rw [ProgramPureProfile.tail_toBehavioral]
        simp [
          toPMFProfile_toBehavioral_eq_toBehavioralPMF k
            (ProgramPureProfile.tail σ)]
  | _, .reveal _ _ _ _ k, σ => by
      funext who
      simp [toPMFProfile, ProgramPureProfile.toBehavioral,
        ProgramPureProfile.toBehavioralPMF,
        toPMFProfile_toBehavioral_eq_toBehavioralPMF k σ]

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
    SyntaxLegalProgramBehavioralProfilePMF g :=
  let raw : ProgramBehavioralProfile g.prog := fun i => (σ i).val
  let hraw : raw.IsLegal := fun i => (σ i).2
  fun i =>
    ⟨ProgramBehavioralProfile.toPMFProfile g.prog raw i,
      ProgramBehavioralProfile.toPMFProfile_isLegal g.prog hraw i⟩

end LegalProgramBehavioralProfile

end Vegas
