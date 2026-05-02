import Vegas.SmallStep.Defs
import Vegas.TraceSemantics

/-!
# Agreement for raw small-step semantics
-/

namespace Vegas
namespace SmallStep

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Project an existing complete `Trace` to the raw small-step labels it
realizes. Deterministic `letExpr` and `reveal` nodes become `tau`. -/
def traceLabels :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) → Trace Γ p → List (Label P L)
  | _, .ret _, .ret => []
  | _, .letExpr _ _ k, .letExpr t =>
      Label.tau :: traceLabels k t
  | _, .sample _ (b := b) _ k, .sample v t =>
      Label.sample b v :: traceLabels k t
  | _, .commit _ who (b := b) _ k, .commit v t =>
      Label.commit who b v :: traceLabels k t
  | _, .reveal _ _ _ _ k, .reveal t =>
      Label.tau :: traceLabels k t

/-- Complete-run distribution over raw small-step labels, defined
structurally from the same choices as `Step`. -/
noncomputable def labelDistCore (σ : OmniscientOperationalProfile P L) :
    {Γ : VCtx P L} → VegasCore P L Γ → VEnv L Γ → FDist (List (Label P L))
  | _, .ret _, _ =>
      FDist.pure []
  | _, .letExpr x e k, env =>
      (labelDistCore σ k
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env)).map
        (fun labels => Label.tau :: labels)
  | _, .sample x (b := b) D k, env =>
      FDist.bind (L.evalDist D (VEnv.eraseSampleEnv env)) fun v =>
        (labelDistCore σ k
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub b)
            v env)).map
          (fun labels => Label.sample b v :: labels)
  | _, .commit x who (b := b) R k, env =>
      FDist.bind (σ.commit who x R (VEnv.eraseEnv env)) fun v =>
        (labelDistCore σ k
          (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who b) v env)).map
          (fun labels => Label.commit who b v :: labels)
  | _, .reveal y _who _x (b := b) hx k, env =>
      (labelDistCore σ k
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
          (show L.Val b from
            VEnv.get (Player := P) (L := L) (x := _x)
              (τ := .hidden _who b) env hx) env)).map
        (fun labels => Label.tau :: labels)

/-- Complete-run label distribution over a packaged world. -/
noncomputable def labelDist
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    FDist (List (Label P L)) :=
  labelDistCore σ w.prog w.env

/-- The raw small-step evaluator is the existing denotational semantics,
repackaged over `World`. -/
theorem runSmallStep_eq_outcomeDist
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    runSmallStep σ w = outcomeDist σ w.prog w.env := by
  rfl

/-- Initial checked-program form of `runSmallStep_eq_outcomeDist`. -/
theorem runInitialSmallStep_eq_outcomeDist
    (σ : OmniscientOperationalProfile P L) (g : WFProgram P L) :
    runInitialSmallStep σ g = outcomeDist σ g.prog g.env := by
  exact runSmallStep_eq_outcomeDist σ (World.initial g)

/-- The raw evaluator is characterized by one probabilistic `Step` followed by
recursive evaluation of the target world. This makes the `Step` relation, not
just the structural recursion, semantically central. -/
theorem step_bind_runSmallStep
    {σ : OmniscientOperationalProfile P L} {w : World P L}
    {d : FDist (Label P L × World P L)}
    (hstep : Step σ w d) :
    d.bind (fun lw => runSmallStep σ lw.2) = runSmallStep σ w := by
  cases hstep with
  | letExpr env =>
      rw [FDist.pure_bind]
      rfl
  | sample env =>
      rw [FDist.bind_assoc]
      congr
      funext v
      rw [FDist.pure_bind]
      rfl
  | commit env =>
      rw [FDist.bind_assoc]
      congr
      funext v
      rw [FDist.pure_bind]
      rfl
  | reveal env =>
      rw [FDist.pure_bind]
      rfl

/-- The structurally defined label distribution is the projection of the
existing trace distribution through `traceLabels`. -/
theorem labelDistCore_eq_traceDist_map_traceLabels
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ) :
    labelDistCore σ p env = (traceDist σ p env).map (traceLabels p) := by
  induction p with
  | ret payoffs =>
      rw [labelDistCore, traceDist, FDist.map_pure]
      rfl
  | letExpr x e k ih =>
      simp only [labelDistCore, traceDist]
      rw [ih, FDist.map_map, FDist.map_map]
      rfl
  | sample x D k ih =>
      simp only [labelDistCore, traceDist]
      rw [FDist.bind_map]
      congr 1
      funext v
      rw [ih, FDist.map_map, FDist.map_map]
      rfl
  | commit x who R k ih =>
      simp only [labelDistCore, traceDist]
      rw [FDist.bind_map]
      congr 1
      funext v
      rw [ih, FDist.map_map, FDist.map_map]
      rfl
  | reveal y who x hx k ih =>
      simp only [labelDistCore, traceDist]
      rw [ih, FDist.map_map, FDist.map_map]
      rfl

/-- Packaged-world form of `labelDistCore_eq_traceDist_map_traceLabels`. -/
theorem labelDist_eq_traceDist_map_traceLabels
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    labelDist σ w = (traceDist σ w.prog w.env).map (traceLabels w.prog) := by
  exact labelDistCore_eq_traceDist_map_traceLabels σ w.prog w.env

/-- Support form of the label/trace bridge: a label list has positive mass
exactly when it is the projection of some positive-weight existing `Trace`. -/
theorem mem_support_labelDistCore_iff_exists_trace
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    (labels : List (Label P L)) :
    labels ∈ (labelDistCore σ p env).support ↔
      ∃ t : Trace Γ p,
        t ∈ (traceDist σ p env).support ∧ traceLabels p t = labels := by
  rw [labelDistCore_eq_traceDist_map_traceLabels, FDist.mem_support_map]

/-- Packaged-world support form of the label/trace bridge. -/
theorem mem_support_labelDist_iff_exists_trace
    (σ : OmniscientOperationalProfile P L) (w : World P L)
    (labels : List (Label P L)) :
    labels ∈ (labelDist σ w).support ↔
      ∃ t : Trace w.Γ w.prog,
        t ∈ (traceDist σ w.prog w.env).support ∧
          traceLabels w.prog t = labels := by
  exact mem_support_labelDistCore_iff_exists_trace σ w.prog w.env labels

/-- Under an admissible profile, every positive-mass label run has a legal
trace witness. -/
theorem exists_legal_trace_of_mem_support_labelDistCore
    {σ : OmniscientOperationalProfile P L}
    {Γ : VCtx P L} {p : VegasCore P L Γ} {env : VEnv L Γ}
    (hadm : FairPlayProfile σ p) {labels : List (Label P L)}
    (hlabels : labels ∈ (labelDistCore σ p env).support) :
    ∃ t : Trace Γ p,
      t.legal p env ∧
        t ∈ (traceDist σ p env).support ∧
          traceLabels p t = labels := by
  obtain ⟨t, ht, hproj⟩ :=
    (mem_support_labelDistCore_iff_exists_trace σ p env labels).1 hlabels
  have hweight : traceWeight σ p env t ≠ 0 := by
    have hmass := Finsupp.mem_support_iff.mp ht
    simpa [traceDist_apply] using hmass
  exact ⟨t, admissible_pos_weight_legal hadm t hweight, ht, hproj⟩

/-- Packaged-world admissibility corollary for positive-mass label runs. -/
theorem exists_legal_trace_of_mem_support_labelDist
    {σ : OmniscientOperationalProfile P L} {w : World P L}
    (hadm : FairPlayProfile σ w.prog) {labels : List (Label P L)}
    (hlabels : labels ∈ (labelDist σ w).support) :
    ∃ t : Trace w.Γ w.prog,
      t.legal w.prog w.env ∧
        t ∈ (traceDist σ w.prog w.env).support ∧
          traceLabels w.prog t = labels := by
  exact exists_legal_trace_of_mem_support_labelDistCore
    (p := w.prog) (env := w.env) hadm hlabels

end SmallStep
end Vegas
