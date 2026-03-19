import Vegas.TraceSemantics

/-!
# Trace-facing corollaries for Vegas

Paper-friendly consequences of the core trace semantics.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Profile-dependent reachability has a witnessing positive-weight trace. -/
theorem reach_has_pos_weight_trace {Γ : VCtx P L} {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {oc : Outcome P}
    (σ : Profile P L) (h : Reach σ p env oc) :
    ∃ t : Trace Γ p, traceOutcome p env t = oc ∧ traceWeight σ p env t ≠ 0 := by
  induction h with
  | ret =>
      exact ⟨.ret, rfl, by simp [traceWeight]⟩
  | letExpr _ ih =>
      obtain ⟨t, ho, hw⟩ := ih
      refine ⟨.letExpr t, ?_, ?_⟩
      · simpa [traceOutcome] using ho
      · simpa [traceWeight] using hw
  | sample v hsupp _ ih =>
      obtain ⟨t, ho, hw⟩ := ih
      have hv := Finsupp.mem_support_iff.mp hsupp
      refine ⟨.sample v t, ?_, ?_⟩
      · simpa [traceOutcome] using ho
      · simpa [traceWeight] using mul_ne_zero hv hw
  | commit v hsupp _ ih =>
      obtain ⟨t, ho, hw⟩ := ih
      have hv := Finsupp.mem_support_iff.mp hsupp
      refine ⟨.commit v t, ?_, ?_⟩
      · simpa [traceOutcome] using ho
      · simpa [traceWeight] using mul_ne_zero hv hw
  | reveal _ ih =>
      obtain ⟨t, ho, hw⟩ := ih
      refine ⟨.reveal t, ?_, ?_⟩
      · simpa [traceOutcome] using ho
      · simpa [traceWeight] using hw

/-- Profile-free reachability is exactly existence of a legal trace. -/
theorem canReach_iff_exists_legal_trace {Γ : VCtx P L} {p : VegasCore P L Γ}
    {env : VEnv (Player := P) L Γ} {oc : Outcome P} :
    CanReach p env oc ↔
      ∃ t : Trace Γ p, t.legal p env ∧ traceOutcome p env t = oc := by
  constructor
  · exact canReach_has_trace
  · rintro ⟨t, hlegal, hout⟩
    simpa [hout] using legal_trace_canReach (p := p) (env := env) t hlegal

/-- The denotational semantics is extensionally equal to the trace-weight sum. -/
theorem outcomeDist_eq_traceWeightSum {Γ : VCtx P L} (σ : Profile P L)
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ) :
    outcomeDist σ p env = traceWeightSum σ p env := by
  funext oc
  exact adequacy_pointwise σ p env oc

/-- An outcome is in the denotational support iff it is realized by some
positive-weight trace. -/
theorem mem_support_outcomeDist_iff_exists_pos_weight_trace
    {Γ : VCtx P L} (σ : Profile P L)
    (p : VegasCore P L Γ) (env : VEnv (Player := P) L Γ) (oc : Outcome P) :
    oc ∈ (outcomeDist σ p env).support ↔
      ∃ t : Trace Γ p, traceOutcome p env t = oc ∧ traceWeight σ p env t ≠ 0 := by
  constructor
  · intro hsupp
    exact reach_has_pos_weight_trace σ
      ((reach_iff_outcomeDist_support σ p env oc).2 hsupp)
  · rintro ⟨t, hout, hwt⟩
    have hreach : Reach σ p env (traceOutcome p env t) :=
      pos_weight_trace_reach (p := p) (env := env) σ t hwt
    simpa [hout] using
      (reach_iff_outcomeDist_support σ p env (traceOutcome p env t)).1 hreach

end Vegas
