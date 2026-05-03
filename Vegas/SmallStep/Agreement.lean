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

/-! ## Finite terminal-path enumeration -/

/-- Finite weighted enumeration of complete raw small-step paths.

Each support element is a pair `(labels, dst)` where `labels` is the full
small-step label sequence and `dst` is the terminal destination world. The
`FDist` mass of that pair is the product of the one-step masses along the
path. This is the finite carrier needed for "sum over terminal paths"
statements; the qualitative `Steps` relation is connected to its support
below. -/
noncomputable def terminalPathDistCore (σ : OmniscientOperationalProfile P L) :
    {Γ : VCtx P L} → VegasCore P L Γ → VEnv L Γ →
      FDist (List (Label P L) × World P L)
  | _, .ret payoffs, env =>
      FDist.pure
        ([],
          ({ Γ := _, prog := .ret payoffs, env := env } : World P L))
  | _, .letExpr x e k, env =>
      (terminalPathDistCore σ k
        (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
          (L.eval e (VEnv.erasePubEnv env)) env)).map
        (fun path => (Label.tau :: path.1, path.2))
  | _, .sample x (b := b) D k, env =>
      FDist.bind (L.evalDist D (VEnv.eraseSampleEnv env)) fun v =>
        (terminalPathDistCore σ k
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub b)
            v env)).map
          (fun path => (Label.sample b v :: path.1, path.2))
  | _, .commit x who (b := b) R k, env =>
      FDist.bind (σ.commit who x R (VEnv.eraseEnv env)) fun v =>
        (terminalPathDistCore σ k
          (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who b) v env)).map
          (fun path => (Label.commit who b v :: path.1, path.2))
  | _, .reveal y _who _x (b := b) hx k, env =>
      (terminalPathDistCore σ k
        (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
          (show L.Val b from
            VEnv.get (Player := P) (L := L) (x := _x)
              (τ := .hidden _who b) env hx) env)).map
        (fun path => (Label.tau :: path.1, path.2))

/-- Finite weighted enumeration of terminal raw small-step paths from a
packaged world. -/
noncomputable def terminalPathDist
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    FDist (List (Label P L) × World P L) :=
  terminalPathDistCore σ w.prog w.env

/-- Projecting the finite terminal-path enumeration to labels recovers
`labelDistCore`. -/
theorem terminalPathDistCore_map_labels_eq_labelDistCore
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ) :
    (terminalPathDistCore σ p env).map
        (fun path : List (Label P L) × World P L => path.1) =
      labelDistCore σ p env := by
  induction p with
  | ret payoffs =>
      rw [terminalPathDistCore, labelDistCore, FDist.map_pure]
  | letExpr x e k ih =>
      simp only [terminalPathDistCore, labelDistCore]
      rw [FDist.map_map]
      rw [← ih]
      rw [FDist.map_map]
      rfl
  | sample x D k ih =>
      simp only [terminalPathDistCore, labelDistCore]
      rw [FDist.bind_map]
      congr 1
      funext v
      rw [FDist.map_map]
      rw [← ih]
      rw [FDist.map_map]
      rfl
  | commit x who R k ih =>
      simp only [terminalPathDistCore, labelDistCore]
      rw [FDist.bind_map]
      congr 1
      funext v
      rw [FDist.map_map]
      rw [← ih]
      rw [FDist.map_map]
      rfl
  | reveal y who x hx k ih =>
      simp only [terminalPathDistCore, labelDistCore]
      rw [FDist.map_map]
      rw [← ih]
      rw [FDist.map_map]
      rfl

/-- Projecting the finite terminal-path enumeration to labels recovers
`labelDist`. -/
theorem terminalPathDist_map_labels_eq_labelDist
    (σ : OmniscientOperationalProfile P L) (w : World P L) :
    (terminalPathDist σ w).map
        (fun path : List (Label P L) × World P L => path.1) =
      labelDist σ w := by
  exact terminalPathDistCore_map_labels_eq_labelDistCore σ w.prog w.env

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

/-- Pointwise weight form of `labelDistCore_eq_traceDist_map_traceLabels`.

The mass assigned to a label list is the sum of the weights of all complete
traces that project to that label list. The qualitative `Steps` relation below
records positive-support reachability; this theorem is the current
weight-carrying statement. -/
theorem labelDistCore_apply_eq_traceLabel_sum
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    (labels : List (Label P L)) :
    (labelDistCore σ p env) labels =
      (traceDist σ p env).support.sum
        (fun t =>
          if traceLabels p t = labels then
            traceWeight σ p env t
          else
            0) := by
  rw [labelDistCore_eq_traceDist_map_traceLabels, FDist.map_apply]
  apply Finset.sum_congr rfl
  intro t _ht
  by_cases h : traceLabels p t = labels
  · simp [h, traceDist_apply]
  · simp [h]

/-- Packaged-world form of `labelDistCore_apply_eq_traceLabel_sum`. -/
theorem labelDist_apply_eq_traceLabel_sum
    (σ : OmniscientOperationalProfile P L) (w : World P L)
    (labels : List (Label P L)) :
    (labelDist σ w) labels =
      (traceDist σ w.prog w.env).support.sum
        (fun t =>
          if traceLabels w.prog t = labels then
            traceWeight σ w.prog w.env t
          else
            0) := by
  exact labelDistCore_apply_eq_traceLabel_sum σ w.prog w.env labels

/-- Pointwise weight form using the finite terminal-path enumeration.

The mass `labelDistCore σ p env labels` is the sum of the masses of all
enumerated terminal paths whose label projection is `labels`. The summation
domain is the finite support of `terminalPathDistCore`. -/
theorem labelDistCore_apply_eq_terminalPath_sum
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    (labels : List (Label P L)) :
    (labelDistCore σ p env) labels =
      (terminalPathDistCore σ p env).support.sum
        (fun path =>
          if path.1 = labels then
            (terminalPathDistCore σ p env) path
          else
            0) := by
  rw [← terminalPathDistCore_map_labels_eq_labelDistCore σ p env]
  rw [FDist.map_apply]

/-- Packaged-world form of `labelDistCore_apply_eq_terminalPath_sum`. -/
theorem labelDist_apply_eq_terminalPath_sum
    (σ : OmniscientOperationalProfile P L) (w : World P L)
    (labels : List (Label P L)) :
    (labelDist σ w) labels =
      (terminalPathDist σ w).support.sum
        (fun path =>
          if path.1 = labels then
            (terminalPathDist σ w) path
          else
            0) := by
  exact labelDistCore_apply_eq_terminalPath_sum σ w.prog w.env labels

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

/-- Every support point of the finite terminal-path enumeration is terminal
and has a qualitative `Steps` witness. -/
theorem terminalPathDistCore_support_terminal_steps
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    {path : List (Label P L) × World P L}
    (hpath : path ∈ (terminalPathDistCore σ p env).support) :
    terminal path.2 ∧
      Steps σ ({ Γ := Γ, prog := p, env := env } : World P L)
        path.1 path.2 := by
  induction p generalizing path with
  | ret payoffs =>
      rw [terminalPathDistCore, FDist.mem_support_pure] at hpath
      cases hpath
      exact ⟨by simp [terminal], Steps.nil _⟩
  | letExpr x e k ih =>
      rw [terminalPathDistCore, FDist.mem_support_map] at hpath
      rcases hpath with ⟨tailPath, htail, hproj⟩
      obtain ⟨hterm, hsteps⟩ :=
        ih
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            (L.eval e (VEnv.erasePubEnv env)) env)
          htail
      let mid : World P L :=
        { Γ := _
          prog := k
          env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            (L.eval e (VEnv.erasePubEnv env)) env }
      have hsupport :
          StepSupport σ
            ({ Γ := _, prog := .letExpr x e k, env := env } : World P L)
            (Label.tau, mid) := by
        refine ⟨_, Step.letExpr (σ := σ) env, ?_⟩
        rw [FDist.mem_support_pure]
      cases hproj
      exact ⟨hterm, Steps.cons hsupport hsteps⟩
  | sample x D k ih =>
      rw [terminalPathDistCore, FDist.mem_support_bind] at hpath
      rcases hpath with ⟨v, hv, htailMap⟩
      rw [FDist.mem_support_map] at htailMap
      rcases htailMap with ⟨tailPath, htail, hproj⟩
      obtain ⟨hterm, hsteps⟩ :=
        ih
          (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            v env)
          htail
      let mid : World P L :=
        { Γ := _
          prog := k
          env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
            v env }
      have hsupport :
          StepSupport σ
            ({ Γ := _, prog := .sample x D k, env := env } : World P L)
            (Label.sample _ v, mid) := by
        refine ⟨_, Step.sample (σ := σ) env, ?_⟩
        rw [FDist.mem_support_bind]
        refine ⟨v, hv, ?_⟩
        rw [FDist.mem_support_pure]
      cases hproj
      exact ⟨hterm, Steps.cons hsupport hsteps⟩
  | commit x who R k ih =>
      rw [terminalPathDistCore, FDist.mem_support_bind] at hpath
      rcases hpath with ⟨v, hv, htailMap⟩
      rw [FDist.mem_support_map] at htailMap
      rcases htailMap with ⟨tailPath, htail, hproj⟩
      obtain ⟨hterm, hsteps⟩ :=
        ih
          (VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who _) v env)
          htail
      let mid : World P L :=
        { Γ := _
          prog := k
          env := VEnv.cons (Player := P) (L := L) (x := x)
            (τ := .hidden who _) v env }
      have hsupport :
          StepSupport σ
            ({ Γ := _, prog := .commit x who R k, env := env } : World P L)
            (Label.commit who _ v, mid) := by
        refine ⟨_, Step.commit (σ := σ) env, ?_⟩
        rw [FDist.mem_support_bind]
        refine ⟨v, hv, ?_⟩
        rw [FDist.mem_support_pure]
      cases hproj
      exact ⟨hterm, Steps.cons hsupport hsteps⟩
  | @reveal Γ y who x b hx k ih =>
      rw [terminalPathDistCore, FDist.mem_support_map] at hpath
      rcases hpath with ⟨tailPath, htail, hproj⟩
      obtain ⟨hterm, hsteps⟩ :=
        ih
          (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
            (show L.Val b from
              VEnv.get (Player := P) (L := L) (x := x)
                (τ := .hidden who b) env hx) env)
          htail
      let mid : World P L :=
        { Γ := _
          prog := k
          env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
            (show L.Val b from
              VEnv.get (Player := P) (L := L) (x := x)
                (τ := .hidden who b) env hx) env }
      have hsupport :
          StepSupport σ
            ({ Γ := _, prog := .reveal y who x hx k, env := env } : World P L)
            (Label.tau, mid) := by
        refine ⟨_, Step.reveal (σ := σ) env, ?_⟩
        rw [FDist.mem_support_pure]
      cases hproj
      exact ⟨hterm, Steps.cons hsupport hsteps⟩

/-- Packaged-world form of
`terminalPathDistCore_support_terminal_steps`. -/
theorem terminalPathDist_support_terminal_steps
    (σ : OmniscientOperationalProfile P L) (w : World P L)
    {path : List (Label P L) × World P L}
    (hpath : path ∈ (terminalPathDist σ w).support) :
    terminal path.2 ∧ Steps σ w path.1 path.2 := by
  exact terminalPathDistCore_support_terminal_steps σ w.prog w.env hpath

/-- Every positive-weight trace induces a terminal qualitative small-step path
with the trace's projected labels.

This theorem connects the pathwise trace presentation to `Steps`. It does not
assign a numeric weight to the `Steps` proof; weights are carried by
`traceWeight` and the pointwise `labelDist` sum theorem above. -/
theorem exists_terminal_steps_of_pos_weight_trace
    (σ : OmniscientOperationalProfile P L)
    {Γ : VCtx P L} (p : VegasCore P L Γ) (env : VEnv L Γ)
    (t : Trace Γ p) (hwt : traceWeight σ p env t ≠ 0) :
    ∃ dst : World P L,
      terminal dst ∧
        Steps σ ({ Γ := Γ, prog := p, env := env } : World P L)
          (traceLabels p t) dst := by
  induction p with
  | ret payoffs =>
      cases t
      exact ⟨{ Γ := _, prog := .ret payoffs, env := env }, by simp [terminal],
        Steps.nil _⟩
  | letExpr x e k ih =>
      cases t with
      | letExpr tTail =>
          obtain ⟨dst, hterm, hsteps⟩ :=
            ih
              (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                (L.eval e (VEnv.erasePubEnv env)) env)
              tTail (by simpa [traceWeight] using hwt)
          let mid : World P L :=
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                (L.eval e (VEnv.erasePubEnv env)) env }
          have hsupport :
              StepSupport σ
                ({ Γ := _, prog := .letExpr x e k, env := env } : World P L)
                (Label.tau, mid) := by
            refine ⟨_, Step.letExpr (σ := σ) env, ?_⟩
            rw [FDist.mem_support_pure]
          exact ⟨dst, hterm, Steps.cons hsupport hsteps⟩
  | sample x D k ih =>
      cases t with
      | sample v tTail =>
          have hmul : (L.evalDist D (VEnv.eraseSampleEnv env)) v *
                traceWeight σ k
                  (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                    v env) tTail ≠ 0 := by
            simpa [traceWeight] using hwt
          have hv_ne :
              (L.evalDist D (VEnv.eraseSampleEnv env)) v ≠ 0 :=
            (mul_ne_zero_iff.mp hmul).1
          have htail_ne :
              traceWeight σ k
                (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                  v env) tTail ≠ 0 :=
            (mul_ne_zero_iff.mp hmul).2
          obtain ⟨dst, hterm, hsteps⟩ :=
            ih
              (VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                v env)
              tTail htail_ne
          let mid : World P L :=
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x) (τ := .pub _)
                v env }
          have hsupport :
              StepSupport σ
                ({ Γ := _, prog := .sample x D k, env := env } : World P L)
                (Label.sample _ v, mid) := by
            refine ⟨_, Step.sample (σ := σ) env, ?_⟩
            rw [FDist.mem_support_bind]
            refine ⟨v, Finsupp.mem_support_iff.mpr hv_ne, ?_⟩
            rw [FDist.mem_support_pure]
          exact ⟨dst, hterm, Steps.cons hsupport hsteps⟩
  | commit x who R k ih =>
      cases t with
      | commit v tTail =>
          have hmul : (σ.commit who x R (VEnv.eraseEnv env)) v *
                traceWeight σ k
                  (VEnv.cons (Player := P) (L := L) (x := x)
                    (τ := .hidden who _) v env) tTail ≠ 0 := by
            simpa [traceWeight] using hwt
          have hv_ne : (σ.commit who x R (VEnv.eraseEnv env)) v ≠ 0 :=
            (mul_ne_zero_iff.mp hmul).1
          have htail_ne :
              traceWeight σ k
                (VEnv.cons (Player := P) (L := L) (x := x)
                  (τ := .hidden who _) v env) tTail ≠ 0 :=
            (mul_ne_zero_iff.mp hmul).2
          obtain ⟨dst, hterm, hsteps⟩ :=
            ih
              (VEnv.cons (Player := P) (L := L) (x := x)
                (τ := .hidden who _) v env)
              tTail htail_ne
          let mid : World P L :=
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := x)
                (τ := .hidden who _) v env }
          have hsupport :
              StepSupport σ
                ({ Γ := _, prog := .commit x who R k, env := env } : World P L)
                (Label.commit who _ v, mid) := by
            refine ⟨_, Step.commit (σ := σ) env, ?_⟩
            rw [FDist.mem_support_bind]
            refine ⟨v, Finsupp.mem_support_iff.mpr hv_ne, ?_⟩
            rw [FDist.mem_support_pure]
          exact ⟨dst, hterm, Steps.cons hsupport hsteps⟩
  | @reveal Γ y who x b hx k ih =>
      cases t with
      | reveal tTail =>
          obtain ⟨dst, hterm, hsteps⟩ :=
            ih
              (VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
                (show L.Val b from
                  VEnv.get (Player := P) (L := L) (x := x)
                    (τ := .hidden who b) env hx) env)
              tTail (by simpa [traceWeight] using hwt)
          let mid : World P L :=
            { Γ := _
              prog := k
              env := VEnv.cons (Player := P) (L := L) (x := y) (τ := .pub b)
                (show L.Val b from
                  VEnv.get (Player := P) (L := L) (x := x)
                    (τ := .hidden who b) env hx) env }
          have hsupport :
              StepSupport σ
                ({ Γ := _, prog := .reveal y who x hx k, env := env } : World P L)
                (Label.tau, mid) := by
            refine ⟨_, Step.reveal (σ := σ) env, ?_⟩
            rw [FDist.mem_support_pure]
          exact ⟨dst, hterm, Steps.cons hsupport hsteps⟩

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
