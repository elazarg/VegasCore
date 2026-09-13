/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SourceExecutionLaw
import Vegas.Compile.SourceExecutionOutcome
import Vegas.Compile.SourceBacktranslation

/-! # Whole-program source and graph policy laws

These laws concern the compiled graph's actual declared-read kernel execution.
Its terminal state decodes to the independently defined written-order source
denotation. Every graph kernel has a playerwise source backtranslation. Later
message runtimes must justify the additional observations and actions they
provide; no message-policy backtranslation is assumed or supplied here.
-/

noncomputable section

namespace Vegas.ToEventGraph

open EventGraph GameTheory GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] [Fintype P] {L : IExpr}

/-- Compiled source policies preserve the full terminal source-environment law.
The `some` on the right also certifies termination, without assigning a source
outcome to any unfinished graph execution. -/
theorem runPolicyNodes_compileSourcePolicy_source
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : SourceBehavioralProfile program.prog) :
    (runPolicyNodes (compile program).graphWF (compile_guardLive program legal)
      (fun who => compileSourcePolicy program.prog program.fresh
        (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
        rfl who (profile who))
      ⟨Config.initial (compile program).graph, .initial⟩
      (compile program).graph.nodeOrder).map (observeSourceOutcome program) =
        (denoteSource program.prog profile program.env).map some := by
  have hgraph := runPolicyNodes_observeSourceOutcome_eq_coupled program
    (fun who => compileSourcePolicy program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
      rfl who (profile who)) (compile_guardLive program legal)
  have hsource := congrArg (FinDist.map some)
    (runCoupledSource_compileSourcePolicy_source program.prog program.fresh
      (BuildState.fromInitial (initialState program.Γ program.env program.wctx)) rfl
      (compile_guardLive program legal) profile (compiledInitialCoupled program))
  exact hgraph.trans (by
    simpa only [FinDist.map_comp, Function.comp_def, compiledInitialCoupled,
      initialCoupledAt, id_eq] using hsource)

/-- Every declared-read graph profile has the law of its playerwise source
backtranslation. The profile need not have been supplied by compilation. -/
theorem runPolicyNodes_backtranslate_source
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : CommitPolicyProfile (compile program).graph) :
    (runPolicyNodes (compile program).graphWF (compile_guardLive program legal) profile
      ⟨Config.initial (compile program).graph, .initial⟩
      (compile program).graph.nodeOrder).map (observeSourceOutcome program) =
        (denoteSource program.prog
          (fun who => backtranslateCommitPolicy program who (profile who)) program.env).map
            some := by
  have hlaw := runPolicyNodes_compileSourcePolicy_source program legal
    (fun who => backtranslateCommitPolicy program who (profile who))
  simpa only [compile_backtranslateCommitPolicy] using hlaw

/-- A unilateral graph-kernel replacement is exactly one source replacement;
the source policies of every opponent are unchanged. -/
theorem runPolicyNodes_source_deviation
    (program : GraphProgram P L) (legal : Legal program.prog)
    (profile : SourceBehavioralProfile program.prog) (who : P)
    (replacement : CommitPolicy (compile program).graph who) :
    (runPolicyNodes (compile program).graphWF (compile_guardLive program legal)
      (Profile.update (sig := ⟨CommitPolicy (compile program).graph,
        ReachableConfig (compile program).graph⟩)
        (fun player => compileSourcePolicy program.prog program.fresh
          (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
          rfl player (profile player)) who replacement)
      ⟨Config.initial (compile program).graph, .initial⟩
      (compile program).graph.nodeOrder).map (observeSourceOutcome program) =
        (denoteSource program.prog
          (Profile.update (sig := sourceGameSignature program.prog) profile who
            (backtranslateCommitPolicy program who replacement)) program.env).map some := by
  have hprofile :
      (fun player => compileSourcePolicy program.prog program.fresh
        (BuildState.fromInitial (initialState program.Γ program.env program.wctx)) rfl player
        (Profile.update (sig := sourceGameSignature program.prog) profile who
          (backtranslateCommitPolicy program who replacement) player)) =
      Profile.update (sig := ⟨CommitPolicy (compile program).graph,
        ReachableConfig (compile program).graph⟩)
        (fun player => compileSourcePolicy program.prog program.fresh
          (BuildState.fromInitial (initialState program.Γ program.env program.wctx))
          rfl player (profile player)) who replacement := by
    funext player
    by_cases h : player = who
    · subst player
      simp only [Profile.update_same, compile_backtranslateCommitPolicy]
    · simp only [Profile.update_of_ne _ _ h]
  rw [← hprofile]
  exact runPolicyNodes_compileSourcePolicy_source program legal _

end Vegas.ToEventGraph
