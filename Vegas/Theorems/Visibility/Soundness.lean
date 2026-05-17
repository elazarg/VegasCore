import Vegas.Core.ViewProjection
import Vegas.Core.ToEventGraph

/-!
# Visibility Soundness Theorems

Project-facing names for the basic information-flow invariants of Vegas.
The source type system makes public computation consume `erasePubVCtx`, while
the scoping judgment makes commit guards local to the acting player's view.
-/

namespace Vegas

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Payoff evaluation depends only on the public erasure of the terminal
environment. Hidden values can affect payoffs only after they have been
revealed into public state. -/
theorem evalPayoffs_eq_of_erasePubEnv_eq
    {Γ : VCtx P L}
    {payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)}
    {left right : VEnv L Γ}
    (hpub : VEnv.erasePubEnv left = VEnv.erasePubEnv right) :
    evalPayoffs payoffs left = evalPayoffs payoffs right := by
  unfold evalPayoffs
  rw [hpub]

/-- Sample distributions are evaluated on the public erasure of the current
environment. There is no private-sample primitive in the current core
language. -/
theorem sample_distribution_env_eq_public_env
    {P : Type} {L : IExpr} {Γ : VCtx P L} (env : VEnv L Γ) :
    VEnv.eraseSampleEnv env = VEnv.erasePubEnv env := rfl

/-- The sample typing context is definitionally the public context. -/
theorem sample_context_eq_public_context
    {P : Type} {L : IExpr} (Γ : VCtx P L) :
    sampleVCtx Γ = pubVCtx Γ := rfl

/-- Commit-guard evaluation is invariant under changes outside the committing
player's observation, provided the guard satisfies the Vegas scoping judgment. -/
theorem commitGuard_eval_eq_of_observation_eq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hfresh : Fresh x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {left right : Env L.Val (eraseVCtx Γ)}
    (hobs : ObsEq (L := L) (Γ := Γ) who left right) :
    evalGuard (Player := P) (L := L) R a left =
      evalGuard (Player := P) (L := L) R a right :=
  evalGuard_eq_of_obsEq hfresh hR hobs

/-- Equality of projected player views is enough to preserve commit-guard
evaluation. This is the view-kernel form of guard locality. -/
theorem commitGuard_eval_eq_of_projectView_eq
    {Γ : VCtx P L} {x : VarId} {who : P} {b : L.Ty}
    {R : L.Expr ((x, b) :: eraseVCtx Γ) L.bool}
    (hctx : WFCtx (L := L) Γ)
    (hfresh : Fresh x Γ)
    (hR : GuardUsesOnly (L := L) (Γ := Γ) (x := x) (who := who) R)
    {a : L.Val b}
    {left right : Env L.Val (eraseVCtx Γ)}
    (hview : projectViewEnv who left = projectViewEnv who right) :
    evalGuard (Player := P) (L := L) R a left =
    evalGuard (Player := P) (L := L) R a right :=
  evalGuard_eq_of_projectViewEnv_eq hctx hfresh hR hview

@[simp] theorem ProgramField.singlePatch_ne
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    {field other : ProgramField p}
    (value : L.Val field.ty)
    (h : other ≠ field) :
    ProgramField.singlePatch field value other = none := by
  simp [ProgramField.singlePatch, h]

private theorem ProgramNode.commit_target_owner_of_sem :
    {Γ : VCtx P L} → {p : VegasCore P L Γ} →
      (obs : ProgramNode.ProgramObligations p) →
      (node : ProgramNode p) →
      {commitWho : P} → {target : ProgramField p} →
      {guard : EventGraph.EventGuard L (ProgramField p)
        (fun field => field.ty) target} →
      ProgramNode.sem obs node =
        EventGraph.NodeSem.commit commitWho target guard →
      target.owner = some commitWho
  | _, .letExpr x e k, obs, .letHere, _, _, _, hsem => by
      simp [ProgramNode.sem] at hsem
  | _, .letExpr x e k, obs, .letTail node, commitWho, target, guard, hsem => by
      cases hinner : ProgramNode.sem obs.letTail node with
      | assign field expr =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.letTail innerTarget)
                  (innerGuard.mapFields ProgramField.letTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields]
              using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          simpa [ProgramField.owner] using
            ProgramNode.commit_target_owner_of_sem obs.letTail node hinner
  | _, .sample x D k, obs, .sampleHere, _, _, _, hsem => by
      simp [ProgramNode.sem] at hsem
  | _, .sample x D k, obs, .sampleTail node, commitWho, target, guard, hsem => by
      cases hinner : ProgramNode.sem obs.sampleTail node with
      | assign field expr =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.sampleTail innerTarget)
                  (innerGuard.mapFields ProgramField.sampleTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields]
              using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          simpa [ProgramField.owner] using
            ProgramNode.commit_target_owner_of_sem obs.sampleTail node hinner
  | _, .commit x who (b := b) R k, obs, .commitHere, commitWho, target, guard, hsem => by
      change
        EventGraph.NodeSem.commit who
            (ProgramField.writtenBy
              (.commitHere (x := x) (who := who) (R := R) (k := k)))
            _ =
          EventGraph.NodeSem.commit commitWho target guard at hsem
      injection hsem with howner htarget hguard
      subst commitWho
      subst target
      change
        (ProgramField.ofCurrent k
          (VCtxField.mk (x := x) (τ := .hidden who b) VHasVar.here)).owner =
            some who
      simp [ProgramField.owner_ofCurrent, VCtxField.owner, VCtxField.bindTy]
  | _, .commit x who R k, obs, .commitTail node, commitWho, target, guard, hsem => by
      cases hinner : ProgramNode.sem obs.commitTail node with
      | assign field expr =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.commitTail innerTarget)
                  (innerGuard.mapFields ProgramField.commitTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields]
              using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          simpa [ProgramField.owner] using
            ProgramNode.commit_target_owner_of_sem obs.commitTail node hinner
  | _, .reveal y who x hx k, obs, .revealHere, _, _, _, hsem => by
      simp [ProgramNode.sem] at hsem
  | _, .reveal y who x hx k, obs, .revealTail node, commitWho, target, guard, hsem => by
      cases hinner : ProgramNode.sem obs.revealTail node with
      | assign field expr =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | sample field dist =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | reveal source innerTarget hty =>
          simp [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields] at hsem
      | commit owner innerTarget innerGuard =>
          have hsem' :
              EventGraph.NodeSem.commit owner (.revealTail innerTarget)
                  (innerGuard.mapFields ProgramField.revealTail
                    (fun _ => rfl)) =
                EventGraph.NodeSem.commit commitWho target guard := by
            simpa [ProgramNode.sem, hinner, EventGraph.NodeSem.mapFields]
              using hsem
          injection hsem' with howner htarget hguard
          subst commitWho
          subst target
          cases hguard
          simpa [ProgramField.owner] using
            ProgramNode.commit_target_owner_of_sem obs.revealTail node hinner

private theorem ProgramNode.writer?_ne_of_ne_commit_target
    {Γ : VCtx P L} {p : VegasCore P L Γ}
    (obs : ProgramNode.ProgramObligations p)
    (node : ProgramNode p)
    {owner : P} {field candidate : ProgramField p}
    {guard : EventGraph.EventGuard L (ProgramField p)
      (fun field => field.ty) field}
    (hsem :
      ProgramNode.sem obs node =
        EventGraph.NodeSem.commit owner field guard)
    (hne : candidate ≠ field) :
    ProgramField.writer? candidate ≠ some node := by
  intro hwriter
  have hcandidateSource : ProgramField.source candidate = Sum.inr node := by
    unfold ProgramField.writer? at hwriter
    cases hsource : ProgramField.source candidate with
    | inl current =>
        simp [hsource] at hwriter
    | inr writer =>
        simp [hsource] at hwriter
        subst node
        rfl
  have hcandidateEq : candidate = ProgramField.writtenBy node :=
    ProgramField.eq_writtenBy_of_source_eq_inr hcandidateSource
  have hfieldWrite :
      field ∈ (ProgramNode.sem obs node).writeFields := by
    rw [hsem]
    simp [EventGraph.NodeSem.writeFields, EventGraph.NodeSem.writes,
      EventGraph.FieldWrite.field]
  have hfieldEq : field = ProgramField.writtenBy node :=
    ProgramNode.eq_writtenBy_of_mem_writeFields obs node hfieldWrite
  exact hne (hcandidateEq.trans hfieldEq.symm)

/-! ## Syntax-Graph Visibility -/

/-- Hidden commit payload changes do not alter public observation, beyond the
public fact that the commit node has completed. -/
theorem eventGraph_hiddenCommit_publicView_eq_of_payload_eq_except_hidden
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {owner : P} {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {leftPatch rightPatch : ProgramField.FieldPatch g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (hsem :
      ProgramNode.sem g.obligations node =
        EventGraph.NodeSem.commit owner field guard)
    (hleftLegal : (programEventGraph g).patchLegal node leftPatch)
    (hrightLegal : (programEventGraph g).patchLegal node rightPatch) :
    eventGraphPublicView g
        (cfg.withPatch leftPatch hfrontier hleftLegal) =
      eventGraphPublicView g
        (cfg.withPatch rightPatch hfrontier hrightLegal) := by
  classical
  have htargetOwner : field.owner = some owner :=
    ProgramNode.commit_target_owner_of_sem g.obligations node hsem
  change ProgramNode.patchLegal g.obligations node leftPatch at hleftLegal
  change ProgramNode.patchLegal g.obligations node rightPatch at hrightLegal
  rw [ProgramNode.patchLegal, hsem] at hleftLegal hrightLegal
  rcases hleftLegal with ⟨leftValue, rfl⟩
  rcases hrightLegal with ⟨rightValue, rfl⟩
  ext candidate
  · by_cases hcandidate : candidate = node
    · simp [eventGraphPublicView, EventGraph.Configuration.withPatch,
        EventGraph.Configuration.updatePatch, hcandidate]
    · change
        (if candidate = node then
            some (ProgramField.singlePatch field leftValue)
          else cfg.result candidate).isSome =
          (if candidate = node then
            some (ProgramField.singlePatch field rightValue)
          else cfg.result candidate).isSome
      rw [if_neg hcandidate, if_neg hcandidate]
  · by_cases hpublic : candidate.owner = none
    · have hne : candidate ≠ field := by
        intro hcandidate
        subst candidate
        simp [htargetOwner] at hpublic
      have hvalueEq :
          eventGraphConfigValue? g
              (cfg.withPatch (ProgramField.singlePatch field leftValue)
                hfrontier hleftLegal) candidate =
            eventGraphConfigValue? g
              (cfg.withPatch (ProgramField.singlePatch field rightValue)
                hfrontier hrightLegal) candidate := by
        have hwriterNe :
            ProgramField.writer? candidate ≠ some node :=
          ProgramNode.writer?_ne_of_ne_commit_target
            g.obligations node hsem hne
        have hleftSame :
            eventGraphConfigValue? g
                (cfg.withPatch
                  (ProgramField.singlePatch field leftValue)
                  hfrontier hleftLegal) candidate =
              ProgramField.value? g.env cfg.result candidate := by
          simpa [eventGraphConfigValue?,
            EventGraph.Configuration.withPatch,
            EventGraph.Configuration.updatePatch] using
            ProgramField.value?_update_of_writer?_ne
              (p := g.prog) g.env (result := cfg.result)
              (field := candidate) (node := node)
              (patch := ProgramField.singlePatch field leftValue)
              hwriterNe
        have hrightSame :
            eventGraphConfigValue? g
                (cfg.withPatch
                  (ProgramField.singlePatch field rightValue)
                  hfrontier hrightLegal) candidate =
              ProgramField.value? g.env cfg.result candidate := by
          simpa [eventGraphConfigValue?,
            EventGraph.Configuration.withPatch,
            EventGraph.Configuration.updatePatch] using
            ProgramField.value?_update_of_writer?_ne
              (p := g.prog) g.env (result := cfg.result)
              (field := candidate) (node := node)
              (patch := ProgramField.singlePatch field rightValue)
              hwriterNe
        exact hleftSame.trans hrightSame.symm
      simp [eventGraphPublicView, hpublic, hvalueEq]
    · simp [eventGraphPublicView, hpublic]

/-- A hidden commit payload is invisible to every player other than its owner. -/
theorem eventGraph_hiddenCommit_observe_eq_of_ne_owner
    (g : WFProgram P L) (receiver owner : P)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {leftPatch rightPatch : ProgramField.FieldPatch g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (hsem :
      ProgramNode.sem g.obligations node =
        EventGraph.NodeSem.commit owner field guard)
    (hne : receiver ≠ owner)
    (hleftLegal : (programEventGraph g).patchLegal node leftPatch)
    (hrightLegal : (programEventGraph g).patchLegal node rightPatch) :
    eventGraphObserve g receiver
        (cfg.withPatch leftPatch hfrontier hleftLegal) =
      eventGraphObserve g receiver
        (cfg.withPatch rightPatch hfrontier hrightLegal) := by
  classical
  have htargetOwner : field.owner = some owner :=
    ProgramNode.commit_target_owner_of_sem g.obligations node hsem
  change ProgramNode.patchLegal g.obligations node leftPatch at hleftLegal
  change ProgramNode.patchLegal g.obligations node rightPatch at hrightLegal
  rw [ProgramNode.patchLegal, hsem] at hleftLegal hrightLegal
  rcases hleftLegal with ⟨leftValue, rfl⟩
  rcases hrightLegal with ⟨rightValue, rfl⟩
  ext candidate
  by_cases hvisible : candidate.VisibleTo receiver
  · have hneTarget : candidate ≠ field := by
      intro hcandidate
      subst candidate
      rcases hvisible with hpublic | hreceiver
      · simp [htargetOwner] at hpublic
      · have howner : owner = receiver :=
          Option.some.inj (htargetOwner.symm.trans hreceiver)
        exact hne howner.symm
    have hvalueEq :
        eventGraphConfigValue? g
            (cfg.withPatch (ProgramField.singlePatch field leftValue)
              hfrontier hleftLegal) candidate =
          eventGraphConfigValue? g
            (cfg.withPatch (ProgramField.singlePatch field rightValue)
              hfrontier hrightLegal) candidate := by
      have hwriterNe :
          ProgramField.writer? candidate ≠ some node :=
        ProgramNode.writer?_ne_of_ne_commit_target
          g.obligations node hsem hneTarget
      have hleftSame :
          eventGraphConfigValue? g
              (cfg.withPatch
                (ProgramField.singlePatch field leftValue)
                hfrontier hleftLegal) candidate =
            ProgramField.value? g.env cfg.result candidate := by
        simpa [eventGraphConfigValue?,
          EventGraph.Configuration.withPatch,
          EventGraph.Configuration.updatePatch] using
          ProgramField.value?_update_of_writer?_ne
            (p := g.prog) g.env (result := cfg.result)
            (field := candidate) (node := node)
            (patch := ProgramField.singlePatch field leftValue)
            hwriterNe
      have hrightSame :
          eventGraphConfigValue? g
              (cfg.withPatch
                (ProgramField.singlePatch field rightValue)
                hfrontier hrightLegal) candidate =
            ProgramField.value? g.env cfg.result candidate := by
        simpa [eventGraphConfigValue?,
          EventGraph.Configuration.withPatch,
          EventGraph.Configuration.updatePatch] using
          ProgramField.value?_update_of_writer?_ne
            (p := g.prog) g.env (result := cfg.result)
            (field := candidate) (node := node)
            (patch := ProgramField.singlePatch field rightValue)
            hwriterNe
      exact hleftSame.trans hrightSame.symm
    simp [eventGraphObserve, hvisible, hvalueEq]
  · simp [eventGraphObserve, hvisible]

/-- The owner of a hidden commit can observe the committed payload after the
commit node has executed. -/
theorem eventGraph_hiddenCommit_observe_owner_sees_payload
    (g : WFProgram P L) (owner : P)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {patch : ProgramField.FieldPatch g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (_hsem :
      ProgramNode.sem g.obligations node =
        EventGraph.NodeSem.commit owner field guard)
    (hvisible : field.VisibleTo owner)
    (hlegal : (programEventGraph g).patchLegal node patch) :
    (eventGraphObserve g owner
        (cfg.withPatch patch hfrontier hlegal)).value? field =
      eventGraphConfigValue? g
        (cfg.withPatch patch hfrontier hlegal) field := by
  simp [eventGraphObserve, hvisible]

/-- Reveal nodes are the declassification primitive: the public observation of
the reveal target is exactly the target's graph value after the reveal step. -/
theorem eventGraph_reveal_is_declassification
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {source target : ProgramField g.prog}
    {sameTy : source.ty = target.ty}
    {patch : ProgramField.FieldPatch g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (_hsem :
      ProgramNode.sem g.obligations node =
        EventGraph.NodeSem.reveal source target sameTy)
    (hpublic : target.owner = none)
    (hlegal : (programEventGraph g).patchLegal node patch) :
    (eventGraphPublicView g
        (cfg.withPatch patch hfrontier hlegal)).value? target =
      eventGraphConfigValue? g
        (cfg.withPatch patch hfrontier hlegal) target := by
  simp [eventGraphPublicView, hpublic]

/-- Commit/reveal information barrier: no reveal can be frontier-simultaneous
with an earlier commit.  This is stronger than saying the reveal reads its own
payload; it prevents a revealed value from becoming observable before all
earlier same-phase commitments have been chosen. -/
theorem reveal_not_frontier_with_prior_commit
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {commit reveal : ProgramNode g.prog}
    {owner : P} {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {source target : ProgramField g.prog}
    {hty : source.ty = target.ty}
    (hcommitFrontier : commit ∈ cfg.frontier)
    (hrevealFrontier : reveal ∈ cfg.frontier)
    (hcommit :
      ProgramNode.sem g.obligations commit =
        EventGraph.NodeSem.commit owner field guard)
    (hreveal :
      ProgramNode.sem g.obligations reveal =
        EventGraph.NodeSem.reveal source target hty)
    (hrank : commit.rank < reveal.rank) :
    False :=
  eventGraph_priorCommit_not_frontier_with_reveal
    g hcommitFrontier hrevealFrontier hcommit hreveal hrank

/-- Terminal outcomes are equal for terminal configurations whose assembled
final environments have equal public erasures. -/
theorem terminalOutcome_eq_of_erasePubEnv_eq
    (g : WFProgram P L)
    {left right : (programEventGraph g).Configuration}
    (_hleftTerminal : left.terminal)
    (_hrightTerminal : right.terminal)
    {leftEnv rightEnv : VEnv L (ProgramField.finalVCtx g.prog)}
    (hleftEnv :
      ProgramField.finalEnv? g.prog (eventGraphConfigValue? g left) =
        some leftEnv)
    (hrightEnv :
      ProgramField.finalEnv? g.prog (eventGraphConfigValue? g right) =
        some rightEnv)
    (hpub : VEnv.erasePubEnv leftEnv = VEnv.erasePubEnv rightEnv) :
    eventGraphOutcome g left = eventGraphOutcome g right := by
  simp [eventGraphOutcome, hleftEnv, hrightEnv,
    evalPayoffs_eq_of_erasePubEnv_eq (payoffs := ProgramField.finalPayoffs g.prog)
      hpub]

omit [DecidableEq P] in
private theorem erasePubVCtx_map_fst_subset_publicVars :
    {Γ : VCtx P L} →
      ∀ x, x ∈ (erasePubVCtx Γ).map Prod.fst →
        x ∈ publicVars (L := L) Γ
  | [], x, hx => by
      simp [erasePubVCtx] at hx
  | (y, ⟨τ, .pub⟩) :: Γ, x, hx => by
      change x ∈ y :: (erasePubVCtx Γ).map Prod.fst at hx
      simp only [List.mem_cons] at hx
      rcases hx with hxy | hx
      · subst x
        simp [publicVars]
      · exact Finset.mem_insert_of_mem
          (erasePubVCtx_map_fst_subset_publicVars (Γ := Γ) x hx)
  | (y, ⟨τ, .hidden owner⟩) :: Γ, x, hx => by
      change x ∈ (erasePubVCtx Γ).map Prod.fst at hx
      simpa [publicVars] using
        (erasePubVCtx_map_fst_subset_publicVars (Γ := Γ) x hx)

omit [DecidableEq P] in
/-- Payoff expressions mention only public/revealed variables. -/
theorem payoff_expr_no_hidden_dependency
    {Γ : VCtx P L}
    (payoffs : List (P × L.Expr (erasePubVCtx Γ) L.int)) :
    ∀ entry ∈ payoffs, L.exprDeps entry.2 ⊆ publicVars (L := L) Γ := by
  intro entry _hentry x hx
  exact erasePubVCtx_map_fst_subset_publicVars (Γ := Γ) x
    (L.expr_deps_context entry.2 x hx)

/-- A hidden commit payload cannot signal to a non-owner: public observation
and the receiver's private observation are unchanged by changing only that
payload. -/
theorem commit_payload_no_signal_to_nonowner
    (g : WFProgram P L) (receiver owner : P)
    {cfg : (programEventGraph g).Configuration}
    {node : ProgramNode g.prog}
    {field : ProgramField g.prog}
    {guard : EventGraph.EventGuard L (ProgramField g.prog)
      (ProgramField.ty (p := g.prog)) field}
    {leftPatch rightPatch : ProgramField.FieldPatch g.prog}
    (hfrontier : node ∈ cfg.frontier)
    (hsem :
      ProgramNode.sem g.obligations node =
        EventGraph.NodeSem.commit owner field guard)
    (hne : receiver ≠ owner)
    (hleftLegal : (programEventGraph g).patchLegal node leftPatch)
    (hrightLegal : (programEventGraph g).patchLegal node rightPatch) :
    eventGraphPublicView g
        (cfg.withPatch leftPatch hfrontier hleftLegal) =
        eventGraphPublicView g
          (cfg.withPatch rightPatch hfrontier hrightLegal) ∧
      eventGraphObserve g receiver
        (cfg.withPatch leftPatch hfrontier hleftLegal) =
        eventGraphObserve g receiver
          (cfg.withPatch rightPatch hfrontier hrightLegal) := by
  exact
    ⟨eventGraph_hiddenCommit_publicView_eq_of_payload_eq_except_hidden
        g hfrontier hsem hleftLegal hrightLegal,
      eventGraph_hiddenCommit_observe_eq_of_ne_owner
        g receiver owner hfrontier hsem hne hleftLegal hrightLegal⟩

/-- If two configurations agree on every field visible to a player, then that
player's current private observation is the same in both configurations. -/
theorem unrevealed_hidden_values_no_signal
    (g : WFProgram P L) (who : P)
    {left right : (programEventGraph g).Configuration}
    (hvisible :
      ∀ field : ProgramField g.prog,
        field.VisibleTo who →
          eventGraphConfigValue? g left field =
            eventGraphConfigValue? g right field) :
    eventGraphObserve g who left = eventGraphObserve g who right := by
  ext field
  by_cases hfield : field.VisibleTo who
  · simp [eventGraphObserve, hfield, hvisible field hfield]
  · simp [eventGraphObserve, hfield]

end Vegas
