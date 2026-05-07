import Vegas.Strategic.KernelGame
import Vegas.Theorems.Visibility

/-!
# Outcome Adequacy Theorems

Project-facing names for the connection between terminal event-graph states,
declared payoff expressions, and strategic-form outcome kernels.
-/

namespace Vegas

open GameTheory

variable {P : Type} [DecidableEq P] {L : IExpr}

@[simp] theorem ProgramField.owner_ofFinal :
    {Γ : VCtx P L} → (p : VegasCore P L Γ) →
      (field : VCtxField P L (ProgramField.finalVCtx p)) →
        (ProgramField.ofFinal p field).owner = field.owner
  | _, .ret _, field => rfl
  | _, .letExpr _ _ k, field => by
      exact ProgramField.owner_ofFinal k field
  | _, .sample _ _ k, field => by
      exact ProgramField.owner_ofFinal k field
  | _, .commit _ _ _ k, field => by
      exact ProgramField.owner_ofFinal k field
  | _, .reveal _ _ _ _ k, field => by
      exact ProgramField.owner_ofFinal k field

/-- Terminal event-graph configurations assemble the final source environment
used by payoff evaluation. -/
theorem checkedProgram_terminalFinalEnv_isSome
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : cfg.terminal) :
    (ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg)).isSome :=
  eventGraph_finalEnv?_isSome_of_terminal g hterminal

/-- Terminal event-graph outcomes are the declared payoff expressions evaluated
in the assembled final source environment. -/
theorem checkedProgram_terminalOutcome_eq_evalPayoffs
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    (hterminal : cfg.terminal) :
    ∃ env : VEnv L (ProgramField.finalVCtx g.prog),
      ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg) = some env ∧
        eventGraphOutcome g cfg =
          evalPayoffs (ProgramField.finalPayoffs g.prog) env :=
  eventGraphOutcome_eq_evalPayoffs_of_terminal g hterminal

/-- A checked game that is played legally to completion reaches its declared
payoff rule. -/
theorem checkedProgram_wholeGame_reaches_declared_payoff_rule
    (g : WFProgram P L)
    (h :
      (((eventGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).History))
    (hcomplete :
      ((eventGraphFOSGView g).toBoundedFOSG
        (syntaxSteps g.prog)).terminal h.lastState) :
    ∃ env : VEnv L (ProgramField.finalVCtx g.prog),
      ProgramField.finalEnv? g.prog
          (eventGraphConfigValue? g h.lastState.state) = some env ∧
        eventGraphOutcome g h.lastState.state =
          evalPayoffs (ProgramField.finalPayoffs g.prog) env :=
  eventGraph_wholeGame_reaches_declared_payoff_rule g h hcomplete

/-- Pure strategic-form outcomes are exactly the event-graph machine blocked
trace outcomes projected to payoff outcomes. -/
theorem checkedProgram_pureOutcome_eq_blockTrace
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (π : pureProfileAt g) :
    pureOutcomeKernelAt g π =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
          (GameTheory.FOSG.legalPureToBehavioral
            ((eventGraphFOSGView g).toBoundedFOSG (syntaxSteps g.prog))
            π.extend)
          (syntaxSteps g.prog)
          (eventGraphInitialHistory g (syntaxSteps g.prog))) :=
  pureOutcomeKernelAt_eq_blockTraceDist g π

/-- PMF behavioral strategic-form outcomes are exactly the event-graph machine
blocked trace outcomes projected to payoff outcomes. -/
theorem checkedProgram_behavioralOutcome_eq_blockTrace
    [Fintype P] (g : WFProgram P L) [FiniteDomains g]
    (β : behavioralProfilePMFAt g) :
    behavioralOutcomeKernelPMFAt g β =
      PMF.map
        (eventGraphTraceOutcome g)
        (eventGraphFOSGBlockTraceDistFrom g (syntaxSteps g.prog)
          β.extend
          (syntaxSteps g.prog)
          (eventGraphInitialHistory g (syntaxSteps g.prog))) :=
  behavioralOutcomeKernelPMFAt_eq_blockTraceDist g β

/-- Equality after projecting blocked traces to syntax outcomes gives equality
of the induced outcome laws. -/
theorem outcomeKernel_eq_of_traceOutcome_eq
    (g : WFProgram P L)
    {left right : PMF (syntaxBlockedTraceAt g)}
    (h :
      PMF.map (eventGraphTraceOutcome g) left =
        PMF.map (eventGraphTraceOutcome g) right) :
    PMF.map (eventGraphTraceOutcome g) left =
      PMF.map (eventGraphTraceOutcome g) right :=
  h

private theorem ProgramField.finalEnv?_erasePubEnv_eq_of_public_values
    {Γ : VCtx P L} (p : VegasCore P L Γ)
    {leftValue? rightValue? :
      (field : ProgramField p) → Option (L.Val field.ty)}
    {leftEnv rightEnv : VEnv L (ProgramField.finalVCtx p)}
    (hleft :
      ProgramField.finalEnv? p leftValue? = some leftEnv)
    (hright :
      ProgramField.finalEnv? p rightValue? = some rightEnv)
    (hpub :
      ∀ field : VCtxField P L (ProgramField.finalVCtx p),
        (ProgramField.ofFinal p field).owner = none →
          leftValue? (ProgramField.ofFinal p field) =
            rightValue? (ProgramField.ofFinal p field)) :
    VEnv.erasePubEnv leftEnv = VEnv.erasePubEnv rightEnv := by
  classical
  unfold ProgramField.finalEnv? at hleft hright
  split at hleft <;> rename_i hleftAvail
  · split at hright <;> rename_i hrightAvail
    · have hleftEnv := Option.some.inj hleft
      have hrightEnv := Option.some.inj hright
      subst leftEnv
      subst rightEnv
      funext x τ hx
      let field : VCtxField P L (ProgramField.finalVCtx p) :=
        .mk (VHasVar.ofPubVCtx (HasVar.toVHasVarPub hx))
      have howner :
          (ProgramField.ofFinal p field).owner = none := by
        rw [ProgramField.owner_ofFinal p field]
        simp [field, VCtxField.owner, VCtxField.bindTy]
      have hvalues := hpub field howner
      have hleftSome :
          leftValue? (ProgramField.ofFinal p field) =
            some (Classical.choose
              (Option.isSome_iff_exists.mp (hleftAvail field))) :=
        Classical.choose_spec
          (Option.isSome_iff_exists.mp (hleftAvail field))
      have hrightSome :
          rightValue? (ProgramField.ofFinal p field) =
            some (Classical.choose
              (Option.isSome_iff_exists.mp (hrightAvail field))) :=
        Classical.choose_spec
          (Option.isSome_iff_exists.mp (hrightAvail field))
      have hchosen :
          Classical.choose
              (Option.isSome_iff_exists.mp (hleftAvail field)) =
            Classical.choose
              (Option.isSome_iff_exists.mp (hrightAvail field)) := by
        apply Option.some.inj
        calc
          some (Classical.choose
              (Option.isSome_iff_exists.mp (hleftAvail field))) =
              leftValue? (ProgramField.ofFinal p field) := hleftSome.symm
          _ = rightValue? (ProgramField.ofFinal p field) := hvalues
          _ = some (Classical.choose
              (Option.isSome_iff_exists.mp (hrightAvail field))) := hrightSome
      simp [VEnv.erasePubEnv_get, field, hchosen]
    · simp at hright
  · simp at hleft

/-- Terminal syntax outcomes depend only on public terminal fields. -/
theorem terminalOutcome_public_only
    (g : WFProgram P L)
    {left right : (programEventGraph g).Configuration}
    (hleftTerminal : left.terminal)
    (hrightTerminal : right.terminal)
    (hpub :
      ∀ field : ProgramField g.prog,
        field.owner = none →
          eventGraphConfigValue? g left field =
            eventGraphConfigValue? g right field) :
    eventGraphOutcome g left = eventGraphOutcome g right := by
  rcases eventGraphOutcome_eq_evalPayoffs_of_terminal g hleftTerminal with
    ⟨leftEnv, hleftEnv, _hleftOutcome⟩
  rcases eventGraphOutcome_eq_evalPayoffs_of_terminal g hrightTerminal with
    ⟨rightEnv, hrightEnv, _hrightOutcome⟩
  apply terminalOutcome_eq_of_erasePubEnv_eq g
    hleftTerminal hrightTerminal hleftEnv hrightEnv
  apply ProgramField.finalEnv?_erasePubEnv_eq_of_public_values g.prog
    hleftEnv hrightEnv
  intro field howner
  exact hpub (ProgramField.ofFinal g.prog field) howner

/-- The declared payoff rule is independent of final-environment witness
choices. -/
theorem declared_payoff_rule_unique
    (g : WFProgram P L)
    {cfg : (programEventGraph g).Configuration}
    {leftEnv rightEnv : VEnv L (ProgramField.finalVCtx g.prog)}
    (hleft :
      ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg) =
        some leftEnv)
    (hright :
      ProgramField.finalEnv? g.prog (eventGraphConfigValue? g cfg) =
        some rightEnv) :
    evalPayoffs (ProgramField.finalPayoffs g.prog) leftEnv =
      evalPayoffs (ProgramField.finalPayoffs g.prog) rightEnv := by
  have henv : leftEnv = rightEnv := Option.some.inj (hleft.symm.trans hright)
  subst rightEnv
  rfl

end Vegas
