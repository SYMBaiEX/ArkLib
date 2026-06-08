import ArkLib.OracleReduction.Composition.Sequential.EmptyAppendReduction
import ArkLib.OracleReduction.Composition.Sequential.AppendRunEvalDist
import ArkLib.OracleReduction.Completeness

/-! Reconstruction helper for append-completeness (#113): component prover+verifier supports
compose into a `Reduction.run` support point. The reusable core of the append-completeness
keystone (used twice after `Verifier.append_run` splits the seam). -/

open OracleComp OracleSpec ProtocolSpec

namespace Reduction

variable {ι : Type} {oSpec : OracleSpec ι} [oSpec.Fintype] [oSpec.Inhabited]
  {StmtIn WitIn StmtOut WitOut : Type} {n : ℕ} {pSpec : ProtocolSpec n}

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- A `Reduction.run` outcome is in the support whenever its prover-transcript piece is in the
prover's support and its verifier output is in the verifier's support on that transcript. -/
theorem mem_support_run_of_prover_verifier
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (tr : FullTranscript pSpec) (prv : StmtOut × WitOut) (vout : StmtOut)
    (hP : (tr, prv) ∈ support (R.prover.run stmt wit))
    (hV : some vout ∈ support (OptionT.run (R.verifier.run stmt tr))) :
    some ((tr, prv), vout) ∈ support (OptionT.run (R.run stmt wit)) := by
  unfold Reduction.run
  simp only [OptionT.run_bind, Option.elimM, mem_support_bind_iff]
  refine ⟨some (tr, prv), ?_, ?_⟩
  · change some (tr, prv) ∈ support (some <$> R.prover.run stmt wit)
    simp only [support_map, Set.mem_image, Option.some.injEq]; exact ⟨_, hP, rfl⟩
  · simp only [Option.elim_some, mem_support_bind_iff]
    refine ⟨some (some vout), ?_, ?_⟩
    · rw [OptionT.run_liftM_run, support_map,
        support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)]
      simp only [Set.mem_image, Option.some.injEq]
      exact ⟨some vout, hV, rfl⟩
    · simp only [Option.elim_some, Option.getM_some, OptionT.run_pure, pure_bind,
        support_pure, Set.mem_singleton_iff]

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- Adding the standard challenge implementation preserves support-faithfulness of a stateful
implementation. The original oracle half is delegated to `hImplSupp`; the challenge half is exactly
the support of the standard sampler. -/
theorem support_faithful_addLift_challengeQueryImpl
    [∀ i, SampleableType (pSpec.Challenge i)]
    {σ : Type} (impl : QueryImpl oSpec (StateT σ ProbComp))
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) =
        support (liftM q : OracleComp oSpec β)) :
    ∀ {β} (q : OracleQuery (oSpec + [pSpec.Challenge]ₒ) β) s,
      Prod.fst <$> support
        ((QueryImpl.mapQuery
          (QueryImpl.addLift impl challengeQueryImpl :
            QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp)) q).run s) =
        support (liftM q : OracleComp (oSpec + [pSpec.Challenge]ₒ) β) := by
  intro β q s
  cases q with | mk t f =>
  cases t with
  | inl i => exact hImplSupp (OracleQuery.mk i f) s
  | inr i =>
    simp only [QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
      QueryImpl.addLift_def, QueryImpl.add_apply_inr]
    have hq := support_challengeQueryImpl_run_eq (q := OracleQuery.mk i f) s
    rw [support_liftM]
    simpa only [ChallengeIdx, Challenge, add_apply_inr, QueryImpl.liftTarget_apply,
      StateT.run_map, StateT.run_monadLift, monadLift_self, bind_pure_comp, Functor.map_map,
      support_map, Set.fmap_eq_image, toPFunctor_add, ofPFunctor_add, ofPFunctor_toPFunctor,
      support_liftM, QueryImpl.mapQuery, OracleQuery.input_apply, OracleQuery.cont_apply,
      liftM_map] using hq

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- Component perfect completeness yields the pure support-good predicate consumed by append support
decomposition, provided the stateful implementation is support-faithful. -/
theorem run_support_good_of_perfectCompleteness
    [∀ i, SampleableType (pSpec.Challenge i)]
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (h : R.perfectCompleteness init impl relIn relOut)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) =
        support (liftM q : OracleComp oSpec β))
    (stmt : StmtIn) (wit : WitIn) (hmem : (stmt, wit) ∈ relIn) :
    ∀ out, out ∈ support (R.run stmt wit) →
      (out.2, out.1.2.2) ∈ relOut ∧ out.1.2.1 = out.2 := by
  have hprob := (perfectCompleteness_eq_prob_one (init := init) (impl := impl)
    (relIn := relIn) (relOut := relOut) (reduction := R)).1 h stmt wit hmem
  rw [probEvent_eq_one_iff] at hprob
  intro out hout
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl challengeQueryImpl
  have hImplSuppAdd : ∀ {β} (q : OracleQuery (oSpec + [pSpec.Challenge]ₒ) β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery pImpl q).run s) =
        support (liftM q : OracleComp (oSpec + [pSpec.Challenge]ₒ) β) := by
    intro β q s
    simpa [pImpl] using
      (support_faithful_addLift_challengeQueryImpl
        (pSpec := pSpec) (impl := impl) hImplSupp (β := β) q s)
  have hsuppEq := support_bind_simulateQ_run'_eq_mk
    (init := init) (impl := pImpl)
    (oa := (R.run stmt wit).run) (hInit := hInit) (hImplSupp := hImplSuppAdd)
  have hsim : out ∈ support
      (OptionT.mk (do
        let s ← init
        (simulateQ pImpl (R.run stmt wit).run).run' s) :
          OptionT ProbComp ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut)) := by
    rw [hsuppEq]
    exact hout
  exact hprob.2 out hsim

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- Component perfect completeness also yields pure failure-freedom of `Reduction.run`, provided the
stateful implementation is support-faithful. This strips the simulated execution back to the
specification by choosing any supported initial state of the never-failing `init`. -/
theorem run_neverFail_of_perfectCompleteness
    [∀ i, SampleableType (pSpec.Challenge i)]
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    {σ : Type} {init : ProbComp σ} {impl : QueryImpl oSpec (StateT σ ProbComp)}
    {relIn : Set (StmtIn × WitIn)} {relOut : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (h : R.perfectCompleteness init impl relIn relOut)
    (hInit : NeverFail init)
    (hImplSupp : ∀ {β} (q : OracleQuery oSpec β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery impl q).run s) =
        support (liftM q : OracleComp oSpec β))
    (stmt : StmtIn) (wit : WitIn) (hmem : (stmt, wit) ∈ relIn) :
    NeverFail (R.run stmt wit) := by
  have hprob := (perfectCompleteness_eq_prob_one (init := init) (impl := impl)
    (relIn := relIn) (relOut := relOut) (reduction := R)).1 h stmt wit hmem
  rw [probEvent_eq_one_iff] at hprob
  let pImpl : QueryImpl (oSpec + [pSpec.Challenge]ₒ) (StateT σ ProbComp) :=
    QueryImpl.addLift impl challengeQueryImpl
  have hImplSuppAdd : ∀ {β} (q : OracleQuery (oSpec + [pSpec.Challenge]ₒ) β) s,
      Prod.fst <$> support ((QueryImpl.mapQuery pImpl q).run s) =
        support (liftM q : OracleComp (oSpec + [pSpec.Challenge]ₒ) β) := by
    intro β q s
    simpa [pImpl] using
      (support_faithful_addLift_challengeQueryImpl
        (pSpec := pSpec) (impl := impl) hImplSupp (β := β) q s)
  have hfail : Pr[⊥ |
      (OptionT.mk (do
        let s ← init
        (simulateQ pImpl (R.run stmt wit).run).run' s) :
          OptionT ProbComp ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut))] = 0 :=
    hprob.1
  rw [OptionT.probFailure_mk_do_bind_eq_zero_iff] at hfail
  obtain ⟨s, hs⟩ := support_nonempty_of_neverFails init hInit
  have hsim := hfail.2 s hs
  rw [probFailure_simulateQ_iff_stateful_run'_mk
    (impl := pImpl) (hImplSupp := hImplSuppAdd)
    (oa := (R.run stmt wit).run) (s := s)] at hsim
  exact NeverFail.mk (by
    change Pr[⊥ |
      (OptionT.mk (R.run stmt wit).run :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut))] = 0
    exact hsim)

/-- A no-failing `OptionT` computation has at least one successful support point. -/
theorem optionT_support_nonempty_of_neverFail
    {ι' : Type} {spec : OracleSpec ι'} [spec.Fintype] [spec.Inhabited]
    {α : Type} (mx : OptionT (OracleComp spec) α) (h : NeverFail mx) :
    (support mx).Nonempty := by
  have hfail : Pr[⊥ | mx] = 0 := h.probFailure_eq_zero
  have h_event_pos : 0 < Pr[fun _ => True | mx] := by
    simp only [probEvent_True_eq_sub, hfail, tsub_zero, zero_lt_one]
  rcases (probEvent_pos_iff (mx := mx) (p := fun _ => True)).1 h_event_pos with
    ⟨x, hx, _⟩
  exact ⟨x, hx⟩

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- Failure-freedom of a full reduction run implies failure-freedom of the honest prover run. -/
theorem prover_neverFail_of_run_neverFail
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (h : NeverFail (R.run stmt wit)) :
    NeverFail (R.prover.run stmt wit) := by
  let tail :
      (pSpec.FullTranscript × StmtOut × WitOut) →
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) :=
    fun proverResult => do
      let stmtOut ← liftM (R.verifier.run stmt proverResult.1).run
      let stmtOut' ← stmtOut.getM
      return Prod.mk proverResult stmtOut'
  have hrun : NeverFail (do
      let proverResult ← (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut))
      tail proverResult) := by
    simpa [Reduction.run, tail] using h
  have hbind := (HasEvalSPMF.neverFail_bind_iff
    (mx := (liftM (R.prover.run stmt wit) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (pSpec.FullTranscript × StmtOut × WitOut)))
    (my := tail)).1 hrun
  exact NeverFail.mk (by
    have hprob : Pr[⊥ | (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut))] = 0 :=
      hbind.1.probFailure_eq_zero
    rw [OptionT.probFailure_liftM] at hprob
    exact hprob)

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- If a run is failure-free and every run support point is relation-good, then every supported
honest prover output already carries a relation-valid output witness. -/
theorem prover_support_rel_of_run_neverFail_good
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    {relOut : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (hnf : NeverFail (R.run stmt wit))
    (hgood :
      ∀ out, out ∈ support (R.run stmt wit) →
        (out.2, out.1.2.2) ∈ relOut ∧ out.1.2.1 = out.2)
    (pr : pSpec.FullTranscript × StmtOut × WitOut)
    (hpr : pr ∈ support (R.prover.run stmt wit)) :
    (pr.2.1, pr.2.2) ∈ relOut := by
  let tail :
      (pSpec.FullTranscript × StmtOut × WitOut) →
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) :=
    fun proverResult => do
      let stmtOut ← liftM (R.verifier.run stmt proverResult.1).run
      let stmtOut' ← stmtOut.getM
      return Prod.mk proverResult stmtOut'
  have hrun : NeverFail (do
      let proverResult ← (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut))
      tail proverResult) := by
    simpa [Reduction.run, tail] using hnf
  have hbind := (HasEvalSPMF.neverFail_bind_iff
    (mx := (liftM (R.prover.run stmt wit) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (pSpec.FullTranscript × StmtOut × WitOut)))
    (my := tail)).1 hrun
  have hprLift :
      pr ∈ support (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut)) := by
    simpa [OptionT.support_liftM] using hpr
  have htail := hbind.2 pr hprLift
  obtain ⟨out, houtTail⟩ :=
    optionT_support_nonempty_of_neverFail (tail pr) htail
  have houtRunBind : out ∈ support (do
      let proverResult ← (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut))
      tail proverResult) := by
    rw [OptionT.mem_support_bind_iff]
    exact ⟨pr, hprLift, houtTail⟩
  have houtRun : out ∈ support (R.run stmt wit) := by
    simpa [Reduction.run, tail] using houtRunBind
  have hout_fst : out.1 = pr := by
    change out ∈ support (do
      let stmtOut ← (liftM (R.verifier.run stmt pr.1).run :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut))
      let stmtOut' ← stmtOut.getM
      return Prod.mk pr stmtOut') at houtTail
    rw [OptionT.mem_support_bind_iff] at houtTail
    rcases houtTail with ⟨stmtOpt, _hstmtOpt, houtTail⟩
    cases stmtOpt with
    | none =>
        simp [Option.getM] at houtTail
    | some stmtOut =>
        have hout_eq : out = (pr, stmtOut) := by
          simpa [Option.getM] using houtTail
        exact congrArg Prod.fst hout_eq
  have hres := hgood out houtRun
  have hstmt : pr.2.1 = out.2 := by
    simpa [hout_fst] using hres.2
  have hrel : (out.2, pr.2.2) ∈ relOut := by
    simpa [hout_fst] using hres.1
  simpa [← hstmt] using hrel

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- On any supported prover transcript, failure-freedom of the full run rules out verifier
failure. -/
theorem verifier_none_not_mem_of_run_neverFail
    [(oSpec + [pSpec.Challenge]ₒ).Fintype] [(oSpec + [pSpec.Challenge]ₒ).Inhabited]
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (hnf : NeverFail (R.run stmt wit))
    (pr : pSpec.FullTranscript × StmtOut × WitOut)
    (hpr : pr ∈ support (R.prover.run stmt wit)) :
    (none : Option StmtOut) ∉ support (OptionT.run (R.verifier.run stmt pr.1)) := by
  intro hnone
  let tail :
      (pSpec.FullTranscript × StmtOut × WitOut) →
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) :=
    fun proverResult => do
      let stmtOut ← liftM (R.verifier.run stmt proverResult.1).run
      let stmtOut' ← stmtOut.getM
      return Prod.mk proverResult stmtOut'
  have hrun : NeverFail (do
      let proverResult ← (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut))
      tail proverResult) := by
    simpa [Reduction.run, tail] using hnf
  have hbind := (HasEvalSPMF.neverFail_bind_iff
    (mx := (liftM (R.prover.run stmt wit) :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
        (pSpec.FullTranscript × StmtOut × WitOut)))
    (my := tail)).1 hrun
  have hprLift :
      pr ∈ support (liftM (R.prover.run stmt wit) :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          (pSpec.FullTranscript × StmtOut × WitOut)) := by
    simpa [OptionT.support_liftM] using hpr
  have htail := hbind.2 pr hprLift
  let tailGet :
      Option StmtOut →
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ))
          ((pSpec.FullTranscript × StmtOut × WitOut) × StmtOut) :=
    fun stmtOut => do
      let stmtOut' ← stmtOut.getM
      return Prod.mk pr stmtOut'
  have htailRun : NeverFail (do
      let stmtOut ← (liftM (R.verifier.run stmt pr.1).run :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut))
      tailGet stmtOut) := by
    simpa [tail, tailGet] using htail
  have htailBind := (HasEvalSPMF.neverFail_bind_iff
    (mx := (liftM (R.verifier.run stmt pr.1).run :
      OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)))
    (my := tailGet)).1 htailRun
  have hnoneLift :
      none ∈ support (liftM (R.verifier.run stmt pr.1).run :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)) := by
    change some none ∈ support (OptionT.run
      (liftM (R.verifier.run stmt pr.1).run :
        OptionT (OracleComp (oSpec + [pSpec.Challenge]ₒ)) (Option StmtOut)))
    rw [OptionT.run_liftM_run, support_map,
      support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)]
    simp only [Set.mem_image, Option.some.injEq]
    exact ⟨none, hnone, rfl⟩
  have hbad := htailBind.2 none hnoneLift
  have hprob : Pr[⊥ | tailGet none] = 0 := hbad.probFailure_eq_zero
  simp [tailGet, Option.getM] at hprob

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- A verifier support point combines with a support-good full run to identify the intermediate
statement and relation. -/
theorem verifier_support_good_of_run_support_good
    {relOut : Set (StmtOut × WitOut)}
    (R : Reduction oSpec StmtIn WitIn StmtOut WitOut pSpec)
    (stmt : StmtIn) (wit : WitIn)
    (hgood :
      ∀ out, out ∈ support (R.run stmt wit) →
        (out.2, out.1.2.2) ∈ relOut ∧ out.1.2.1 = out.2)
    (pr : pSpec.FullTranscript × StmtOut × WitOut)
    (hpr : pr ∈ support (R.prover.run stmt wit))
    (mid : StmtOut)
    (hmid : some mid ∈ support (OptionT.run (R.verifier.run stmt pr.1))) :
    (mid, pr.2.2) ∈ relOut ∧ pr.2.1 = mid := by
  have hrun :
      some ((pr.1, (pr.2.1, pr.2.2)), mid) ∈
        support (OptionT.run (R.run stmt wit)) :=
    mem_support_run_of_prover_verifier
      R stmt wit pr.1 (pr.2.1, pr.2.2) mid hpr hmid
  have hsupport :
      (((pr.1, (pr.2.1, pr.2.2)), mid)) ∈ support (R.run stmt wit) :=
    (OptionT.mem_support_iff
      (mx := R.run stmt wit)
      (x := (((pr.1, (pr.2.1, pr.2.2)), mid)))).2 hrun
  simpa using hgood _ hsupport

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- The composed lift from an `OracleComp` into an `OptionT` over a larger oracle spec wraps every
base output in `some`; it does not introduce OptionT failure. -/
theorem run_liftM_oracleComp_to_optionT
    {ι' : Type} {superSpec : OracleSpec ι'} [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery oSpec) (OracleQuery superSpec)]
    {α : Type}
    (oa : OracleComp oSpec α) :
    OptionT.run
      (@liftM (OracleComp oSpec) (OptionT (OracleComp superSpec))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
          (OptionT (OracleComp superSpec))) α oa) =
      some <$> (liftM oa : OracleComp superSpec α) := by
  change OptionT.run
      (liftM (monadLift oa : OptionT (OracleComp oSpec) α) :
        OptionT (OracleComp superSpec) α) =
    some <$> (liftM oa : OracleComp superSpec α)
  rw [OracleComp.liftM_OptionT_eq]
  change simulateQ (fun t => liftM (oSpec.query t))
      ((monadLift oa : OptionT (OracleComp oSpec) α).run) =
    some <$> (liftM oa : OracleComp superSpec α)
  rw [OptionT.run_monadLift (m := OracleComp oSpec) (n := OracleComp oSpec) (x := oa)]
  rw [monadLift_eq_self]
  erw [simulateQ_map]
  rw [← OracleComp.liftComp_eq_liftM (superSpec := superSpec) oa]
  rfl

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- Lifting a plain `OracleComp` into `OptionT` over a larger oracle spec cannot fail. -/
theorem probFailure_liftM_oracleComp_to_optionT_eq_zero
    {ι' : Type} {superSpec : OracleSpec ι'} [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery oSpec) (OracleQuery superSpec)]
    {α : Type}
    (oa : OracleComp oSpec α) :
    Pr[⊥ |
      (@liftM (OracleComp oSpec) (OptionT (OracleComp superSpec))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
          (OptionT (OracleComp superSpec))) α oa)] = 0 := by
  rw [OptionT.probFailure_eq]
  rw [run_liftM_oracleComp_to_optionT (superSpec := superSpec) oa]
  simp only [HasEvalPMF.probFailure_eq_zero, zero_add]
  apply probOutput_eq_zero_of_not_mem_support
  intro hnone
  rw [support_map] at hnone
  rcases hnone with ⟨x, _, hx⟩
  cases hx

omit [oSpec.Fintype] [oSpec.Inhabited] in
/-- Support of the composed `OracleComp`-to-`OptionT` lift reflects to support of the base
computation. -/
theorem mem_support_of_mem_support_liftM_oracleComp_to_optionT
    {ι' : Type} {superSpec : OracleSpec ι'} [superSpec.Fintype] [superSpec.Inhabited]
    [MonadLift (OracleQuery oSpec) (OracleQuery superSpec)]
    {α : Type}
    (oa : OracleComp oSpec α) {x : α}
    (hx : x ∈ support
      (@liftM (OracleComp oSpec) (OptionT (OracleComp superSpec))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
          (OptionT (OracleComp superSpec))) α oa)) :
    x ∈ support oa := by
  have hxRun :
      some x ∈ support (OptionT.run
        (@liftM (OracleComp oSpec) (OptionT (OracleComp superSpec))
          (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
            (OptionT (OracleComp superSpec))) α oa)) :=
    (OptionT.mem_support_iff
      (mx := @liftM (OracleComp oSpec) (OptionT (OracleComp superSpec))
        (instMonadLiftTOfMonadLift (OracleComp oSpec) (OptionT (OracleComp oSpec))
          (OptionT (OracleComp superSpec))) α oa)
      (x := x)).1 hx
  rw [run_liftM_oracleComp_to_optionT (superSpec := superSpec) oa] at hxRun
  rw [support_map] at hxRun
  rcases hxRun with ⟨y, hy, hyx⟩
  have hyLift : y ∈ support (oa.liftComp superSpec) := by
    simpa [OracleComp.liftComp_eq_liftM] using hy
  have hyBase : y ∈ support oa :=
    OracleComp.mem_support_of_mem_support_liftComp
      (oa := oa) (x := y) hyLift
  simpa [Option.some.inj hyx] using hyBase

variable {Stmt₁ Stmt₂ Stmt₃ : Type} {m n : ℕ}
  {pSpec₁ : ProtocolSpec m} {pSpec₂ : ProtocolSpec n}

/-- Successful support of an appended verifier splits through the intermediate statement. -/
theorem mem_support_append_verifier_run_some_iff
    (V₁ : Verifier oSpec Stmt₁ Stmt₂ pSpec₁)
    (V₂ : Verifier oSpec Stmt₂ Stmt₃ pSpec₂)
    (stmt : Stmt₁) (tr : (pSpec₁ ++ₚ pSpec₂).FullTranscript) (out : Stmt₃) :
    some out ∈ support (OptionT.run ((V₁.append V₂).run stmt tr)) ↔
      ∃ mid,
        some mid ∈ support (OptionT.run (V₁.run stmt tr.fst)) ∧
          some out ∈ support (OptionT.run (V₂.run mid tr.snd)) := by
  rw [Verifier.append_run, OptionT.mem_support_run_bind_some_iff]
  constructor
  · rintro ⟨mid, hmid, hout⟩
    rw [OptionT.mem_support_run_bind_some_iff] at hout
    rcases hout with ⟨out', hout', hpure⟩
    have hout_eq : out = out' := by
      simpa [OptionT.run_pure, support_pure, Set.mem_singleton_iff] using hpure
    subst out
    exact ⟨mid,
      (OptionT.mem_support_iff (mx := V₁.run stmt tr.fst) (x := mid)).1 hmid,
      (OptionT.mem_support_iff (mx := V₂.run mid tr.snd) (x := out')).1 hout'⟩
  · rintro ⟨mid, hmid, hout⟩
    refine ⟨mid,
      (OptionT.mem_support_iff (mx := V₁.run stmt tr.fst) (x := mid)).2 hmid,
      ?_⟩
    rw [OptionT.mem_support_run_bind_some_iff]
    refine ⟨out,
      (OptionT.mem_support_iff (mx := V₂.run mid tr.snd) (x := out)).2 hout,
      ?_⟩
    simp [OptionT.run_pure]

variable {Wit₁ Wit₂ Wit₃ : Type}

/-- If both components are support-good, then appending a zero-round trailing component is
support-good. This is the support-containment core of n=0 append perfect-completeness: it avoids any
distributional reordering and reconstructs the component `Reduction.run` support points from the
append support decomposition. -/
theorem append_empty_run_support_good
    {pSpec₂₀ : ProtocolSpec 0}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    [∀ i, SampleableType (pSpec₂₀.Challenge i)]
    {rel₂ : Set (Stmt₂ × Wit₂)} {rel₃ : Set (Stmt₃ × Wit₃)}
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂₀)
    (stmt : Stmt₁) (wit : Wit₁)
    (h₁good :
      ∀ out, out ∈ support (R₁.run stmt wit) →
        (out.2, out.1.2.2) ∈ rel₂ ∧ out.1.2.1 = out.2)
    (h₂good :
      ∀ stmt₂ wit₂, (stmt₂, wit₂) ∈ rel₂ →
        ∀ out, out ∈ support (R₂.run stmt₂ wit₂) →
          (out.2, out.1.2.2) ∈ rel₃ ∧ out.1.2.1 = out.2)
    (out : ((pSpec₁ ++ₚ pSpec₂₀).FullTranscript × Stmt₃ × Wit₃) × Stmt₃)
    (hout : out ∈ support ((R₁.append R₂).run stmt wit)) :
    (out.2, out.1.2.2) ∈ rel₃ ∧ out.1.2.1 = out.2 := by
  rw [run_append_empty] at hout
  rw [OptionT.mem_support_iff] at hout
  simp only [OptionT.run_bind, OptionT.run_pure, Option.elimM] at hout
  rw [mem_support_bind_iff] at hout
  obtain ⟨p1, hp1, hout⟩ := hout
  rcases p1 with _ | pr1
  · simp only [Option.elim_none, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hout
  · simp only [Option.elim_some] at hout
    have hp1' : pr1 ∈ support (R₁.prover.run stmt wit) := by
      change some pr1 ∈ support
        (some <$> (liftM (R₁.prover.run stmt wit) :
          OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)
            (pSpec₁.FullTranscript × Stmt₂ × Wit₂))) at hp1
      rw [support_map] at hp1
      simp only [Set.mem_image, Option.some.injEq] at hp1
      rcases hp1 with ⟨pr1', hpr1', hEq⟩
      have hpr1 :
          pr1' ∈ support
            ((R₁.prover.run stmt wit).liftComp
              (oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)) := by
        simpa [OracleComp.liftComp_eq_liftM] using hpr1'
      have hpr1_base : pr1' ∈ support (R₁.prover.run stmt wit) :=
        OracleComp.mem_support_of_mem_support_liftComp
          (oa := R₁.prover.run stmt wit) (x := pr1') hpr1
      simpa [hEq] using hpr1_base
    rw [mem_support_bind_iff] at hout
    obtain ⟨p2, hp2, hout⟩ := hout
    rcases p2 with _ | pr2
    · simp only [Option.elim_none, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hout
    · simp only [Option.elim_some] at hout
      have hp2' : pr2 ∈ support (R₂.prover.run pr1.2.1 pr1.2.2) := by
        change some pr2 ∈ support
          (some <$> (liftM (R₂.prover.run pr1.2.1 pr1.2.2) :
            OracleComp (oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)
              (pSpec₂₀.FullTranscript × Stmt₃ × Wit₃))) at hp2
        rw [support_map] at hp2
        simp only [Set.mem_image, Option.some.injEq] at hp2
        rcases hp2 with ⟨pr2', hpr2', hEq⟩
        have hpr2 :
            pr2' ∈ support
              ((R₂.prover.run pr1.2.1 pr1.2.2).liftComp
                (oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)) := by
          simpa [OracleComp.liftComp_eq_liftM] using hpr2'
        have hpr2_base : pr2' ∈ support (R₂.prover.run pr1.2.1 pr1.2.2) :=
          OracleComp.mem_support_of_mem_support_liftComp
            (oa := R₂.prover.run pr1.2.1 pr1.2.2) (x := pr2') hpr2
        simpa [hEq] using hpr2_base
      rw [mem_support_bind_iff] at hout
      obtain ⟨vopt, hv, hout⟩ := hout
      rcases vopt with _ | vout
      · simp only [Option.elim_none, support_pure, Set.mem_singleton_iff, reduceCtorEq] at hout
      · simp only [Option.elim_some] at hout
        have hvDirect :
            vout ∈ support
              (OptionT.run
                ((R₁.verifier.append R₂.verifier).run stmt (pr1.1 ++ₜ pr2.1))) := by
          rw [OptionT.run_liftM_run, support_map,
            support_simulateQ_eq_OracleComp_of_superSpec _ _ (fun _ => rfl)] at hv
          simp only [Set.mem_image, Option.some.injEq] at hv
          rcases hv with ⟨vout', hvout', hEq⟩
          simpa [hEq] using hvout'
        rcases vout with _ | stmtOut
        · exfalso
          simp only [Option.getM_none, mem_support_bind_iff] at hout
          rcases hout with ⟨i, hi, hout⟩
          subst i
          simp at hout
        · have hout_eq :
              out = ((pr1.1 ++ₜ pr2.1, pr2.2.1, pr2.2.2), stmtOut) := by
            simp only [Option.getM_some, mem_support_bind_iff] at hout
            rcases hout with ⟨i, hi, hout⟩
            simp only [OptionT.run_pure, support_pure, Set.mem_singleton_iff] at hi
            subst i
            simpa [support_pure] using hout
          have hvSplit :=
            (mem_support_append_verifier_run_some_iff
              (V₁ := R₁.verifier) (V₂ := R₂.verifier)
              (stmt := stmt) (tr := pr1.1 ++ₜ pr2.1) (out := stmtOut)).1 hvDirect
          rcases hvSplit with ⟨mid, hv1, hv2⟩
          have hv1' : some mid ∈ support (OptionT.run (R₁.verifier.run stmt pr1.1)) := by
            simpa [ProtocolSpec.FullTranscript.append_fst] using hv1
          have hv2' : some stmtOut ∈ support (OptionT.run (R₂.verifier.run mid pr2.1)) := by
            simpa [ProtocolSpec.FullTranscript.append_snd] using hv2
          have hR1Run :
              some (((pr1.1, (pr1.2.1, pr1.2.2)), mid)) ∈
                support (OptionT.run (R₁.run stmt wit)) :=
            mem_support_run_of_prover_verifier
              R₁ stmt wit pr1.1 (pr1.2.1, pr1.2.2) mid hp1' hv1'
          have hR1 :
              (((pr1.1, (pr1.2.1, pr1.2.2)), mid)) ∈
                support (R₁.run stmt wit) :=
            (OptionT.mem_support_iff
              (mx := R₁.run stmt wit)
              (x := (((pr1.1, (pr1.2.1, pr1.2.2)), mid)))).2 hR1Run
          have h1res := h₁good _ hR1
          have hstmt : pr1.2.1 = mid := by
            simpa using h1res.2
          have hrel2 : (pr1.2.1, pr1.2.2) ∈ rel₂ := by
            rw [hstmt]
            exact h1res.1
          have hv2'' :
              some stmtOut ∈ support (OptionT.run (R₂.verifier.run pr1.2.1 pr2.1)) := by
            rw [hstmt]
            exact hv2'
          have hR2Run :
              some (((pr2.1, (pr2.2.1, pr2.2.2)), stmtOut)) ∈
                support (OptionT.run (R₂.run pr1.2.1 pr1.2.2)) :=
            mem_support_run_of_prover_verifier
              R₂ pr1.2.1 pr1.2.2 pr2.1 (pr2.2.1, pr2.2.2) stmtOut hp2' hv2''
          have hR2 :
              (((pr2.1, (pr2.2.1, pr2.2.2)), stmtOut)) ∈
                support (R₂.run pr1.2.1 pr1.2.2) :=
            (OptionT.mem_support_iff
              (mx := R₂.run pr1.2.1 pr1.2.2)
              (x := (((pr2.1, (pr2.2.1, pr2.2.2)), stmtOut)))).2 hR2Run
          have h2res := h₂good pr1.2.1 pr1.2.2 hrel2 _ hR2
          simpa [hout_eq] using h2res

/-- If the first component run and every related second component run are failure-free, then
appending a zero-round trailing component is failure-free. The relation bridge is needed to feed
the prover output of the first component into the no-failure hypothesis for the second component. -/
theorem append_empty_run_neverFail
    {pSpec₂₀ : ProtocolSpec 0}
    [∀ i, SampleableType (pSpec₁.Challenge i)]
    [∀ i, SampleableType (pSpec₂₀.Challenge i)]
    [(oSpec + [pSpec₁.Challenge]ₒ).Fintype] [(oSpec + [pSpec₁.Challenge]ₒ).Inhabited]
    [(oSpec + [pSpec₂₀.Challenge]ₒ).Fintype] [(oSpec + [pSpec₂₀.Challenge]ₒ).Inhabited]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ).Fintype]
    [(oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ).Inhabited]
    {rel₂ : Set (Stmt₂ × Wit₂)}
    (R₁ : Reduction oSpec Stmt₁ Wit₁ Stmt₂ Wit₂ pSpec₁)
    (R₂ : Reduction oSpec Stmt₂ Wit₂ Stmt₃ Wit₃ pSpec₂₀)
    (stmt : Stmt₁) (wit : Wit₁)
    (h₁nf : NeverFail (R₁.run stmt wit))
    (h₁good :
      ∀ out, out ∈ support (R₁.run stmt wit) →
        (out.2, out.1.2.2) ∈ rel₂ ∧ out.1.2.1 = out.2)
    (h₂nf : ∀ stmt₂ wit₂, (stmt₂, wit₂) ∈ rel₂ → NeverFail (R₂.run stmt₂ wit₂)) :
    NeverFail ((R₁.append R₂).run stmt wit) := by
  rw [run_append_empty]
  simp only [HasEvalSPMF.neverFail_bind_iff, OptionT.support_liftM]
  constructor
  · exact NeverFail.mk (by
      rw [OptionT.probFailure_liftM]
      exact HasEvalPMF.probFailure_eq_zero _)
  · intro pr1 hpr1Lift
    have hpr1 : pr1 ∈ support (R₁.prover.run stmt wit) := by
      have hpr1Lift' :
          pr1 ∈ support
            ((R₁.prover.run stmt wit).liftComp
              (oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)) := by
        simpa [OracleComp.liftComp_eq_liftM] using hpr1Lift
      exact OracleComp.mem_support_of_mem_support_liftComp
        (oa := R₁.prover.run stmt wit) (x := pr1) hpr1Lift'
    have hrel₂ : (pr1.2.1, pr1.2.2) ∈ rel₂ :=
      prover_support_rel_of_run_neverFail_good R₁ stmt wit h₁nf h₁good pr1 hpr1
    have h₂nf_pr1 : NeverFail (R₂.run pr1.2.1 pr1.2.2) :=
      h₂nf pr1.2.1 pr1.2.2 hrel₂
    constructor
    · exact NeverFail.mk (by
        rw [OptionT.probFailure_liftM]
        exact HasEvalPMF.probFailure_eq_zero _)
    · intro pr2 hpr2Lift
      have hpr2 : pr2 ∈ support (R₂.prover.run pr1.2.1 pr1.2.2) := by
        have hpr2Lift' :
            pr2 ∈ support
              ((R₂.prover.run pr1.2.1 pr1.2.2).liftComp
                (oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)) := by
          simpa [OracleComp.liftComp_eq_liftM] using hpr2Lift
        exact OracleComp.mem_support_of_mem_support_liftComp
          (oa := R₂.prover.run pr1.2.1 pr1.2.2) (x := pr2) hpr2Lift'
      constructor
      · exact NeverFail.mk (by
          exact probFailure_liftM_oracleComp_to_optionT_eq_zero
            (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)
            (((R₁.verifier.append R₂.verifier).run stmt (pr1.1 ++ₜ pr2.1)).run))
      · intro vopt hvopt
        cases vopt with
        | none =>
            exfalso
            have hvDirect :
                none ∈ support (OptionT.run
                  ((R₁.verifier.append R₂.verifier).run stmt (pr1.1 ++ₜ pr2.1))) := by
              exact mem_support_of_mem_support_liftM_oracleComp_to_optionT
                (superSpec := oSpec + [(pSpec₁ ++ₚ pSpec₂₀).Challenge]ₒ)
                (((R₁.verifier.append R₂.verifier).run stmt
                  (pr1.1 ++ₜ pr2.1)).run) hvopt
            rw [Verifier.append_run, OptionT.run_bind, Option.elimM,
              mem_support_bind_iff] at hvDirect
            rcases hvDirect with ⟨v₁, hv₁, hv₂⟩
            cases v₁ with
            | none =>
                have hv₁' :
                    none ∈ support (OptionT.run (R₁.verifier.run stmt pr1.1)) := by
                  simpa [ProtocolSpec.FullTranscript.append_fst] using hv₁
                exact (verifier_none_not_mem_of_run_neverFail
                  R₁ stmt wit h₁nf pr1 hpr1) hv₁'
            | some mid =>
                have hv₁' :
                    some mid ∈ support (OptionT.run (R₁.verifier.run stmt pr1.1)) := by
                  simpa [ProtocolSpec.FullTranscript.append_fst] using hv₁
                have hmid :=
                  verifier_support_good_of_run_support_good
                    R₁ stmt wit h₁good pr1 hpr1 mid hv₁'
                have hstmt : pr1.2.1 = mid := hmid.2
                simp only [Option.elim_some] at hv₂
                have hv₂' :
                    none ∈ support (OptionT.run (R₂.verifier.run pr1.2.1 pr2.1)) := by
                  simpa [ProtocolSpec.FullTranscript.append_snd, hstmt] using hv₂
                exact (verifier_none_not_mem_of_run_neverFail
                  R₂ pr1.2.1 pr1.2.2 h₂nf_pr1 pr2 hpr2) hv₂'
        | some stmtOut =>
            constructor
            · simp [Option.getM]
            · intro out hout
              exact inferInstance

end Reduction
