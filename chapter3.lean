/-
  def 1.
  a *BNF grammar* is based on three sets:
    · terminals: exactly match the input character
    · non terminals: sets of strings
    · rules: define relations between strings and monterminals

  def 2.
  we give an *inductive definition* of a set of terms:
  the set of terms is the smallest set `T`s.t.
    · {true, false, 0} ⊆ T
    · if t₁ ∈ T then {succ t₁, pred t₁, iszero t₁} ⊆ T
    · if t₁, t₂, t₃ ∈ T then ite t₁ t₂ t₃ ⊆ T


  def 3.
  we can define the same set starting from the *inference rules*, where:
  axioms:
    · true ∈ T
    · false ∈ T
    · 0 ∈ T
  rules:
      t₁ ∈ T          t₁ ∈ T            t₁ ∈ T
    -----------     -----------     -------------
    succ t₁ ∈ T     pred t₁ ∈ T     iszero t₁ ∈ T

              t₁ ∈ T  t₂ ∈ T  t₃ ∈ T
              ----------------------
                 ite t₁ t₂ t₃ ∈ T
    these rules say that if we can establish the upper terms, we can derive the lower term.

    def 4.
    we can give a *concrete definition* of terms:
    for each natural number `i`, define a set Si:
      S₀ = ∅
      S (i+1) = {true, false, 0}
                ∪ {succ t₁, pred t₁, iszero t₁ | t₁ ∈ Si}
                ∪ { ite t₁ t₂ t₃ | t₁, t₂ t₃ ∈ Si}
    and S = ∪i Si

    because of the fundamental difference between set theory and type theory, it's very hard to
    reason about sets in Lean.

    def 5.
    there are different types of induction proofs for natural numbers:
    · *complete induction*
      given a predicate P on Nat,
        if given P(i) for all i < n we can show P(n),
      then P(n) holds ∀ n
    · *ordinary induction*
      given a predicate on Nat,
        if P(0) and ∀i, P(i) → P(i+1)
      then P(n) holds ∀ n
    · *lexicographic induction*
      given a predicate on Nat × Nat,
        if ∀ (m,n) ∈ Nat, given ∀ (m',n') < (m,n), P(m',n') we can show P(m,n)
      then P(m,n) holds ∀ m,n

    def 6.
    we can define induction on terms as well:
    · *induction on depth*
      if ∀ s
        given P(r) ∀ r s.t. depth(r) < depth(s) we can show P(s)
      then P(s) holds ∀ s
    · *induction on size*
      if ∀ s
        given P(r) ∀ r s.t. size(r) < size(s) we can show P(s)
      then P(s) holds ∀ s
    · *structural induction*
      if ∀ s
        given P(r) ∀ immediate subterms r of s we can show P(s)
      then P(s) holds ∀ s

    def 7.
    we can define semantics in different ways:
    · *operational semantics*
        specifies the behavior of a program by building
        an abstract machine for it states/transitions
    · *denotational semantics*
        the meaning of a term is a mathematical object,
        this model thus requires defining the program's semantic domains and
        an interpretation function
    · *axiomatic semantics*
        the meaning of a term is what can be proven about it
-/

-- Untyped Booleans Language

-- terms

namespace myFirstType
open myFirstType

inductive t where
  | True : t
  | False : t
  | ite : t → t → t → t

-- values
inductive tv : t → Prop where
  | True : tv t.True
  | False : tv t.False

#reduce sizeOf t.True -- 1
#reduce sizeOf t.False -- 1
#reduce sizeOf (t.ite t.True t.True t.False) -- 4

-- evaluation, defined as an *inductive predicate*
inductive t.EvaluatesTo : t → t → Prop
  | EvaluatesToTrue {x l r} (hx : x = .ite .True l r) : t.EvaluatesTo x l
  | EvaluatesToFalse {x l r} (hx : x = .ite .False l r) : t.EvaluatesTo x r
  | EvaluatesToIf{x y l r cd cd' } (hx : x = .ite cd l r) (hy : y = .ite cd' l r) : (h : t.EvaluatesTo cd cd') → t.EvaluatesTo x y

-- reduceCtorEq is an axiom in lean that, when creating an inductive type, none of the constructores are equal to each other.
#check t.noConfusion
theorem foo : t.True ≠ t.False := by
  simp only [ne_eq, reduceCtorEq, not_false_eq_true]

-- we first prove some inversion lemmas about what can (not) evaluate from what

theorem TrueCantEvaluate (x : t): ¬ t.True.EvaluatesTo x := by
  intro hcontra
  cases hcontra
  case EvaluatesToTrue r hx => simp only [reduceCtorEq] at hx
  case EvaluatesToFalse l hx => simp only [reduceCtorEq] at hx
  case EvaluatesToIf l r cd cd' h hx hy => simp only [reduceCtorEq] at hx

theorem FalseCantEvaluate (x : t): ¬ t.False.EvaluatesTo x := by
  intro hcontra
  cases hcontra
  case EvaluatesToTrue r hx => simp only [reduceCtorEq] at hx
  case EvaluatesToFalse l hx => simp only [reduceCtorEq] at hx
  case EvaluatesToIf l r cd cd' h hx hy => simp only [reduceCtorEq] at hx

/-
  theorem 3.5.4: determinacy of one-step evaluation
  if t → t' and t → t'' then t' = t''
  (note that '→' = 'EvaluatesTo')
-/
theorem OneStepDeterminacy (a b c : t) (hab : t.EvaluatesTo a b) (hac : t.EvaluatesTo a c) : b = c := by
  revert c
  induction hab
  case EvaluatesToTrue x l r hx =>
    intros c hac
    cases hac
    case EvaluatesToTrue r' hx' =>
      subst hx
      simp only [t.ite.injEq, true_and] at hx'
      simp only [hx']
    case EvaluatesToFalse l' hx' =>
      -- contradiction:
      -- hx : x = t.True.ite l r
      -- hx' : x = t.False.ite l' c
      subst hx
      simp only [t.ite.injEq, reduceCtorEq, false_and] at hx'
    case EvaluatesToIf l' r' cd cd' hcd hx' hc =>
      subst hx
      simp only [t.ite.injEq] at hx'
      obtain ⟨h1, h2⟩ := hx'
      subst h1
      contradiction
  case EvaluatesToFalse x l r hx =>
    intros c hac
    cases hac
    case EvaluatesToTrue r' hx' =>
      -- contradiction:
      -- hx : x = t.True.ite l r
      -- hx' : x = t.False.ite l' c
      subst hx
      simp only [t.ite.injEq, reduceCtorEq, false_and] at hx'
    case EvaluatesToFalse l' hx' =>
      subst hx
      simp only [t.ite.injEq, true_and] at hx'
      simp only [hx']
    case EvaluatesToIf l' r' cd cd' hcd hx' hc =>
      subst hx
      simp only [t.ite.injEq] at hx'
      obtain ⟨h1, h2⟩ := hx'
      subst h1
      contradiction
  case EvaluatesToIf x y l r cd cd' hx hx' hy ih  =>
    intros c hac
    cases hac
    case EvaluatesToTrue k hk =>
      subst hk
      simp at hx
      obtain ⟨h1,h2,h3⟩ := hx
      subst h1
      contradiction
    case EvaluatesToFalse k hk =>
      subst hk
      simp at hx
      obtain ⟨h1,h2,h3⟩ := hx
      subst h1
      contradiction
    case EvaluatesToIf lx rx cdx cd'x hcdx hcdx' hc =>
      subst hx
      simp only [t.ite.injEq] at hcdx'
      obtain ⟨h1,h2,h3⟩ := hcdx'
      subst h1
      specialize ih cd'x hcdx
      subst ih
      subst hx' hc h2 h3
      rfl


/- def 8.
   a term t is in normal form if no evaluation rule applies to it
-/
def NormalForm (tt : t) := ¬ ∃ tt', t.EvaluatesTo tt tt'

/- theorem 3.5.7 : Every value is in normal form -/
theorem ValueIsInNF (v : t) (h : tv v) : NormalForm v := by
  -- note that this theorem always applies to arithmetic expressions, in any language (e.g. the next one)
  unfold NormalForm
  intro h' -- by contradiction, suppose ∃ tt such that v → tt
  obtain ⟨tt, htt⟩ := h'
  cases h -- by h, we know that v is eithet t.True or t.False, and no evaluation rule exists for these elements
  · case intro.True =>
    cases htt
    · case EvaluatesToTrue r hr => simp at hr
    · case EvaluatesToFalse l hl => simp at hl
    · case EvaluatesToIf l r cd cd' h hx hy => cases hx
  · case intro.False =>
    cases htt
    · case EvaluatesToTrue r hr => simp at hr
    · case EvaluatesToFalse l hl => simp at hl
    · case EvaluatesToIf l r cd cd' h hx hy => cases hx

/--
  Recall the principle of structural induction:
  if for each term `s`
    given `P(r)` for each subterm `r` of `s` we can show `P(s)`
  then `P(s)` holds for all `s`.
-/

theorem IteNotTv {cd l r : t} : ¬ tv (t.ite cd l r) := by
  intro h; cases h

/- theorem 3.5.8 : If t is in normal form, then t is a value -/
theorem NFImpValue (v : t) (h : NormalForm v) : tv v := by
  induction v
  · -- true is indeed a value!
    case True => exact tv.True
  · case False => exact tv.False
  · case ite cd l r ihcd ihl ihr =>
    -- the inductive hypothesis applies to each sub-term
    have hiteNotTv := IteNotTv (cd := cd) (l := l) (r := r)
    cases cd
    · -- can't be in normal form, since a rule applies!
      case True =>
      unfold NormalForm at h
      simp only [not_exists] at h
      specialize h l -- if ∀ (x : t), ¬(t.True.ite l r).EvaluatesTo x, then we can specialize with x = l: ¬(t.True.ite l r).EvaluatesTo l
      have := t.EvaluatesTo.EvaluatesToTrue (r := r) (l := l) (x := t.True.ite l r) (by rfl) -- however, this rules exists!
      contradiction
    · -- same as above
      case False =>
      unfold NormalForm at h
      simp only [not_exists] at h
      specialize h r
      have := t.EvaluatesTo.EvaluatesToFalse (r := r) (l := l) (x := t.False.ite l r) (by rfl)
      contradiction
    · -- v = ite cd l r, cd = ite cd' l' r', i.e., v = ite (ite cd' l' r') l r
      -- cd is not a value and by the inductive hp it is also not nf, i.e., ∃ tt' : cd → tt'
      -- however, if this is the case, then (v = ite cd l r) [EvaluatesToIf]→ (ite tt' l r) (this is the only viable rule!)
      -- and t is thus not nf either
      case ite cd' l' r' =>
      have hIteNottv := IteNotTv (cd := cd') (l := l') (r := r')
      simp only [NormalForm, not_exists, hIteNottv, imp_false, Classical.not_forall,
        Classical.not_not] at ihcd h
      obtain ⟨x, hx⟩ := ihcd
      have := t.EvaluatesTo.EvaluatesToIf (cd := cd'.ite l' r') (cd' := x) (l := l) (r := r) (x := (cd'.ite l' r').ite l r ) (y := x.ite l r)
      simp_all only [imp_false, not_true_eq_false]

/- 3.5.13: if we add a new rule things could go wild and the theorems might stop holding. -/

inductive t.FunnyEvaluatesTo : t → t → Prop
  | EvaluatesToTrue: t.FunnyEvaluatesTo (.ite .True l r) l
  | EvaluatesToFalse: t.FunnyEvaluatesTo (.ite .False l r) r
  | EvaluatesToIf : (h : t.FunnyEvaluatesTo cd cd') → t.FunnyEvaluatesTo (.ite cd l r) (.ite cd' l r)
  | EvaluatesToFunny : t.FunnyEvaluatesTo (.ite .True l r) r

-- one expression can evaluate to two different expressions
theorem funnyEval₁ : (t.True.ite l r).FunnyEvaluatesTo l := t.FunnyEvaluatesTo.EvaluatesToTrue (l := l) (r := r)
theorem funnyEval₂ : (t.True.ite l r).FunnyEvaluatesTo r := t.FunnyEvaluatesTo.EvaluatesToFunny (l := l) (r := r)

end myFirstType

namespace mySecondType

/--  Untyped Booleans and Naturals: we introduce a new type t' which contains either elements from t (booleans) or natural numbers -/

inductive t where
  | True : t
  | False : t
  | ite : t → t → t → t
  | zero : t
  | succ : t → t
  | pred : t → t
  | iszero : t → t
  deriving Repr

inductive tv : t → Prop where
  | True : tv t.True
  | False : tv t.False

inductive nv : t → Prop where
  | zero : nv t.zero
  | succ n : nv n → nv (t.succ n)

inductive t.EvaluatesTo : t → t → Prop
| -- ite true l r → l
  EvaluatesToTrue {l r : t} : t.EvaluatesTo (True.ite l r) l
| -- ite false l r → r
  EvaluatesToFalse {l r : t} : t.EvaluatesTo (False.ite l r) r
| -- (cd → cd') → (ite cd l r → ite cd' l r)
  EvaluatesToIf (h : t.EvaluatesTo cd cd') : t.EvaluatesTo (t.ite cd l r) (t.ite cd' l r)
| -- (v → v') → (succ v → succ v')
  EvaluatesToSucc {v v' : t} (h : EvaluatesTo v v') : (EvaluatesTo (t.succ v) (t.succ v'))
| -- pred 0 = 0
  EvaluatesToZero : t.EvaluatesTo (t.pred t.zero) (t.zero)
| -- pred (succ nv) → nv
  EvaluatesToPredSucc (h : nv v) : t.EvaluatesTo (t.pred (t.succ v))  (v)
| -- (v → v') → (pred v → pred v')
  EvaluatesToPred (h : t.EvaluatesTo v v') : t.EvaluatesTo (t.pred v) (t.pred v')
| -- iszero 0 → true
  EvaluatesToIsZeroZero : t.EvaluatesTo (t.iszero t.zero) (t.True)
| -- iszero (succ nv) → false
  EvaluatesToIsZeroSucc (h : nv v) : t.EvaluatesTo (t.iszero (t.succ v)) (t.False)
| -- (tt → tt) → (iszero tt → iszero tt)
  EvaluatesToIsZero (h : t.EvaluatesTo tt tt') : t.EvaluatesTo (t.iszero tt) (t.iszero tt')

/-- Excursus on inductive predicates and relations based on a set-theory-perspective,
  from https://link.springer.com/chapter/10.1007/3-540-61780-9_64

  Inductive definitions of sets rely on *constructors*: an element belongs to the set inductively
  defined iff it has been generated according to the rules.

  An inductive relation is usually defined with the smallest set closed under a set of rules and
  is formally the least fixed point of a monotone relation over a complete lattice (cfr. Knaster Tarski).

  For example, consider the set of natural numbers built on two rules:
  1. 0 ∈ Nat
  2. if n ∈ Nat then (S n) ∈ Nat

  And the relations:
  1. ( ) [≤0]→ 0 ≤ n
  2. (n ≤ m) [≤s]→ (S n) ≤ (S m)

  More in general: let P be a property about natural numbers and suppose we want to prove:
  prop: ∀ n, m ∈ Nat, if (S n) ≤ m then (P n m)
  then we need to e.g. use:
  fact 1: m = (S m₀)
  fact 2: n ≤ m₀
  for some m₀ ∈ Nat.
  This is true because the only constructor whose conclusion matches (S n) ≤ m is [≤s].
  Using these facts is called "doing *inversion*" on the instance (S n) ≤ m (prop).

  The *inversion principle* requires us to state that:
  inv: if (S n) ≤ m then ∃ m₀ ∈ Nat s.t. m = (S m₀) ∧ n ≤ m₀

  Consider:
  prop: (S n) ≤ 0 is false
  i.e. a proof of prop can't be built with the given rules.

  In brief, inversion requires finding out the assumptions and structural conditions under
  which an instance we're trying to prove can be derived.
  Inversion lemmas state that "if an evaluation of this form holds, then there must be something
  that makes the evaluation hold".

  exercise 3.5.14:
  Given the set of elements in t', we want to prove the determinacy of the evaluation rules
  and before doing that we will write down some inversion rules, to make the subsequent
  overall proof smoother.
  To understand which inversion lemmas we need, let's consider
  prop: (hab : t'.EvaluatesTo a b) (hac : t'.EvaluatesTo a c) : b = c
  and ask ourselves: what conditions hold for b and c if prop holds?
  And we infer that:
  1. there cannot be an evaluation from `True` or `False`.
  1. there cannot be an evaluation from `t'.zero`.
  2. a numerical value nv can not evaluate to a generic t.
-/

-- it is not true that given any t: True → t
theorem NotTrueEvalTo (v : t) : ¬ t.EvaluatesTo t.True v := by
  intro h -- suppose by hp. we have t'.EvaluatesTo t'.True t
  cases h -- then we evaluate the cases by which this hypothesi can be true: none!

-- it is not true that given any t: False → t
theorem NotFalseEvalTo (v : t) : ¬ t.EvaluatesTo t.False v := by
  intro h -- suppose by hp. we have t.EvaluatesTo t.False t
  cases h -- then we evaluate the cases by which this hypothesi can be true: none!

-- it is not true that given any t: zero → t
theorem NotZeroEvalTo (v : t) : ¬ t.EvaluatesTo t.zero v := by
  intro h -- suppose by hp. we have t.EvaluatesTo t.zero t
  cases h -- then we evaluate the cases by which this hypothesi can be true: none!

-- it is not true that a v : t such that ∃ n : nv v can evaluate to a generic t
theorem NotNvEvalTo (v u : t) (n : nv v) : ¬ t.EvaluatesTo v u := by
  induction n generalizing u
  · -- n = nv t'.zero, v' = t'.zero
    case zero => exact NotZeroEvalTo u
  · -- n = succ n' = nv (t.succ n'), v' = t.succ n'
    -- with ihn : ∀ (t : t), ¬v'.EvaluatesTo t
    -- and the goal will require to demonstrate ¬v'.succ.EvaluatesTo t
    case succ v' n ihn =>
    intro h' -- suppose we can actually have an evaluation of (t.succ v') → t
    cases h' -- this can only happen by (t.succ v')[EvaluatesToSucc]→ t
    · case EvaluatesToSucc t₁' h =>
      -- note that the rule says that given (h : EvaluatesTo t₁ t₁') then (EvaluatesTo (t.succ t₁) (t.succ t₁'))
      -- we thus suppose there exists a t₁' such that v' → t₁', by which we conclude (t.succ v') → (t.succ t₁')
      -- we need to prove that the inductive hypothesis still holds: ¬ v' → (succ t₁')
      -- we apply the inductive hypothesis ¬v'.EvaluatesTo t with t = t₁' and given the evaluation in h.
      exact ihn t₁' h

theorem OneStepDeterminacy' (a b c : t) (hab : t.EvaluatesTo a b) (hac : t.EvaluatesTo a c) : b = c := by
  -- we use induction on the derivation rule hab
  induction hab generalizing c -- same as "revert c"
  · -- a [EvaluatesToTrue]→ b
    -- i.e., a = ite True l r
    case EvaluatesToTrue l r =>
    cases hac
    · -- a [EvaluatesToTrue]→ c
      case EvaluatesToTrue => rfl -- same rule
    · -- a [EvaluatesToIf]→ c
      -- i.e., given (h : t'.EvaluatesTo True cd') then t'.EvaluatesTo (ite True l r) (ite cd' l r)
      -- with a = ite True l r according to the first case and c = ite cd' l r
      case EvaluatesToIf c hTrueEvalTo =>
        -- does not exist, as per the first inversion lemma:
        -- we show that the hypotheses are contradictory (showing that the
        -- contrary of NotTrueEvalTo is absurd)
        exact absurd hTrueEvalTo (NotTrueEvalTo _)
  · -- a [EvaluatesToFalse]→ b
    -- i.e., a = ite False l r
    -- this case works exactly as the previous one
    case EvaluatesToFalse l r =>
    cases hac
    · -- a [EvaluatesToFalse]→ c
      case EvaluatesToFalse => rfl -- same rule
    · -- a [EvaluatesToIf]→ c
      -- i.e., given (h : t'.EvaluatesTo False cd') then t'.EvaluatesTo (ite False l r) (ite cd' l r)
      -- with a = ite False l r according to the first case and c = ite cd' l r
      case EvaluatesToIf c hTrueEvalTo =>
        -- does not exist, as per the second inversion lemma:
        -- we show that the hypotheses are contradictory (showing that the
        -- contrary of NotFalseEvalTo is absurd)
        exact absurd hTrueEvalTo (NotFalseEvalTo _)
  · -- a [EvaluatesToIf]→ b
    case EvaluatesToIf cd cd' l r hCdEvalToCd ihcond =>
    -- the inductive hypothesis applies the theorem statement
    -- to the subterm involved in the hypothesis this evaluation
    -- rules relies on
    cases hac
    · -- a [EvaluatesToTrue]→ c
      case EvaluatesToTrue => -- absurd as above
      exact absurd hCdEvalToCd (NotTrueEvalTo _)
    · -- a [EvaluatesToFalse]→ c
      case EvaluatesToFalse => -- absurd as above
      exact absurd hCdEvalToCd (NotFalseEvalTo _)
    · -- a [EvaluatesToIf]→ c
      -- i.e., given a = ite cd l r and hab : given (cd → cd') then (ite cd l r) → (cd' l r)
      -- we suppose
      -- hac : given (cd → cd'') then (ite cd l r) → (cd'' l r)
      -- and thus the goal b = c becomes:
      -- (cond₂ l r) = (cond' l r)
      case EvaluatesToIf cd'' hCdEvalToCd =>
      -- we exploit the congruence in functions and applications and construct
      exact congrFun (congrFun (congrArg t.ite (ihcond cd'' hCdEvalToCd)) l) r
  · -- a [EvaluatesToSucc]→ b
    -- i.e. a = succ v and hab : given (v → v') then (succ v) → (succ v')
    -- with a = succ v and b = succ v'
    case EvaluatesToSucc v v' hvEvalTov' ih =>
    cases hac
    · -- i.e., given a = succ v and hab : given (v → v') then (succ v) → (succ v')
      -- we suppose
      -- hac : given (v → v'') then (succ v) → (succ v'')
      -- and the goal b = c becomes:
      -- succ v' = succ v''
      case EvaluatesToSucc v'' hvEvalTov'' =>
      exact congrArg t.succ (ih v'' hvEvalTov'')
  · -- a [EvaluatesToZero]→ b
    -- i.e. a = zero
    case EvaluatesToZero =>
    cases hac
    · -- given a = zero, if this rule applies to it thus hab = hac
      case EvaluatesToZero => rfl
    · -- we now suppose a [EvaluatesToPred]→ b
      -- i.e. hab : given (v → v') then (pred v) → (pred v')
      -- assuming that a = pred v = zero
      -- this rule requires us to show zero → v', which is absurd
      case EvaluatesToPred v' hZeroEvalTo =>
      exact absurd hZeroEvalTo (NotZeroEvalTo _)
  · -- a [EvaluatesToPredSucc] → b
    -- i.e. hab : a = pred (succ v) and hab : pred (succ v) → v given that v has a numerical value nv v
    -- and thus b = v
    case EvaluatesToPredSucc v hNv =>
    cases hac
    · case EvaluatesToPredSucc => rfl
    · -- a [EvaluatesToPred]→ c
      -- i.e. hac : given ((succ v) → v') then (pred (succ v)) → (pred v')
      -- and thus b = c becomes
      -- v = pred v'
      case EvaluatesToPred v' hvEvalTov' =>
      -- we construct the numerical value of succ v
      -- using the constructors of nv, v and its numerical value
      have hnv : nv (t.succ v) := nv.succ v hNv
      -- and we exploit the fact that the numerical value can not be evaluated to anything
      exact absurd hvEvalTov' (NotNvEvalTo _ _ hnv)
  · -- a [EvaluatesToPred] → b
    -- i.e. hab : a = pred v and hab : given (v → v') then (pred v) → (pred v')
    case EvaluatesToPred v v' hvEvalTov' ih =>
    cases hac
    · -- a [EvaluatesToZero]→ c
      -- i.e. hac : (pred zero) → zero in hab, which would rely on zero → v', which is absurd
      -- as zero does not evaluate to anything
      case EvaluatesToZero =>
      exact absurd hvEvalTov' (NotZeroEvalTo v')
    · -- a [EvaluatesToPredSucc]→ c
      -- i.e. hac : a = (pred (succ _)) and (pred (succ _)) → c,
      -- which becomes succ c → v' in the hypotheses hab introduces
      -- the goal b = c becomes
      -- pred v' = c
      case EvaluatesToPredSucc hnv' =>
      -- we use the constructor of nv to
      have hnv' : nv (t.succ c) := nv.succ c hnv'
      -- no evaluation rule applies to numerical values, i.e., hvEvalTov' yields an absurd
      -- given the construction of hnv'
      exact absurd hvEvalTov' (NotNvEvalTo _ _ hnv')
    · -- a [EvaluatesToPred]→ c
      -- i.e. hac : a = (pred v) and (pred v) → (pred v''),
      -- which relies on v → v''
      -- the goal b = c becomes
      -- pred v' = pred v'', we use the inductive hypothesis
      case EvaluatesToPred v'' hvEvalTov'' =>
      exact congrArg t.pred (ih v'' hvEvalTov'')
  · -- a [EvaluatesToIsZeroZero]→ b
    -- i.e. hab : (iszero zero) → True and thus a = iszero zero, b = True
    case EvaluatesToIsZeroZero =>
    cases hac
    · case EvaluatesToIsZeroZero => rfl
    · -- a [EvaluatesToIsZero]→ c
      -- i.e. hac : given tt → tt' then iszero tt → iszero tt'
      -- however, a = iszero zero, and thus hac becomes:
      -- given zero → tt then iszero zero → iszero tt', which is absurd
      -- according to the inversion lemmas.
      case EvaluatesToIsZero hZeroEvalTott' =>
      exact absurd hZeroEvalTott' (NotZeroEvalTo _)
  · -- a [EvaluatesToIsZeroSucc]→ b
    -- i.e. given a v with numerical value nv v, then iszero (succ v) → false
    -- with a = iszero (succ v) and b = false
    case EvaluatesToIsZeroSucc v hNv =>
    cases hac
    · case EvaluatesToIsZeroSucc => rfl
    · -- a [EvaluatesToIsZero]→ c
      -- i.e. hac : given (succ v) → v'' then (iszero (succ v)) → (iszero v'') remembering that a = iszero (succ v) from hab
      -- the goal b = c thus becomes
      -- false = iszero v''
      case EvaluatesToIsZero  hvsuccEvalTov'' =>
      -- we construct the numerical value of succ v
      have hNvSucc : nv (t.succ v) := nv.succ v hNv
      -- and we show that the derivation (succ v) → v'' is absurd, since
      exact absurd hvsuccEvalTov'' (NotNvEvalTo _ _ hNvSucc)
  · -- a [EvaluatesToIsZero]→ b
    -- i.e. hab : given tt → tt' then (iszero tt) → (iszero tt')
    -- with a = iszero tt and b = iszero tt'
    case EvaluatesToIsZero tt httEvalTott' ih =>
    cases hac
    · -- a [EvaluatesToIsZeroZero]→ c
      -- i.e. hac : (iszero zero) → true however, a = iszero tt from hab,
      -- and if a = iszero zero in hab we would have zero → tt' in httEvalTott', which is absurd
      -- since zero can't evaluate to tt'
      case EvaluatesToIsZeroZero =>
      exact absurd httEvalTott' (NotZeroEvalTo _)
    · -- a [EvaluatesToIsZeroSucc]→ c
      -- i.e. hac : given a numerical value nv v, then (iszero (succ v)) → false
      -- with a = iszero (succ v). in hab, this would require iszero (succ v) → iszero tt'
      -- and in particular succ v → tt'
      case EvaluatesToIsZeroSucc v hNv =>
      -- we construct the numerical value for succ v
      have hNvSucc : nv (t.succ v) := nv.succ v hNv
      -- hypothesis httEvalTott' is absurd, since it supposes succ v → tt'
      exact absurd httEvalTott' (NotNvEvalTo _ _ hNvSucc)
    · -- a [EvaluatesToIsZero]→ c
      -- i.e. given tt → tt'' then (iszero tt) → (iszero tt'')
      -- with hac : a = iszero tt and c = iszero tt''
      -- the goal b = c thus becomes
      -- iszero tt' = iszero tt'', we apply the inductive hypothesis
      case EvaluatesToIsZero tt'' httEvalTott' =>
      exact congrArg t.iszero (ih tt'' httEvalTott')

/- def 3.5.9 a closed term is *stuck* if it is in normal form, but not a value -/

def NormalForm (tt : t) := ¬ ∃ tt', t.EvaluatesTo tt tt'

def isStuck (v : t) := (¬ nv v) ∧ (¬ tv v) ∧ NormalForm v

end mySecondType

namespace myThirdType

open myThirdType

/- 3.5.16: we enrich the semantics with a new term `wrong`, to formalize meaningless states and
  introduce rules that generate this term every time the semantics gets stuck. -/

inductive t where
  | True : t
  | False : t
  | ite : t → t → t → t
  | zero : t
  | succ : t → t
  | pred : t → t
  | iszero : t → t
  | wrong : t
  deriving Repr

-- values
inductive tv : t → Prop where
  | True : tv t.True
  | False : tv t.False

inductive nv : t → Prop where
  | zero : nv (t.zero)
  | succ n : nv n → nv (t.succ n)

inductive badNat : t → Prop where
  | wrong : badNat t.wrong
  | badTv : tv x → badNat x

inductive badBool : t →  Prop  where
  | wrong : badBool t.wrong
  -- | badBoolZero : badBool t.zero
  -- | badBoolNvSucc n : badBool n → badBool (t.succ n) note that this allows succ wrong!
  | badNv : nv x → badBool x

inductive t.AugmentedEvaluatesTo : t → t → Prop
| -- ite true l r → l
  EvaluatesToTrue {l r : t} : t.AugmentedEvaluatesTo (True.ite l r) l
| -- ite false l r → r
  EvaluatesToFalse {l r : t} : t.AugmentedEvaluatesTo (False.ite l r) r
| -- (cd → cd') → (ite cd l r → ite cd' l r)
  EvaluatesToIf (h : t.AugmentedEvaluatesTo cd cd')  : t.AugmentedEvaluatesTo (cd.ite l r) (cd'.ite l r)
| -- (v → v') → (succ v → succ v')
  EvaluatesToSucc {v v' : t} (h : AugmentedEvaluatesTo v v') : (AugmentedEvaluatesTo (t.succ v) (t.succ v'))
| -- pred 0 = 0
  EvaluatesToZero : t.AugmentedEvaluatesTo (t.pred t.zero) (t.zero)
| -- pred (succ nv) → nv
  EvaluatesToPredSucc (h : nv v) : t.AugmentedEvaluatesTo (t.pred (t.succ v))  (v)
| -- (v → v') → (pred v → pred v')
  EvaluatesToPred (h : t.AugmentedEvaluatesTo v v') : t.AugmentedEvaluatesTo (t.pred v) (t.pred v')
| -- iszero 0 → true
  EvaluatesToIsZeroZero : t.AugmentedEvaluatesTo (t.iszero t.zero) (t.True)
| -- iszero (succ nv) → false
  EvaluatesToIsZeroSucc (h : nv v) : t.AugmentedEvaluatesTo (t.iszero (t.succ v)) (t.False)
| -- (tt → tt') → (iszero tt → iszero tt')
  EvaluatesToIsZero (h : t.AugmentedEvaluatesTo tt tt') : t.AugmentedEvaluatesTo (t.iszero tt) (t.iszero tt')
|-- ite badBool l r → wrong
  EvaluatesToIfWrong (h : badBool cd) : t.AugmentedEvaluatesTo (cd.ite l r) t.wrong
| -- succ badNat → wrong
  EvaluatesToSuccWrong (h : badNat tt) : t.AugmentedEvaluatesTo (succ tt) t.wrong
| -- pred badNat → wrong
  EvaluatesToPredWrong (h : badNat tt) : t.AugmentedEvaluatesTo (pred tt) t.wrong
| -- iszero badNat → wrong
  EvaluatesToIsZeroWrong (h : badNat tt) : t.AugmentedEvaluatesTo (t.iszero tt) t.wrong

/-- Given that we can't mix different types in the same theorem, we first define a mapping from mySecondType.t to t -/
def map (e : mySecondType.t) : t :=
  match e with
  | .True => t.True
  | .False => t.False
  | .ite cnd lhs rhs => t.ite (map cnd) (map lhs) (map rhs)
  | .zero => t.zero
  | .pred n => t.pred (map n)
  | .succ n => t.succ (map n)
  | .iszero n => t.iszero (map n)

-- badnat has two constructors: wrong and tv, we say that neither of these is legal
theorem nvCantBeABadNatWrong (u : t) : nv u → ¬ u = t.wrong := by
  intro h
  induction h
  · case zero => simp
  · case succ ti iht ihti => simp

theorem nvCantBeTv (u : t) : nv u→ ¬ tv u := by
  intro h
  induction h
  · case zero => intro h; cases h
  · case succ ti iht ihti => intro h; cases h

theorem tvCantBeNv (u : t) : tv u→ ¬ nv u := by
  intro h
  induction h
  · case True => intro h; cases h
  · case False => intro h; cases h

theorem nvCantBeABadNat (u : t) : nv u → ¬ badNat u := by
  intro h hcontra
  induction hcontra
  · case wrong =>
      have := nvCantBeABadNatWrong _ h
      contradiction
  · case badTv bad hbad =>
      have := nvCantBeTv _ h
      contradiction

theorem tvCantBeABadBoolWrong (u : t) : tv u → ¬ u = t.wrong := by
  intro h
  induction h
  · case True => simp
  · case False => simp

theorem tvCantBeABadBool (u : t) : tv u → ¬ badBool u := by
  intro h hcontra
  induction hcontra
  · case wrong =>
      have := tvCantBeABadBoolWrong _ h
      contradiction
  · case badNv bad hbad =>
      have := tvCantBeNv _ h
      contradiction

-- it is not true that given any t: wrong → t
theorem NotWrongEvalTo (u : t) : ¬ t.AugmentedEvaluatesTo t.wrong u := by
  intro h -- suppose by hp. we have t.AugmentedEvaluatesTo t.wrong t
  cases h -- then we evaluate the cases by which this hypothesis can be true: none!

-- todo: if nv' x then x can't evaluate to anything
theorem NotnvEvalTo (u v : t) (h : nv v): ¬ t.AugmentedEvaluatesTo v u := by
  induction h generalizing u
  · case zero => intros h; cases h
  · case succ ti vi ihn =>
    intros hcontra
    cases hcontra
    · case EvaluatesToSucc vii ihvii => specialize ihn vii; contradiction
    · case EvaluatesToSuccWrong vii =>
      have := nvCantBeABadNat _ vi vii
      exact this

theorem NotBadBoolEvalTo (u v : t) (h : badBool v) : ¬ t.AugmentedEvaluatesTo v u := by
  induction h
  · case wrong => exact NotWrongEvalTo u
  · case badNv nv hnv => exact NotnvEvalTo u nv hnv

theorem nvEvalToNv (u v : t) (h₁ : nv u) (h₂ : tv v) : ¬ t.AugmentedEvaluatesTo u v := by
  induction h₁
  · case zero =>
    intro hcontra
    cases hcontra
  · case succ n hn hn' =>
    intro hcontra
    cases hcontra
    · case EvaluatesToSucc m hm =>
      cases h₂
    · case EvaluatesToSuccWrong hbad =>
      have := nvCantBeABadNat n hn
      contradiction

theorem selfCantEvalToSelf (u : t) : ¬ t.AugmentedEvaluatesTo u u := by
  apply Classical.byContradiction
  intro hcontra
  simp at hcontra
  induction u
  · case True => cases hcontra
  · case False => cases hcontra
  · case ite cd l r cd' ihl ihr =>
    cases hcontra
    · case EvaluatesToIf hif => exact cd' hif
  · case zero => cases hcontra
  · case succ s hs =>
    cases hcontra
    · case EvaluatesToSucc ihs => exact hs ihs
  · case pred p hp =>
    cases hcontra
    · case EvaluatesToPred ihp => exact hp ihp
  · case iszero z hz =>
    cases hcontra
    · case EvaluatesToIsZero ih => exact hz ih
  · case wrong => cases hcontra

theorem selfCantEvalToSucc (u v : t) (hnv : nv u) (huv : v = u.succ) (h : t.AugmentedEvaluatesTo u v) :
    ¬ t.AugmentedEvaluatesTo u u.succ := by
  induction h
  <;> cases huv
  · case EvaluatesToSucc.refl s p ih =>
    exact NotnvEvalTo s.succ.succ s.succ hnv

theorem nvOfEvalTonv (u v : t) (hnv : nv u) (heval : u.AugmentedEvaluatesTo v) : nv v := by
  induction hnv generalizing v
  · case zero =>
    cases heval
  · case succ s hs ih =>
    cases heval
    · case EvaluatesToSucc p hp =>
      exact nv.succ p (ih p hp)
    · case EvaluatesToSuccWrong hbad =>
      have := nvCantBeABadNat s hs
      contradiction

-- becuse the semantics are cakk-by-value, the type systems are deterministic

/-- We first prove the one-step determinacy of AugmentsedEvaluatesTo, which will be useful to prove the subsequent lemma -/
theorem OneStepDeterminacyAugmented (a b c : t) (hab : t.AugmentedEvaluatesTo a b) (hac : t.AugmentedEvaluatesTo a c) : b = c := by
  induction hab generalizing c
  · case EvaluatesToTrue lhs rhs =>
    cases hac
    · case EvaluatesToTrue => rfl
    · case EvaluatesToIf lhs' ihl' => cases ihl'
    · case EvaluatesToIfWrong hbad =>
      -- True is not a badBool!
      contradiction
  · case EvaluatesToFalse lhs rhs =>
    cases hac
    · case EvaluatesToFalse => rfl
    · case EvaluatesToIf lhs' ihl' => cases ihl'
    · case EvaluatesToIfWrong hbad =>
      -- False is not a badBool!
      contradiction
  · -- a [EvaluatesToIf]→ b
    -- a = cd.ite l r
    -- b = cd'.ite l r
    -- and ∃ h : cd.evalTo cd'
    case EvaluatesToIf cond cond' lhs rhs ihl ihr =>
    cases hac
    · case EvaluatesToTrue => cases ihl -- True does not evaluate to anything
    · case EvaluatesToFalse => cases ihl -- False does not evaluate to anything
    · case EvaluatesToIf cond'' ihc' =>
      specialize ihr cond''
      exact congrFun (congrFun (congrArg t.ite (ihr ihc')) lhs) rhs
    · -- a [EvaluatesToIfWrong]→ c
      case EvaluatesToIfWrong hbad =>
      -- we want to show that if a = wrong then a [EvaluatesToIf]→ b is a contradiction
      induction hbad generalizing cond'
      · case wrong => cases ihl
      · case badNv nvbad hbad =>
        -- nvbad can't evaluate to cond'
        have := NotnvEvalTo cond' nvbad hbad
        contradiction
  · -- a [EvaluatesToSucc]→ b
    -- a = succ n
    -- b = succ m
    -- under the hypothesis that n [EvaluatesTo]→ m
    case EvaluatesToSucc s r ihs ihr =>
    cases hac
    · -- hab and hac evaluate with the same rule
      case EvaluatesToSucc r' h =>
      specialize ihr r' h
      simp [ihr]
    · case EvaluatesToSuccWrong hbad =>
      cases hbad
      · case wrong => cases ihs
      · case badTv htv =>
        -- given htv, s can't evaluate to anything whose "succ" is different than wrong
        cases htv
        · case True => cases ihs
        · case False => cases ihs
  · case EvaluatesToZero =>
    cases hac
    · case EvaluatesToZero => rfl
    · case EvaluatesToPred n hzero => cases hzero
    · case EvaluatesToPredWrong hbad =>
      -- zero is not badNat
      have hnv : nv t.zero := nv.zero
      have := nvCantBeABadNat t.zero hnv
      contradiction
  · case EvaluatesToPredSucc s ihs =>
    cases hac
    · case EvaluatesToPredSucc =>
      rfl
    · case EvaluatesToPred x hx =>
      have := NotnvEvalTo x (s.succ) (by  constructor; apply ihs)
      contradiction
    · case EvaluatesToPredWrong badNat =>
        -- NV can't be a badNat
        have := nv.succ s ihs
        have := nvCantBeABadNat s.succ this
        contradiction
  · case EvaluatesToPred s r ihs ihr =>
    cases hac
    · case EvaluatesToZero => cases ihs -- zero does not evaluate to anything
    · case EvaluatesToPredSucc hnv =>
      have := NotnvEvalTo r (c.succ) (by  constructor; apply hnv)
      contradiction
    · case EvaluatesToPred p hp =>
      specialize ihr p hp
      simp [ihr]
    · case EvaluatesToPredWrong hbad =>
      cases hbad
      · case wrong => cases ihs
      · case badTv h =>
        have := tvCantBeNv s h
        -- tv can't evalute to anything
        cases h
        · cases ihs
        · cases ihs
  · case EvaluatesToIsZeroZero =>
    cases hac
    · case EvaluatesToIsZeroZero => rfl
    · case EvaluatesToIsZero v h => cases h
    · case EvaluatesToIsZeroWrong hbad =>
      have := nvCantBeABadNat t.zero nv.zero
      contradiction
  · case EvaluatesToIsZeroSucc s ihs =>
      cases hac
      · case EvaluatesToIsZeroSucc h => rfl
      · case EvaluatesToIsZero v h =>
        have ihs' := nv.succ s ihs
        have := NotnvEvalTo v s.succ ihs'
        contradiction
      · case EvaluatesToIsZeroWrong h =>
        have := nvCantBeABadNat s.succ (nv.succ s ihs)
        contradiction
  · case EvaluatesToIsZero s r ihsr ih =>
      cases hac
      · case EvaluatesToIsZeroZero => cases ihsr
      · case EvaluatesToIsZeroSucc v ih =>
        rename_i ihv
        have := NotnvEvalTo r v.succ (nv.succ v ihv)
        contradiction
      · case EvaluatesToIsZero v h =>
        simp only [t.iszero.injEq]
        apply ih
        exact h
      · case EvaluatesToIsZeroWrong hbad =>
        cases hbad
        · case wrong => cases ihsr
        · case badTv htv =>
          cases htv
          · case True => cases ihsr
          · case False => cases ihsr
  · case EvaluatesToIfWrong cd l' r' hbad =>
    cases hac
    · case EvaluatesToTrue =>
      have := tvCantBeABadBool (u := t.True) tv.True
      contradiction
    · case EvaluatesToFalse =>
      have := tvCantBeABadBool (u := t.False) tv.False
      contradiction
    · case EvaluatesToIf cd' ih =>
      cases hbad
      · case wrong => cases ih
      · case badNv hbad =>
        have := NotnvEvalTo cd' cd hbad
        contradiction
    · case EvaluatesToIfWrong => rfl
  · case EvaluatesToSuccWrong s ihs =>
    cases hac
    · case EvaluatesToSucc v ih =>
      cases ihs
      · case wrong => cases ih
      · case badTv hv =>
        cases hv
        · case True => cases ih
        · case False => cases ih
    · case EvaluatesToSuccWrong => rfl
  · case EvaluatesToPredWrong s ihs =>
    cases hac
    · case EvaluatesToZero =>
      have := nvCantBeABadNat t.zero (nv.zero)
      contradiction
    · case EvaluatesToPredSucc h =>
      have := nvCantBeABadNat c.succ (nv.succ c h)
      contradiction
    · case EvaluatesToPred v' hv' =>
      cases ihs
      · case wrong => cases hv'
      · case badTv htv =>
        cases htv
        · case True => cases hv'
        · case False => cases hv'
    · case EvaluatesToPredWrong => rfl
  · case EvaluatesToIsZeroWrong s ihs =>
    cases hac
    · case EvaluatesToIsZeroZero =>
      have := nvCantBeABadNat t.zero nv.zero
      contradiction
    · case EvaluatesToIsZeroSucc u hu =>
      have := nvCantBeABadNat u.succ (nv.succ u hu)
      contradiction
    · case EvaluatesToIsZero u hu =>
      cases ihs
      · case wrong => cases hu
      · case badTv htv =>
        cases htv
        · case True => cases hu
        · case False => cases hu
    · case EvaluatesToIsZeroWrong => rfl

/-- Then we prove that the augmented evaluations in t correspond to the def. of `stuck` in t' -/
theorem stuck_iff (g : mySecondType.t):
    ((t.AugmentedEvaluatesTo (map g) (t.wrong))) ↔ (mySecondType.isStuck g) := by
  induction g
  · case True =>
    simp [map]
    constructor
    · intro h; cases h
    · intro h
      obtain ⟨h1, h2, h3⟩ := h
      apply ElimOftvTrue h2
  · case False =>
    simp [map]
    constructor
    · intro h; cases h
    · intro h
      obtain ⟨h1, h2, h3⟩ := h
      apply ElimOftvFalse h2
  · case ite cnd lhs rhs ihc ihl ihr =>
    cases cnd
    · case True =>
      simp [map] at ihc ⊢
      simp [isStuck'] at ihc
      constructor
      · intro h
        cases h

        sorry
      · intro h
        sorry
    · case False => sorry
    · case ite cnd' lhs' rhs' => sorry
    · case zero => sorry
    · case succ s => sorry
    · case pred s => sorry
    · case iszero s => sorry










  · intro haug
    cases g
    · case True =>
        unfold map at haug
        cases haug
    · case False =>
        unfold map at haug
        cases haug
    · case ite cnd lhs rhs =>
        unfold map at haug
        unfold isStuck' NormalForm'
        cases cnd
        · case True =>
          have hexists : t'.EvaluatesTo (t'.ite t'.True lhs rhs) lhs := t'.EvaluatesTo.EvaluatesToTrue
          have : ¬ ∀ (x : t'), ¬(t'.True.ite lhs rhs).EvaluatesTo x := by
            simp only [Classical.not_forall, Classical.not_not]
            exists lhs
          simp at this
          simp [map] at haug
          have hexistsaug : t.AugmentedEvaluatesTo (t.ite t.True (map lhs) (map rhs)) (map lhs) := t.AugmentedEvaluatesTo.EvaluatesToTrue
          cases lhs <;> cases rhs
          · simp [map] at haug hexistsaug
            simp [this]
            cases haug
            · case True.True.EvaluatesToIfWrong hbad => rcases hbad



          sorry
        sorry
    · case zero =>
        unfold map at haug
        cases haug
    · case succ n =>
        unfold map at haug
        cases haug
    · case pred n =>
        unfold map at haug
        cases haug
    · case iszero n =>
        unfold map at haug
        cases haug
  · sorry
