/--
  Inductive definition of terms:
  The set of terms T contains:
  · {true, false, 0}
  · if t₁ ∈ T then {succ t₁, pred t₁, iszero t₁} ⊆ T
  · if t₁, t₂, t₃ ∈ T then "if t₁ then t₂ else t₃" ∈ T
-/

/- Lean automatically indexes the levels of the types -/
inductive newType : Type where
  | ttrue : newType
  | ffalse  : newType
  | zero : newType
  | pred (t : newType)  : newType
  | isZero (t : newType) : newType
  | ite  (t₁ t₂ t₃ : newType) : newType


/- Lean generates a `sizeOf` automatically that knows the level `i` for a `tᵢ`: -/
#reduce sizeOf newType.ttrue -- 1
#reduce sizeOf newType.ffalse -- 1
#reduce sizeOf (newType.isZero .ttrue) -- 2

/-- Untyped Booleans -/

inductive t where
  | True : t
  | False : t
  | ite : t → t → t → t

#reduce sizeOf t.True -- 1
#reduce sizeOf t.False -- 1
#reduce sizeOf (t.ite t.True t.True t.False) -- 4

/- define the evaluation relation: in Lean we incode it as an  *inductive prooposition* -/

inductive t.EvaluatesTo : t → t → Prop
| EvaluatesToTrue: t.EvaluatesTo (.ite .True t₂ t₃) t₂
| EvaluatesToFalse: t.EvaluatesTo (.ite .False t₂ t₃) t₃
| EvaluatesToIf (h : t.EvaluatesTo c c') : t.EvaluatesTo (.ite c l r) (.ite c' l r)

open t

/-
  theorem 3.5.4: determinacy of one-step evaluation
    if t → t' and t → t'' then t' = t''
  (note that we represent "→" as EvaluatesTo)
-/
theorem OneStepDeterminacy (a b c : t) (hab : t.EvaluatesTo a b) (hac : t.EvaluatesTo a c) : b = c := by
  revert c -- need to generalize c to be able to use it afterwards in the inductive cases
  induction hab
  · case EvaluatesToTrue =>
   intros c hac
   cases hac
   · case EvaluatesToTrue => rfl
   · case EvaluatesToIf tthenc telsec =>
      cases telsec -- absurd, t.True is a normal form, cannot EvaluatesTo.
  · case EvaluatesToFalse =>
      intros c hac
      cases hac
      · case EvaluatesToFalse => rfl
      · case EvaluatesToIf tthen telse =>
        cases telse -- absurd, t.False is a normal form, cannot EvaluatesTo.
  · case EvaluatesToIf ac ac' al ar hacac' ih  =>
      intros c thenRed
      cases thenRed
      · case EvaluatesToTrue => cases hacac' -- absurd, t.True is a normal form, cannot EvaluatesTo.
      · case EvaluatesToFalse => cases hacac' -- absurd, t.False is a normal form, cannot EvaluatesTo.
      · case EvaluatesToIf tthen telse =>
          rw [ih]
          exact telse

/--  Untyped Booleans and Naturals: we introduce a new type t' which contains either elements from t (booleans) or natural numbers -/

inductive t' where
  | True : t'
  | False : t'
  | ite : t' → t' → t' → t'
  | zero : t'
  | succ : t' → t'
  | pred : t' → t'
  | iszero : t' → t'
  deriving Repr

inductive nv : t' → Prop where
  | zero : nv t'.zero
  | succ n : nv n → nv (t'.succ n)

inductive t'.EvaluatesTo : t' → t' → Prop
| -- ite true t₂ t₃ → t₂
  EvaluatesToTrue {t₁ t₁' : t'} : t'.EvaluatesTo (True.ite t₁ t₁') t₁
| -- ite false t₂ t₃ → t₃
  EvaluatesToFalse {t₁ t₁' : t'} : t'.EvaluatesTo (False.ite t₁ t₁') t₁'
| -- (c → c') → (ite c l r → ite c' l r)
  EvaluatesToIf (h : t'.EvaluatesTo c c') : t'.EvaluatesTo (c.ite l r) (c'.ite l r)
| -- (t₁ → t₁') → (succ t₁ → succ t₂)
  EvaluatesToSucc {t₁ t₁' : t'} (h : EvaluatesTo t₁ t₁') : (EvaluatesTo (t'.succ t₁) (t'.succ t₁'))
| -- pred 0 = 0
  EvaluatesToZero : t'.EvaluatesTo (t'.pred t'.zero) (t'.zero)
| -- pred (succ nv) → nv
  EvaluatesToPredSucc (h : nv v₁) : t'.EvaluatesTo (t'.pred (t'.succ v₁))  (v₁)
| -- (t₁ → t₁') → (pred t₁ → pred t₂)
  EvaluatesToPred (h : t'.EvaluatesTo t₁ t₁') : t'.EvaluatesTo (t'.pred t₁) (t'.pred t₁')
| -- iszero 0 → true
  EvaluatesToIsZeroZero : t'.EvaluatesTo (t'.iszero t'.zero) (t'.True)
| -- iszero (succ nv) → false
  EvaluatesToIsZeroSucc (h : nv v₁) : t'.EvaluatesTo (t'.iszero (t'.succ v₁)) (t'.False)
| -- (t₁ → t₁') → (iszero t₁ → iszero t₂)
  EvaluatesToIsZero (h : t'.EvaluatesTo t₁ t₁') : t'.EvaluatesTo (t'.iszero t₁) (t'.iszero t₁')

-- Q: what's the diff between doing cases on an inductive type vs. induction

/-- A perspective on inductive predicates and relations based on set theory, from https://link.springer.com/chapter/10.1007/3-540-61780-9_64

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
theorem NotTrueEvalTo (t : t') : ¬ t'.EvaluatesTo t'.True t := by
  intro h -- suppose by hp. we have t'.EvaluatesTo t'.True t
  cases h -- then we evaluate the cases by which this hypothesi can be true: none!

-- it is not true that given any t: False → t
theorem NotFalseEvalTo (t : t') : ¬ t'.EvaluatesTo t'.False t := by
  intro h -- suppose by hp. we have t'.EvaluatesTo t'.False t
  cases h -- then we evaluate the cases by which this hypothesi can be true: none!

-- it is not true that given any t: zero → t
theorem NotZeroEvalTo (t : t') : ¬ t'.EvaluatesTo t'.zero t := by
  intro h -- suppose by hp. we have t'.EvaluatesTo t'.zero t
  cases h -- then we evaluate the cases by which this hypothesi can be true: none!

-- it is not true that a v : t' such that ∃ n : nv v can evaluate to a generic t
theorem NotNvEvalTo (v t : t') (n : nv v) : ¬ t'.EvaluatesTo v t := by
  induction n generalizing t
  · -- n = nv t'.zero, v' = t'.zero
    case zero => exact NotZeroEvalTo t
  · -- n = succ n' = nv (t'.succ n'), v' = t'.succ n'
    -- with ihn : ∀ (t : t'), ¬v'.EvaluatesTo t
    -- and the goal will require to demonstrate ¬v'.succ.EvaluatesTo t
    case succ v' n ihn =>
    intro h' -- suppose we can actually have an evaluation of (t'.succ v') → t
    cases h' -- this can only happen by (t'.succ v')[EvaluatesToSucc]→ t
    · case EvaluatesToSucc t₁' h =>
      -- note that the rule says that given (h : EvaluatesTo t₁ t₁') then (EvaluatesTo (t'.succ t₁) (t'.succ t₁'))
      -- we thus suppose there exists a t₁' such that v' → t₁', by which we conclude (t'.succ v') → (t'.succ t₁')
      -- we need to prove that the inductive hypothesis still holds: ¬ v' → (succ t₁')
      -- we apply the inductive hypothesis ¬v'.EvaluatesTo t with t = t₁' and given the evaluation in h.
      exact ihn t₁' h


theorem OneStepDeterminacy' (a b c : t') (hab : t'.EvaluatesTo a b) (hac : t'.EvaluatesTo a c) : b = c := by
  -- we use induction on the derivation rule hab
  induction hab generalizing c -- same as "revert c"
  · -- a [EvaluatesToTrue]→ b
    -- i.e., a = ite True t₁ t₁'
    case EvaluatesToTrue t₁ t₁' =>
    cases hac
    · -- a [EvaluatesToTrue]→ c
      case EvaluatesToTrue => rfl
    · -- a [EvaluatesToIf]→ c
      -- i.e., given (h : t'.EvaluatesTo True c') then t'.EvaluatesTo (ite True t₁ t₁') (ite c' t₁ t₁')
      -- with a = ite True t₁ t₁' according to the first case and c = ite c' t₁ t₂
      case EvaluatesToIf c hTrueEvalTo =>
        -- does not exist, as per the first inversion lemma:
        -- we show that the hypotheses are contradictory (showing that the
        -- contrary of NotTrueEvalTo is absurd)
        exact absurd hTrueEvalTo (NotTrueEvalTo _)
  · -- a [EvaluatesToFalse]→ b
    -- i.e., a = ite False t₁ t₁'
    -- this case works exactly as the previous one
    case EvaluatesToFalse t₁ t₁' =>
    cases hac
    · -- a [EvaluatesToFalse]→ c
      case EvaluatesToFalse => rfl
    · -- a [EvaluatesToIf]→ c
      -- i.e., given (h : t'.EvaluatesTo False c') then t'.EvaluatesTo (ite False t₁ t₁') (ite c' t₁ t₁')
      -- with a = ite False t₁ t₁' according to the first case and c = ite c' t₁ t₂
      case EvaluatesToIf c hTrueEvalTo =>
        -- does not exist, as per the second inversion lemma:
        -- we show that the hypotheses are contradictory (showing that the
        -- contrary of NotFalseEvalTo is absurd)
        exact absurd hTrueEvalTo (NotFalseEvalTo _)
  · -- a [EvaluatesToIf]→ b
    case EvaluatesToIf cond₁ cond₂ l r hCondEvalToCond ihcond =>
    -- the inductive hypothesis applies the theorem statement
    -- to the subterm involved in the hypothesis this evaluation
    -- rules relies on
    cases hac
    · -- a [EvaluatesToTrue]→ c
      case EvaluatesToTrue => -- absurd as above
      exact absurd hCondEvalToCond (NotTrueEvalTo _)
    · -- a [EvaluatesToFalse]→ c
      case EvaluatesToFalse => -- absurd as above
      exact absurd hCondEvalToCond (NotFalseEvalTo _)
    · -- a [EvaluatesToIf]→ c
      -- i.e., given a = ite cond₁ l r and hab : given (cond₁ → cond₂) then (ite cond₁ l r) → (cond₂ l r)
      -- we suppose
      -- hac : given (cond₁ → cond') then (ite cond₁ l r) → (cond' l r)
      -- and thus the goal b = c becomes:
      -- (cond₂ l r) = (cond' l r)
      case EvaluatesToIf cond' hcontEvalToCond =>
      -- we exploit the congruence in functions and applications and construct
      exact congrFun (congrFun (congrArg t'.ite (ihcond cond' hcontEvalToCond)) l) r
  · -- a [EvaluatesToSucc]→ b
    case EvaluatesToSucc t₁ t₁' ht₁EvalTot₁' ih =>

    sorry
