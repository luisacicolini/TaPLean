/-- Inductive definition of terms:
  The set of terms T contains:
  · {true, false, 0}
  · if t₁ ∈ T then {succ t₁, pred t₁, iszero t₁} ⊆ T
  · if t₁, t₂, t₃ ∈ T then "if t₁ then t₂ else t₃" ∈ T
-/

/-
inductive newType : Nat → Type where
  | ttrue {n : Nat} : newType 0
  | ffalse {n : Nat} : newType 0
  | zero {n : Nat} : newType 0
  | pred {n : Nat} (t : newType (n - 1)) : newType n
  | isZero {n : Nat} (t : newType (n - 1)) : newType n
  | ite {n : Nat} (t₁ t₂ t₃ : newType (n - 1)) : newType n
-/


/- Lean automatically indexes the levels of the types -/
inductive newType : Type where
  | ttrue : newType
  | ffalse  : newType
  | zero : newType
  | pred (t : newType)  : newType
  | isZero (t : newType) : newType
  | ite  (t₁ t₂ t₃ : newType) : newType

#eval Lean.versionString


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
  (note that we implement "→" as EvaluatesTo)
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
  EvaluatesToIf {t₁ t₁' : t'} (h : t'.EvaluatesTo c c') : t'.EvaluatesTo (c.ite l r) (c'.ite l r)
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

/-- exercise 3.5.14: show that theorem 3.5.4 also holds for t' -/
theorem OneStepDeterminacy' (a b c : t') (hab : t'.EvaluatesTo a b) (hac : t'.EvaluatesTo a c) : b = c := by
  -- this time we use induction on the structure of a
  revert b c
  induction a
  · -- if a = t'.True only [EvaluatesToTrue] is a valid evaluation rule
    case True =>
      intros b c hb hc
      cases hb
  · -- if a = t'.False only [EvaluatesToFalse] is a valid evaluation rule
    case False =>
      intros b c hb hc
      cases hb
  · -- suppose a = ite a1 a2 a3
    -- then
    -- hab := (ite a1 a2 a3).EvaluatesTo b
    -- hac := (ite a1 a2 a3).EvaluatesTo c
    case ite a1 a2 a3 ih1 ih2 ih3 =>
      intros b c hb hc
      · cases hb
        · case EvaluatesToTrue =>
          cases hc
          · -- a [EvaluatesToTrue] → b and
            -- a [EvaluatesToTrue] → c
            case EvaluatesToTrue => rfl
          · -- a [EvaluatesToTrue] → b and
            -- a [EvaluatesToIf] → c,
            -- this is absurd  since a = ite true a2 a3 can only evaluate by
            -- EvaluatesToTrue
            case EvaluatesToIf c' hTrueEvalTo => cases hTrueEvalTo
        · case EvaluatesToFalse =>
          cases hc
          · case EvaluatesToFalse => rfl
          · case EvaluatesToIf c' hFalseEvalTo => cases hFalseEvalTo -- absurd
        · case EvaluatesToIf c' t₁ t₁' ha1Toc1 =>
          cases hc
          · case EvaluatesToTrue => cases ha1Toc1 -- contradiction
          · case EvaluatesToFalse => cases ha1Toc1 -- contradictio
          · case EvaluatesToIf c' t₁ t₁' ha1Toc' =>
            simp only [t'.ite.injEq, and_self, and_true]
            -- we can specialize ih1 with the hypotheses haToc1 and haToc'
            apply ih1
            · exact ha1Toc1
            · exact ha1Toc'
  · -- suppose a = zero
    case zero =>
    intros b c hb hc
    cases hb -- there is only one rule that can evaluate .zero
  · -- suppose a = succ s
    case succ s ih =>
    intros b c hb hc
    cases hb
    · case EvaluatesToSucc t₁ hsTot₁ =>
      cases hc
      · case EvaluatesToSucc t₁' hsTot₁' =>
        simp only [t'.succ.injEq]
        apply ih
        · exact hsTot₁
        · exact hsTot₁'
  · -- suppose a = pred s
    case pred s ih =>
    intros b c hb hc
    cases hb
    · case EvaluatesToZero =>
      cases hc
      · case EvaluatesToZero => rfl -- same derivation rule
      · case EvaluatesToPred t₁' hzeroTot₁' => cases hzeroTot₁' -- absurd
    · case EvaluatesToPredSucc b =>
      induction b
      · case zero =>
        cases hc
        · case EvaluatesToPredSucc => rfl
        · case EvaluatesToPred t₁' h =>
          cases h
          · case EvaluatesToSucc t₁' h =>
            cases h
      · case succ b ihb =>
        cases hc
        · case EvaluatesToPredSucc => rfl
        · case EvaluatesToPred t₁' h =>

          cases h
          · case EvaluatesToSucc t₁' h =>
            cases h
            · case EvaluatesToSucc t₁' h =>




      sorry
    · case EvaluatesToPred t₁' hsTot₁' =>
      cases hc
      · case EvaluatesToZero => cases hsTot₁'
      · case EvaluatesToPredSucc =>

        sorry
      · case EvaluatesToPred t₁' h =>
        simp
        apply ih
        · exact hsTot₁'
        · exact h
  · -- suppose a = iszero s
    case iszero s ih =>
    intros b c hb hc
    cases hb
    · case EvaluatesToIsZeroZero =>
      cases hc
      · case EvaluatesToIsZeroZero => rfl
      · case EvaluatesToIsZero t₁' h => cases h -- absurd
    · case EvaluatesToIsZeroSucc v₁ h =>

      cases hc
      · case EvaluatesToIsZeroSucc => rfl
      · case EvaluatesToIsZero t₁' h =>
        simp [h]


        sorry
    · case EvaluatesToIsZero t₁' h =>
      cases hc
      · case EvaluatesToIsZeroZero => sorry
      · case EvaluatesToIsZeroSucc => sorry
      · case EvaluatesToIsZero t₁'' hsTot₁'' =>
        simp
        apply ih
        · exact h
        · exact hsTot₁''








/-
/-- Untyped Bools and Nats -/
inductive t' where
  | True : t'
  | False : t'
  | ite : t' → t' → t' → t'
  | zero : t'
  | succ : t' → t'
  | pred : t' → t'
  | isZero : t' → t'
def valB (b : t') :=
  match b with
  | t'.True => true
  | t'.False => false
  | t'.ite c a b => if valB c then valB a else valB b
  | _ => _
def valN (n : t') : Nat :=
  match n with
  | t'.True => valB n
  | t'.False => valB n
  | t'.ite c a b => valB n
  | t'.zero => val: t'
  | t'.succ => val: t' → t'
  | t'.pred => val: t' → t'
  | t'.isZero => val: t' → t'
-/
