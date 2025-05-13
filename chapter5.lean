/- *Untyped Lambda Calculus*

  we use `λn.something` to descrive a function that, for each `n`, yields `something`

  def 13.
  the concrete syntax of a language refers to the strings of characters that programmers read/write
  the abstract syntax of a Language is a simpler internal representation by means of an AST

  def 14.
  tiven λx.t we say variable x is bound if it appears in the body of t and we say λx is a
  binder whose scope is t

  def 15.
  tn occurrence of a variable is free if it is not bound by an enclosing abstraction

  def 16.
  a term t with no free variables is closed, closed terms are also called combinator
  the identity function is the simplest combinator: id = λx.x

  def 17.
  a β-reduction is a reduction of the form:
      (λx.t₁) t₂ → [x ↦ t₂]t₁
  where we replace all free occurrences of x in t₁ by t₂
  there exist various reduction strategies:
  · full β-reduction: any reducible expression can be reduced at any time
  · normal order strategy: reduce outermost expressions first
  · call-by-name strategy: allows no reductions inside abstractions
  · call-by-value strategy: only outermost indices are reduced and reducible expressions are only reduced
      when its RHS has been reduced to a value already

  def 18.
  currying is a transformation that allows for multiple arguments in λ-calculus
  let s be a term involving two free variables, suppose we want to write:
    f : (v, w) → s [x := v, y := w] "replace x by v, y by w"
      = λx.λy.s
    such that:
        (λx.λy.s) v w = f v w = (f v) w (assuming left-associativity)
      = ((λy.[x↦ v]s)w)
      = [y ↦ w][x ↦ v]s
-/
