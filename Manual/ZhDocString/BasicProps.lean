namespace ZhDoc

/-
/--
`Or a b`, or `a ∨ b`, is the disjunction of propositions. There are two
constructors for `Or`, called `Or.inl : a → a ∨ b` and `Or.inr : b → a ∨ b`,
and you can use `match` or `cases` to destruct an `Or` assumption into the
two cases.
-/
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` is "left injection" into an `Or`. If `h : a` then `Or.inl h : a ∨ b`. -/
  | inl (h : a) : Or a b
  /-- `Or.inr` is "right injection" into an `Or`. If `h : b` then `Or.inr h : a ∨ b`. -/
  | inr (h : b) : Or a b
-/


/--
`Or a b`，或 `a ∨ b`，是命题的析取。
`Or` 有两个构造器，分别是 `Or.inl : a → a ∨ b` 和 `Or.inr : b → a ∨ b`，
可以使用 `match` 或 `cases` 将 `Or` 的假设析构为两种情况。
-/
inductive Or (a b : Prop) : Prop where
  /-- `Or.inl` 是向 `Or` 的“左注入”。如果 `h : a`，那么 `Or.inl h : a ∨ b`。-/
  | inl (h : a) : Or a b
  /-- `Or.inr` 是向 `Or` 的“右注入”。如果 `h : b`，那么 `Or.inr h : a ∨ b`。-/
  | inr (h : b) : Or a b

end ZhDoc
