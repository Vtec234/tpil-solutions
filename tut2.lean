section ex1
  -- merged do_twice and Do_Twice into one function using dependent type
  def do_twice: Π {α: Type}, ((α → α) → α → α) := λ α f x, f (f x)
  -- this is the same, just different notation
  def do_twice' {α: Type} (f: α → α): α → α := λ x, f (f x)

  def double: ℕ → ℕ := λ x, x+x

  #reduce do_twice do_twice' double 2
end ex1


section ex2
  def curry {α β γ: Type} (f: α × β → γ): α → β → γ := λ a b, f (a, b)
  def uncurry {α β γ: Type} (f: α → β → γ): α × β → γ := λ pr, f pr.fst pr.snd

  def mult_two: ℕ → ℕ → ℕ := λ x y, x*y
  def mult_pair: (ℕ × ℕ) → ℕ := λ pr, pr.fst*pr.snd

  #reduce curry mult_pair 2 4
  #reduce uncurry mult_two (3, 5)
end ex2


namespace ex3
  constant vec: Type → ℕ → Type

  constant vec_add {α: Type} {m: ℕ}: vec α m → vec α m → vec α m
  constant vec_reverse {α: Type} {m: ℕ}: vec α m → vec α m

  constant v: vec ℕ 3

  #check vec_add v v
  #check vec_reverse v
end ex3


namespace ex4
  constant vec: Type → ℕ → Type
  constant matrix : Type → ℕ → ℕ → Type

  constant madd: Π {α: Type} {m n: ℕ}, matrix α m n → matrix α m n → matrix α m n
  constant mmul: Π {α: Type} {m n k: ℕ}, matrix α m n → matrix α n k → matrix α m k
  -- assume column vector and matrix on left, so m rows in answer
  constant mvmul: Π {α: Type} {m n: ℕ}, matrix α m n → vec α n → vec α m

  constant M: matrix ℕ 3 4
  constant M': matrix ℕ 4 5
  constant v: vec ℕ 4

  #check madd M M
  #check mmul M M'
  #check mvmul M v
end ex4
