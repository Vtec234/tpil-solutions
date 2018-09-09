-- use mathlib stuff
import tactic.find
import logic.basic


section notes
  universe u
  variables (α: Type) (p q: α → Prop) (r: α → α → Prop)
  variables (a b c d e: ℤ)

  example: (∀ x: α, p x ∧ q x) → ∀ y: α, p y :=
    assume h: ∀ x: α, p x ∧ q x,
    assume y: α,
    show p y, from (h y).left

  variable refl_r : ∀ x, r x x
  variable symm_r : ∀ {x y}, r x y → r y x
  variable trans_r : ∀ {x y z}, r x y → r y z → r x z

  -- double transitivity + one symmetry
  example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
    trans_r (trans_r hab (symm_r hcb)) hcd

  example (a b c d: α) (hab: a=b) (hcb: c=b) (hcd: c=d): a=d :=
    eq.trans (eq.trans hab (eq.symm hcb)) hcd

  -- cool!
  example: 2+5 = 7 := rfl

  example (α: Type u) (a b: α) (p: α → Prop) (h1: a = b) (h2: p a): p b :=
    h1 ▸ h2

  example: a+0 = a := add_zero a
  example: a*(b+c) = a*b + a*c := mul_add a b c

  example (x y: ℤ): (x+y)*(x+y) = x*x + y*x + x*y + y*y :=
    have h1: (x+y)*(x+y) = (x+y)*x + (x+y)*y, from mul_add (x+y) x y,
    have h2: (x+y)*(x+y) = x*x + y*x + (x*y + y*y),
    from (add_mul x y x) ▸ (add_mul x y y) ▸ h1,
    h2.trans (add_assoc (x*x + y*x) (x*y) (y*y)).symm

  theorem T (h1: a=b) (h2: b=c+1) (h3: c=d) (h4: e=1+d): a=e :=
    calc
      a   = b   : by rw h1
      ... = c+1 : by rw h2
      ... = d+1 : by rw h3
      ... = 1+d : by rw add_comm
      ... = e   : by rw h4

  theorem T' (h1: a=b) (h2: b=c+1) (h3: c=d) (h4: e=1+d): a=e :=
    -- black magic
    by simp [h1, h2, h3, h4]

  example (x y: ℤ): (x+y)*(x+y) = x*x + y*y + x*y + y*x :=
    by simp [mul_add, add_mul]

  example (x y z: ℤ) (hxy: x < y) (hyz: y < z):
    ∃ w, x < w ∧ w < z :=
  exists.intro y (and.intro hxy hyz)

  #check @exists.intro

  variable g : ℕ → ℕ → ℕ
  variable hg : g 0 0 = 0

  theorem gex1 : ∃ x, g x x = x := ⟨0, hg⟩
  theorem gex2 : ∃ x, g x 0 = x := ⟨0, hg⟩
  theorem gex3 : ∃ x, g 0 0 = x := ⟨0, hg⟩
  theorem gex4 : ∃ x, g x x = 0 := ⟨0, hg⟩

  set_option pp.implicit true  -- display implicit arguments
  #print gex1
  #print gex2
  #print gex3
  #print gex4

  example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with ⟨w, hw⟩ :=
    ⟨w, hw.right, hw.left⟩
  end

  def is_even (a: ℕ) := ∃ b, a = 2*b

  theorem even_plus_even {a b: ℕ}
    (h1: is_even a) (h2: is_even b): is_even (a+b) :=
  match h1, h2 with
    ⟨w1, hw1⟩, ⟨w2, hw2⟩ := ⟨w1 + w2, by rw [hw1, hw2, mul_add]⟩
  end

  -- requires LEM
  example (h: ¬ ∀ x, ¬ p x): ∃ x, p x :=
  classical.by_contradiction
    (assume h1: ¬ ∃ x, p x,
      have h2: ∀ x, ¬ p x, from
        assume x: α,
        assume h3: p x,
        -- ‹› <> ⟨⟩: thanks, Leo
        have h4: ∃ x, p  x, from ⟨x, ‹p x›⟩,
        show false, from h1 h4,
      show false, from h h2)
end notes


section ex1
  variables (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) :=
    iff.intro
      (assume h: ∀ x, p x ∧ q x,
        and.intro
          (assume x, show p x, from (h x).left)
          (assume x, show q x, from (h x).right))
      (assume h: (∀ x, p x) ∧ (∀ x, q x),
      assume x,
      show p x ∧ q x, from
        and.intro (h.left x) (h.right x))

  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) :=
    assume h : (∀ x, p x → q x),
    assume h' : (∀ x, p x),
    (assume x,
      have p x → q x, from h x,
      show q x, from this (h' x))

  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x :=
    assume h : (∀ x, p x) ∨ (∀ x, q x),
    assume x,
    or.elim h
      (assume : (∀ x, p x), or.inl (this x))
      (assume : (∀ x, q x), or.inr (this x))
end ex1


section ex2
  variables (α : Type) (p q : α → Prop)
  variable r : Prop

  example : α → ((∀ x : α, r) ↔ r) :=
    assume x: α,
    iff.intro
      (assume h: (∀ x: α, r), h x)
      (assume h: r, assume _: α, h)

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r :=
    iff.intro
      (assume h: ∀ x, p x ∨ r,
      classical.by_contradiction
        (assume : ¬((∀ x, p x) ∨ r),
        have h1: ¬(∀ x, p x) ∧ ¬r, from not_or_distrib.mp this,
        have ¬∀ x, p x, from h1.left,
        have ¬r, from h1.right,
        have ∃ x, ¬p x, from classical.not_forall.mp ‹¬∀ x, p x›,
        match this with ⟨x, hpx⟩ :=
          show false, from or.elim (h x)
            (assume : p x, ‹¬p x› ‹p x›)
            (assume : r, ‹¬r› ‹r›)
        end))
      (assume h: (∀ x, p x) ∨ r,
      show (∀ x, p x ∨ r), from or.elim h
        (assume hpx: ∀ x, p x, assume x, or.inl (hpx x))
        (assume hr: r, assume x, or.inr hr))

  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) :=
    iff.intro
      (assume h: ∀ x, r → p x,
      assume hr: r,
      assume x,
      show p x, from (h x) hr)
      (assume h: r → ∀ x, p x,
      assume x,
      assume hr: r,
      show p x, from (h hr) x)
end ex2


section ex3
  variables (men : Type) (barber : men)
  variable  (shaves : men → men → Prop)

  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
    false :=
  have h: shaves barber barber ↔ ¬ shaves barber barber, from h barber,
  show false, from (iff_not_self _).mp h
end ex3


namespace ex4
  def divides (m n : ℕ) : Prop := ∃ k, m * k = n

  instance : has_dvd nat := ⟨divides⟩

  def even (n : ℕ) : Prop := 2 ∣ n

  section
    variables m n : ℕ

    #check m ∣ n
    #check m^n
    #check even (m^n +3)
  end

  def prime (n : ℕ) : Prop := ∀ m, (m ≠ 1 ∧ m ≠ n) →
    ¬ (m ∣ n)

  def infinitely_many_primes : Prop := ∀ p, (prime p) →
    (∃ p₂, p < p₂ ∧ prime p₂)

  def Fermat_prime (n : ℕ) : Prop := prime n ∧ (∃ k: ℕ, k ≠ 0 ∧ 2^k + 1 = n)

  def infinitely_many_Fermat_primes : Prop := ∀ p, (Fermat_prime p) →
    (∃ p₂, p < p₂ ∧ Fermat_prime p₂)

  def goldbach_conjecture : Prop := ∀ n, (2 ∣ n ∧ n > 2) →
    -- TODO prove
    (∃ p₁ p₂, prime p₁ ∧ prime p₂ ∧ n = p₁ + p₂)

  def Goldbach's_weak_conjecture : Prop := ∀ n, (¬ (2 ∣ n) ∧ n > 5) →
    (∃ p₁ p₂ p₃, prime p₁ ∧ prime p₂ ∧ prime p₃ ∧ n = p₁ + p₂ + p₃)

  def Fermat's_last_theorem : Prop := ¬ (∃ (a b c n: ℕ),
    a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ (a^n + b^n = c^n))
end ex4


section ex5
  variables (α : Type) (p q : α → Prop)
  -- assume that at α has at least one element
  variable a : α
  variable r : Prop


  -- exists elimination
  example : (∃ x : α, r) → r :=
    assume h: ∃ x: α, r,
    match h with ⟨_, hw⟩ :=
      hw
    end

  -- exists introduction
  example : r → (∃ x : α, r) :=
    assume hr: r,
    -- using assumption about non-emptiness of α here
    exists.intro a hr

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r :=
  iff.intro
    (assume h: (∃ x, p x ∧ r),
      match h with ⟨x, hpr⟩ :=
        ⟨⟨x, hpr.left⟩, hpr.right⟩
      end)
    (assume h: (∃ x, p x) ∧ r,
      match h.left with ⟨x, hp⟩ :=
        ⟨x, hp, h.right⟩
      end)

  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    iff.intro
      (assume h: ∃ x, p x ∨ q x,
        match h with ⟨x, hpq⟩ :=
          or.elim hpq
            (assume hp: p x,
            or.inl ⟨x, hp⟩)
            (assume hq: q x,
            or.inr ⟨x, hq⟩)
        end)
      (assume h: (∃ x, p x) ∨ (∃ x, q x),
        or.elim h
          (assume hxp: ∃ x, p x,
          match hxp with ⟨x, hp⟩ :=
            ⟨x, or.inl hp⟩
          end)
          (assume hxq: ∃ x, q x,
          match hxq with ⟨x, hq⟩ :=
            ⟨x, or.inr hq⟩
          end))


  -- classical reasoning generally needed to show that something exists
  -- but not needed to show "doesn't exist", i.e. ¬(∃ x, blah x)
  -- i guess that's because "doesn't exist" doesn't require constructing an example
  theorem dne {a: Prop} (h: ¬¬a): a :=
    classical.by_cases
      (assume ha: a, ha)
      (assume hna: ¬a, absurd hna h)

  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) :=
    iff.intro
      (assume h: ∀ x, p x,
      assume : ∃ x, ¬p x,
      match this with ⟨x, hnp⟩ :=
        show false, from hnp (h x)
      end)
      (assume h: ¬(∃ x, ¬p x),
      -- forall_not_of_not_exists proven below
      have h1: ∀ x, ¬¬p x, from forall_not_of_not_exists h,
      show ∀ x, p x, from assume x,
      show p x, from dne (h1 x))

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) :=
    iff.intro
      (assume h: ∃ x, p x,
      match h with ⟨x, hp⟩ :=
        assume hno: ∀ x, ¬p x,
        show false, from hno x hp
      end)
      (assume h: ¬(∀ x, ¬p x),
      classical.by_contradiction
        (assume : ¬(∃ x, p x),
        have ∀ x, ¬p x, from forall_not_of_not_exists this,
        show false, from h this))

  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) :=
    iff.intro
      (assume h: ¬∃ x, p x,
      assume x, assume hp: p x,
      have ∃ x, p x, from ⟨x, hp⟩,
      h this)
      (assume h: ∀ x, ¬p x,
      assume : ∃ x, p x,
      match this with ⟨x, hp⟩ :=
        h x hp
      end)

  example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) :=
    iff.intro
      (assume h: ¬∀ x, p x,
      classical.by_contradiction
        (assume : ¬(∃ x, ¬p x),
        have ∀ x, ¬¬p x, from forall_not_of_not_exists this,
        have ∀ x, p x, from assume x, dne (this x),
        show false, from h this))
      (assume h: ∃ x, ¬p x,
      match h with ⟨x, _⟩ :=
        assume hno: ∀ x, p x,
        have p x, from hno x,
        ‹¬p x› this
      end)


  example : (∀ x, p x → r) ↔ (∃ x, p x) → r :=
    iff.intro
      (assume h: ∀ x, p x → r,
      assume : ∃ x, p x,
      match this with ⟨x, hp⟩ :=
        h x hp
      end)
      (assume h: (∃ x, p x) → r,
      assume x,
      assume : p x,
      h ⟨x, this⟩)

  -- assume decidability of propositions from now on
  local attribute [instance] classical.prop_decidable

  example : (∃ x, p x → r) ↔ (∀ x, p x) → r :=
    iff.intro
      (assume ⟨x, hpr⟩,
      assume : ∀ x, p x,
      have p x, from this x,
      show r, from hpr this)
      (assume h: (∀ x, p x) → r,
      classical.by_contradiction
        (assume : ¬(∃ x, p x → r),
        have ∀ x, ¬(p x → r), from forall_not_of_not_exists this,
        have ∀ x, p x ∧ ¬r, from assume x, not_imp.mp (this x),
        have (∀ x, p x) ∧ ¬r, from and.intro
          (assume x, (this x).left)
          -- need non-emptiness of α
          (this a).right,
        show false, from this.right (h this.left)))

  example : (∃ x, r → p x) ↔ (r → ∃ x, p x) :=
    iff.intro
      (assume h: ∃ x, r → p x,
      match h with ⟨x, hrp⟩ :=
        assume hr: r,
        ⟨x, hrp hr⟩
      end)
      (assume h: r → ∃ x, p x,
      classical.by_contradiction
        (assume : ¬(∃ x, r → p x),
        have ∀ x, ¬(r → p x), from forall_not_of_not_exists this,
        have h1: ∀ x, r ∧ ¬p x, from assume x, not_imp.mp (this x),
        -- need non-emptiness of α
        have ∃ x, p x, from h (h1 a).left,
        have h2: ¬(∀ x, ¬p x), from not_forall_not.mpr this,
        have h3: ∀ x, ¬p x, from assume x, (h1 x).right,
        show false, from h2 h3))
end ex5


section ex6
  variables (real : Type) [ordered_ring real]
  variables (log exp : real → real)
  variable  log_exp_eq : ∀ x, log (exp x) = x
  variable  exp_log_eq : ∀ {x}, x > 0 → exp (log x) = x
  variable  exp_pos    : ∀ x, exp x > 0
  variable  exp_add    : ∀ x y, exp (x + y) = exp x * exp y

  -- this ensures the assumptions are available in tactic proofs
  include log_exp_eq exp_log_eq exp_pos exp_add

  example (x y z : real) :
    exp (x + y + z) = exp x * exp y * exp z :=
  by rw [exp_add, exp_add]

  example (y : real) (h : y > 0)  : exp (log y) = y :=
  exp_log_eq h

  theorem log_mul {x y : real} (hx : x > 0) (hy : y > 0) :
    log (x * y) = log x + log y :=
  calc
    log (x * y) = log (exp (log x) * y)           : by rw exp_log_eq hx
    ...         = log (exp (log x) * exp (log y)) : by rw exp_log_eq hy
    ...         = log (exp (log x + log y))       : by rw exp_add
    ...         = log x + log y                   : by rw log_exp_eq
end ex6


section ex7
  #check sub_self

  example (x : ℤ) : x * 0 = 0 :=
  calc
    x * 0 = x * (x - x)   : by rw sub_self
    ...   = x * x - x * x : by rw mul_sub
    ...   = 0             : by rw sub_self
end ex7
