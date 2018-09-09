import tactic.find -- super useful!


section ex1
  variables {p q r s: Prop}

  -- commutativity of ∧ and ∨
  example : p ∧ q ↔ q ∧ p :=
    iff.intro
      (assume h: p ∧ q, and.intro h.right h.left)
      (assume h: q ∧ p, and.intro h.right h.left)

  -- in one direction
  theorem or_comm_1: p ∨ q → q ∨ p :=
    (assume h: p ∨ q,
      or.elim h
        (assume hp: p, show q ∨ p, from or.inr hp)
        (assume hq: q, show q ∨ p, from or.inl hq))
  example : p ∨ q ↔ q ∨ p :=
    iff.intro
      (@or_comm_1 p q)
      (@or_comm_1 q p)


  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
    iff.intro
      (assume h: (p ∧ q) ∧ r, ⟨h.left.left, h.left.right, h.right⟩)
      (assume h: p ∧ (q ∧ r), ⟨⟨h.left, h.right.left⟩, h.right.right⟩)

  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
    iff.intro
      -- ORs are so much worse to reason about :\
      (assume h: (p ∨ q) ∨ r, or.elim h
        (assume hpq: p ∨ q, or.elim hpq
          (assume hp: p, or.inl hp)
          (assume hq: q, or.inr (or.inl hq)))
        (assume hr: r, or.inr (or.inr hr)))
      (assume h: p ∨ (q ∨ r), or.elim h
        (assume hp: p, or.inl (or.inl hp))
        (assume hqr: q ∨ r, or.elim hqr
          (assume hq: q, or.inl (or.inr hq))
          (assume hr: r, or.inr hr)))


  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
    -- shamelessly pasted from the book
    iff.intro
      (assume h : p ∧ (q ∨ r),
        have hp : p, from h.left,
        or.elim (h.right)
          (assume hq : q,
            show (p ∧ q) ∨ (p ∧ r), from or.inl ⟨hp, hq⟩)
          (assume hr : r,
            show (p ∧ q) ∨ (p ∧ r), from or.inr ⟨hp, hr⟩))
      (assume h : (p ∧ q) ∨ (p ∧ r),
        or.elim h
          (assume hpq : p ∧ q,
            have hp : p, from hpq.left,
            have hq : q, from hpq.right,
            show p ∧ (q ∨ r), from ⟨hp, or.inl hq⟩)
          (assume hpr : p ∧ r,
            have hp : p, from hpr.left,
            have hr : r, from hpr.right,
            show p ∧ (q ∨ r), from ⟨hp, or.inr hr⟩))

  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
    iff.intro
      (assume h : p ∨ (q ∧ r), or.elim h
        (assume hp: p, and.intro (or.inl hp) (or.inl hp))
        (assume hqr: q ∧ r, and.intro (or.inr hqr.left) (or.inr hqr.right)))
      (assume h : (p ∨ q) ∧ (p ∨ r),
        have hpq: p ∨ q, from h.left,
        have hpr: p ∨ r, from h.right,
        or.elim hpq
          (assume hp: p, or.inl hp)
          (assume hq: q, or.elim hpr
            (assume hp: p, or.inl hp)
            (assume hr: r, or.inr (and.intro hq hr))))


  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) :=
    iff.intro
      (assume h: p → (q → r),
      assume hpq: p ∧ q,
      h hpq.left hpq.right)
      (assume h: (p ∧ q → r),
      assume hp: p,
      assume hq: q,
      h (and.intro hp hq))

  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
    iff.intro
      (assume h: (p ∨ q) → r, and.intro
        (assume hp: p, h (or.inl hp))
        (assume hq: q, h (or.inr hq)))
      (assume h: (p → r) ∧ (q → r),
      assume hpq: p ∨ q, or.elim hpq
        (assume hp: p, h.left hp)
        (assume hq: q, h.right hq))

  theorem de_morgan_2 : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
    iff.intro
      (assume h: ¬(p ∨ q), and.intro
        (assume hp: p, absurd (or.inl hp) h)
        (assume hq: q, absurd (or.inr hq) h))
      (assume h: ¬p ∧ ¬q,
      assume hpq: p ∨ q,
      or.elim hpq
        (assume hp: p, absurd hp h.left)
        (assume hq: q, absurd hq h.right))

  example : ¬p ∨ ¬q → ¬(p ∧ q) :=
    assume h: ¬p ∨ ¬q,
    assume hpq: p ∧ q,
    or.elim h
      (assume hnp: ¬p, absurd hpq.left hnp)
      (assume hnq: ¬q, absurd hpq.right hnq)

  theorem non_contradiction : ¬(p ∧ ¬p) :=
    assume h: p ∧ ¬p,
    absurd h.left h.right

  example : p ∧ ¬q → ¬(p → q) :=
    assume h: p ∧ ¬q,
    assume hpq: p → q,
    absurd (hpq h.left) h.right

  example : ¬p → (p → q) :=
    assume hnp: ¬p,
    assume hp: p,
    absurd hp hnp

  theorem or_not_imp: (¬p ∨ q) → (p → q) :=
    assume h: ¬p ∨ q,
    assume hp: p,
    or.elim h
      (assume hnp: ¬p, absurd hp hnp)
      (assume hq: q, hq)

  example : p ∨ false ↔ p :=
    iff.intro
      (assume h: p ∨ false, or.elim h
        (assume hp: p, hp)
        (assume hp: false, false.elim hp))
      (assume h: p, or.inl h)

  example : p ∧ false ↔ false :=
    iff.intro
      (assume h: p ∧ false, false.elim h.right)
      (assume h: false, false.elim h)

  example : (p → q) → (¬q → ¬p) :=
    assume h: p → q,
    assume hnq: ¬q,
    assume hp: p,
    absurd (h hp) hnq


  -- these require classical reasoning
  theorem dne (h: ¬¬p): p :=
    classical.by_cases
      (assume hp: p, hp)
      (assume hnp: ¬p, absurd hnp h)

  -- finds by_contradiction
  #find (¬ _ → false) → _

  -- long proof in classical logic
  theorem de_morgan_1_b: ¬(p ∧ q) → ¬p ∨ ¬q :=
    assume hnpq: ¬(p ∧ q),
    classical.by_contradiction
      (assume not_conclusion: ¬(¬p ∨ ¬q),
        have hpq: p ∧ q, from and.intro
          (show p, from classical.by_contradiction
            (assume hnp: ¬p,
              not_conclusion (show ¬p ∨ ¬q, from or.intro_left (¬q) hnp)))
          (show q, from classical.by_contradiction
            (assume hnq: ¬q,
              not_conclusion (show ¬p ∨ ¬q, from or.intro_right (¬p) hnq))),
        show false, from hnpq hpq)

  -- code-golfy proof using classical logic
  theorem de_morgan_1_b' (hnpq: ¬(p ∧ q)) : ¬p ∨ ¬q :=
    or.elim (classical.em p) (λ hp, or.inr $ λ hq, hnpq ⟨hp, hq⟩) or.inl

  -- proof using decidability assumption on p
  theorem de_morgan_1_b'' (hnpq: ¬(p ∧ q)) [decidable p] : ¬p ∨ ¬q :=
    if hp : p then or.inr (λ hq, hnpq ⟨hp, hq⟩) else or.inl hp

  theorem not_imp : ¬(p → q) → p ∧ ¬q :=
    assume h: ¬(p → q),
    classical.by_contradiction
      (assume hno: ¬(p ∧ ¬q),
      have hnpnnq: ¬p ∨ ¬¬q, from de_morgan_1_b hno,
      have hnpq: ¬p ∨ q, from (or.elim hnpnnq
        (assume hp: ¬p, or.inl hp)
        (assume hq: ¬¬q, or.inr (dne hq))),
      have hno': p → q, from or_not_imp hnpq,
      absurd hno' h)

  example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
    assume h: p → r ∨ s,
    -- absolutely horrific proof, must be some better way
    classical.by_contradiction
      (assume hno: ¬((p → r) ∨ (p → s)),
      have hno': _, from de_morgan_2.mp hno,
      have hnpr: ¬(p → r), from hno'.left,
      have hnps: ¬(p → s), from hno'.right,
      have hpnr: p ∧ ¬r, from not_imp hnpr,
      have hpns: p ∧ ¬s, from not_imp hnps,
      or.elim (h hpnr.left)
        (assume hr: r, absurd hr hpnr.right)
        (assume hs: s, absurd hs hpns.right))

  example : (p → q) → (¬p ∨ q) :=
    assume h: p → q,
    classical.by_contradiction
      (assume hfalse: ¬(¬p ∨ q),
      have hfalse': ¬¬p ∧ ¬q, from de_morgan_2.mp hfalse,
      absurd (h (dne hfalse'.left)) hfalse'.right)

  example : (¬q → ¬p) → (p → q) :=
    assume h: ¬q → ¬p,
    classical.by_contradiction
      (assume hno: ¬(p → q),
      have hpnq: p ∧ ¬q, from not_imp hno,
      absurd hpnq.left (h hpnq.right))

  example : p ∨ ¬p := classical.em p

  example : ((p → q) → p) → p :=
    assume h: ((p → q) → p),
    classical.by_cases
      (assume hpq: (p → q), h hpq)
      (assume hnpq: ¬(p → q),
        have hpnq: p ∧ ¬q, from not_imp hnpq,
        hpnq.left)
end ex1


section ex2
  variable p: Prop

  -- prove ¬(p ↔ ¬p) without using classical logic
  example : ¬(p ↔ ¬p) :=
    assume h: p ↔ ¬p,
    have hnp: ¬p, from
      (assume hp: p,
      have hnp: ¬p, from h.mp hp,
      show false, from hnp hp),
    have hp: p, from h.mpr hnp,
    show false, from hnp hp
end ex2


namespace dne_test
  variable {p: Prop}

  axiom dne (h: ¬¬p): p

  -- derive by_contradiction from dne
  theorem contradict (h: ¬p → false): p :=
    have hnn: ¬¬p, from not.intro h,
    show p, from dne hnn

  -- this seems to say it's unprovable: https://math.stackexchange.com/a/913019
  -- in spite of stack exchange, derive LEM from DNE
  theorem lem: p ∨ ¬p :=
    suffices hp: ¬(p ∨ ¬p) → false, from contradict hp,
    assume hp: ¬(p ∨ ¬p),
    have hnpnnp: ¬p ∧ ¬¬p, from de_morgan_2.mp hp,
    have hp: p, from dne hnpnnp.right,
    have hnp: ¬p, from hnpnnp.left,
    show false, from hnp hp
end dne_test


section de_morgan
  variables {p q: Prop}

  theorem de_morgan_1_a (hnpnq: ¬p ∨ ¬q): ¬(p ∧ q) :=
    assume (hpq: p ∧ q),
    or.elim hnpnq
      (assume hnp: ¬p,
        show false, from hnp hpq.left)
      (assume hnq: ¬q,
        show false, from hnq hpq.right)

  -- mathlib's proof, using equation compiler
  theorem de_morgan_1_a' (hnpnq: ¬p ∨ ¬q): ¬(p ∧ q)
    | ⟨hp, hq⟩ := or.elim hnpnq (absurd hp) (absurd hq)

  theorem de_morgan_1: ¬(p ∧ q) ↔ ¬p ∨ ¬q :=
    -- no longer annpoying, using implicit variables
    iff.intro de_morgan_1_b de_morgan_1_a
  #check de_morgan_1
end de_morgan


-- why is the type Prop "below" normal types? that is, we have
#check ℕ -- Type
#check 1 -- ℕ

#check Prop -- Type
constant p: Prop
#check p -- Prop
constant h: p
#check h -- p <- it's as if "1" was a type
-- kinda answered in section 4.1 of TPIL
