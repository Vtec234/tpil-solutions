import data.list.basic

-- Go back to the exercises in Chapter 3 and Chapter 4 and redo as many as you can now
-- with tactic proofs, using also rw and simp as appropriate.
section ex1
  -- Almost all of these can be proven by `safe` or `solve_iff`:
  meta def solve_iff : tactic unit :=
  `[ apply iff.intro, repeat { safe } ]
  -- So I only left out the ones that couldn't.

  -- chapter 3 automated away

  section chapter4
    -- ex. 1 automated away

    section ex2
      variables (α : Type) (p q : α → Prop)
      variable r : Prop

      example : α → ((∀ x : α, r) ↔ r) := begin
      intro,
        apply iff.intro,
          safe,
          have : r, from a_1 a, -- is it fine to rely on auto-generated names?
          repeat { safe }
      end
    end ex2

    section ex3
      variables (men : Type) (barber : men)
      variable  (shaves : men → men → Prop)

      example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) :
        false := begin
          have h', from h barber,
          safe
        end
    end ex3

    -- ex. 4 contains no proofs

    section ex5
      variables (α : Type) (p q : α → Prop)
      variable a : α
      include a -- use non-emptiness of α in tactic proofs
      variable r : Prop

      example : r → (∃ x : α, r) := begin
        intro,
        apply exists.intro,
        repeat { assumption }
      end

      example : (∃ x, p x → r) ↔ (∀ x, p x) → r := begin
        apply iff.intro,
        safe,
        safe,
        show false, from a_2 a
      end
      example : (∃ x, r → p x) ↔ (r → ∃ x, p x) := begin
        apply iff.intro,
        safe,
        safe,
        show false, from a_2 a
      end
    end ex5

    -- ex. 6 automated away

    -- ex. 7 automated away
  end chapter4
end ex1

-- Use tactic combinators to obtain a one line proof of the following:
section ex2
  example (p q r: Prop) (hp: p) :
    (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
  by simp * -- was i supposed to do something more low-level here? :)
end ex2
