import tactic

inductive SKIBird
  | S
  | K
  | I
  | response (A : SKIBird) (B : SKIBird)

open SKIBird

-- notation for bird response
instance : has_coe_to_fun SKIBird :=
⟨λ _, SKIBird → SKIBird, response⟩

def contains : SKIBird → SKIBird → Prop
  | x (response A B) := (contains x A) ∨ (contains x B)
  | x y := (x = y)

instance decidable_contains (x E : SKIBird) : decidable (contains x E) :=
begin
  induction E with A B hA hB,
  {
    rw contains,
    exact SKIBird.cases_on x (is_true rfl) (is_false (by apply SKIBird.no_confusion)) (is_false (by apply SKIBird.no_confusion))
    (λ (x_A x_B : SKIBird), is_false (by apply SKIBird.no_confusion)),
  },
  {
    rw contains,
    exact SKIBird.cases_on x (is_false (by apply SKIBird.no_confusion)) (is_true rfl) (is_false (by apply SKIBird.no_confusion))
    (λ (x_A x_B : SKIBird), is_false (by apply SKIBird.no_confusion)),
  },
  {
    rw contains,
    exact SKIBird.cases_on x (is_false (by apply SKIBird.no_confusion)) (is_false (by apply SKIBird.no_confusion)) (is_true rfl)
    (λ (x_A x_B : SKIBird), is_false (by apply SKIBird.no_confusion)),
  },
  {
    rw contains,
    cases hA with hfA htA,
    {
      cases hB with hfB htB,
      exact is_false (not_or hfA hfB),
      exact is_true (or.inr htB),
    },
    {
      cases hB with hfB htB,
      exact is_true (or.inl htA),
      exact is_true (or.inr htB),
    }
  },
end

def free_in (x E : SKIBird) : Prop := ¬(contains x E)

instance decidable_free_in 
  (x E : SKIBird)
    : decidable (free_in x E) :=
begin
  exact not.decidable,
end

set_option pp.implicit true
set_option pp.generalized_field_notation false


example : (if (contains K (K I)) then true else false) := trivial