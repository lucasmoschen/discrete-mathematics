variables A B C: Prop

section 
    variable h1: A → B
    variable h2: B → C
    example: A → C :=
    assume h: A, 
    show C, from  h2 (h1 h)  
end

section
    example: (A → (B → C)) → (A ∧ B → C) :=
    assume h1: (A → (B → C)),
    assume h2: A ∧ B,
    show C, from h1 (and.left h2) (and.right h2) 
end

section
    example: A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
    assume h: A ∧ (B ∨ C),
    or.elim (and.right h)
    (assume h1: B,
    show (A ∧ B) ∨ (A ∧ C), 
      from or.inl (and.intro (and.left h) h1))
    (assume h1: C,
    show (A ∧ B) ∨ (A ∧ C),
      from or.inr (and.intro (and.left h) h1))
end