variables A B C: Prop

--IMPLICATION
section 
    example : A → B :=
    assume h : A,
    show B, from sorry
end

section
  variable h1 : A → B
  variable h2 : A

  example : B := h1 h2
end

--CONJUNTION 
section
    variables (h1: A) (h2: B)
    example : A ∧ B := and.intro h1 h2
end

section 
    variable h3: A ∧ B
    example: A :=
    show A, from and.left h3
    example: B := and.right h3
end

--DISJUCTION
section 
    variable (h4: A)
    example: A ∨ B := or.inl h4
    variable (h5: B)
    example: A ∨ B := or.inr h5
end

section 
    variable h5: A ∨ B
    variables (ha: A → C) (hb: B → C)
    example: C := 
    or.elim h5
        (assume h: A,
        show C, from ha h)
        (assume h: B, 
        show C, from hb h)
end


--NEGATION 
section
    example : ¬ A :=
    assume h: A, 
    show false, from sorry
end

section 
    variables (h6: A) (h7: ¬ A)
    example: false := h7 h6 --h6 h7 doesn't work 
end