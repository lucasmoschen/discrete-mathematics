variables A B C D : Prop

example : A ∧ (A → B) → B :=
assume : A ∧ (A → B),
show B, from (and.right this) (and.left this)

example : A → ¬ (¬ A ∧ B) :=
assume h: A,
assume h₁ : ¬A ∧ B,
show false, from (and.left h₁) h 

example : ¬ (A ∧ B) → (A → ¬ B) :=
assume h: ¬ (A ∧ B),
assume h₁ : A,
assume h₂ : B,
show false, from h (and.intro h₁ h₂) 

example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
show C ∨ D, 
  from or.elim h₁ 
    (assume h: A, show C ∨ D, from or.inl (h₂ h))
    (assume h: B, show C ∨ D, from or.inr (h₃ h))

theorem or_resolve_left (h1 : A ∨ B) (h2 : ¬ A) : B :=
or.elim h1
  (assume h3 : A, show B, from false.elim (h2 h3))
  (assume h3 : B, show B, from h3)

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=
assume h₁ : A ∨ B,
show false, 
  from or.elim h₁ 
    (assume h₂ : A, show false, from (and.left h) h₂)
    (assume h₂ : B, show false, from (and.right h) h₂)


open classical 

example : ¬ (A ↔ ¬ A) :=
assume h1 : A ↔ ¬ A,
have h2: ¬A, from
  assume h4: A,
  have h5: ¬ A, from iff.elim_left h1 h4,
  show false, from h5 h4,
have h3: A, from
  by_contradiction
    (assume h: ¬A, 
    have h6: A, from iff.elim_right h1 h,
    show false, from h h6),
show false, from h2 h3