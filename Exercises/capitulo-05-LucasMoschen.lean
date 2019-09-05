variables {A B C D E F P Q R : Prop}

namespace theorems 

	theorem or_simplification_right (A B : Prop) : (A ∨ B) ∧ ¬ B → A :=
	assume h1: (A ∨ B) ∧ ¬ B,
	show A, from or.elim (and.left h1)
	   (assume h: A, show A, from h)
	   (assume h: B, show A, from false.elim (and.right h1 h))

	theorem or_simplification_left (A B : Prop) : (A ∨ B) ∧ ¬ A → B :=
	assume h1: (A ∨ B) ∧ ¬ A,
	show B, from or.elim (and.left h1)
	   (assume h: A, show B, from false.elim (and.right h1 h))
	   (assume h: B, show B, from h)

	theorem and_simplification_left (A B: Prop) : ¬ (A ∧ B) ∧ A → ¬ B :=
	assume h: ¬ (A ∧ B) ∧ A,
	assume h1: B,
	show false, from h.left (and.intro h.right h1)

end theorems 

-- exercício 1

variable h: ¬ A → false

example (h1: A ∨ ¬ A) : A :=
have h2: ¬¬ A, from
  assume a : ¬ A,
  show false, from h a,
show A, from theorems.or_simplification_right A (¬ A) (and.intro h1 h2)

-- exercício 2

example (h: ¬ A ∨ ¬ B): ¬ (A ∧ B) :=
show ¬ (A ∧ B), from or.elim h
    (assume h1: ¬ A, assume h2: A ∧ B, show false, from h1 (and.left h2))
    (assume h1: ¬ B, assume h2: A ∧ B, show false, from h1 (and.right h2))

open classical

-- exercício 3

example (h: ¬ (A ∧ B)): ¬ A ∨ ¬ B :=
show ¬ A ∨ ¬ B, from or.elim (em A) 
    (assume h1: A, show ¬ A ∨ ¬ B, from 
       or.inr (theorems.and_simplification_left A B (and.intro h h1)))
    (assume h1: ¬ A, show ¬ A ∨ ¬ B, from or.inl h1)

-- exercício 4

example (h1: ¬ P → (Q ∨ R)) (h2: ¬ Q) (h3: ¬ R): P :=
show P, from by_contradiction 
    (assume h: ¬ P, show false, 
        from h3 (theorems.or_simplification_left Q R (and.intro (h1 h) h2)))

-- exercício 5 

example (h: A → B): ¬ A ∨ B :=
show ¬ A ∨ B, from or.elim (em A)
   (assume h1: A, show ¬ A ∨ B, from or.inr (h h1))
   (assume h1: ¬A, show ¬ A ∨ B, from or.inl h1)

-- exercício 6

example : A → ((A ∧ B) ∨ (A ∧ ¬ B)) :=
assume h: A,
show ((A ∧ B) ∨ (A ∧ ¬ B)), from or.elim (em B)
    (assume h1: B, show ((A ∧ B) ∨ (A ∧ ¬ B)), from or.inl (and.intro h h1))
    (assume h1: ¬B, show ((A ∧ B) ∨ (A ∧ ¬ B)), from or.inr (and.intro h h1))

-- exercício 7

-- Eu concluo que de (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F), chego em  (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ 
-- (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F)
-- Mostrei como derivei essa afirmação, mesmo que não foi o pedido. 

variable disjuntive: (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
                     (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) 

lemma step_6 (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) (h1: B) (h2: D) :  
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.right.right)
        (assume : E, 
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inr (or.inr (or.inr (or.inr (or.inr(or.inl (and.intro h1 (and.intro h2 this)))))))))
        (assume : F,
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inr (or.inr (or.inr (or.inr (or.inr (or.inr (and.intro h1 (and.intro h2 this))))))))) 

lemma step_5 (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) (h1: B) (h2: C) :  
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.right.right)
        (assume : E, 
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inr (or.inr (or.inr (or.inl (and.intro h1 (and.intro h2 this)))))))
        (assume : F,
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inr (or.inr (or.inr (or.inr (or.inl (and.intro h1 (and.intro h2 this)))))))) 

lemma step_4 (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) (h1: A) (h2: D) :  
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.right.right)
        (assume : E, 
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inr (or.inl (and.intro h1 (and.intro h2 this)))))
        (assume : F,
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inr (or.inr (or.inl (and.intro h1 (and.intro h2 this))))))       

lemma step_3 (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) (h1: A) (h2: C) :  
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.right.right)
        (assume : E, 
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inl (and.intro h1 (and.intro h2 this)))
        (assume : F,
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from or.inr (or.inl (and.intro h1 (and.intro h2 this))))

lemma step_2 (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) (h1: B) :  
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.right.left)
        (assume : C, 
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from step_5 h h1 this)
        (assume : D,
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from step_6 h h1 this)     

lemma step_1 (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) (h1: A) :  
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.right.left)
        (assume : C, 
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from step_3 h h1 this)
        (assume : D,
        show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
            (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
            from step_4 h h1 this)

example (h: (A ∨ B) ∧ (C ∨ D) ∧ (E ∨ F)) : 
        (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F) :=
show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
     (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
    from or.elim (h.left) 
    (assume : A, 
    show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
         (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
         from step_1 h this)
    (assume : B,
    show (A ∧ C ∧ E) ∨ (A ∧ C ∧ F) ∨ (A ∧ D ∧ E) ∨ (A ∧ D ∧ F) ∨ 
        (B ∧ C ∧ E) ∨ (B ∧ C ∧ F) ∨ (B ∧ D ∧ E) ∨ (B ∧ D ∧ F),
        from step_2 h this)

-- exercício 8

lemma step1 (h₁ : ¬ (A ∧ B)) (h₂ : A) : ¬ A ∨ ¬ B :=
have ¬ B, from  
   assume : B,
   have A ∧ B, from (and.intro h₂ this),
   show false, from h₁ this, 
show ¬ A ∨ ¬ B, from or.inr this

lemma step2 (h₁ : ¬ (A ∧ B)) (h₂ : ¬ (¬ A ∨ ¬ B)) : false :=
have ¬ A, from
  assume : A,
  have ¬ A ∨ ¬ B, from step1 h₁ ‹A›,
  show false, from h₂ this,
show false, from h₂ (or.inl ‹¬A›) 

theorem step3 (h : ¬ (A ∧ B)) : ¬ A ∨ ¬ B :=
by_contradiction
  (assume h' : ¬ (¬ A ∨ ¬ B),
    show false, from step2 h h')

-- exercício 9

example (h : ¬ B → ¬ A) : A → B :=
assume h1: A,
show B, from or.elim (em B)
    (assume : B, show B, from this)
    (assume : ¬ B, show B, from by_contradiction
        (assume : ¬ B, show false, from (h this) h1)) 

example (h : A → B) : ¬ A ∨ B :=
show ¬ A ∨ B, from or.elim (em A)
   (assume h1: A, show ¬ A ∨ B, from or.inr (h h1))
   (assume h1: ¬A, show ¬ A ∨ B, from or.inl h1)