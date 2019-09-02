variables {p11 p21 p31 p12 p22 p32 : Prop}

lemma second_elim2 (h: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32)) (h1: p12) (h2: p21) : 
            (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32) :=
show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
from or.elim (h.right.right)
    (assume : p31, 
    show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
        from or.inr (or.inr (or.inl (and.intro h2 this))))
    (assume : p32,
    show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
        from or.inr (or.inr (or.inr (or.inr (or.inl (and.intro h1 this))))))
     

lemma second_elim1 (h: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32)) (h1: p11) (h2: p22) : 
            (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32) :=
show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
from or.elim (h.right.right)
    (assume : p31, 
    show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
        from or.inr (or.inl (and.intro h1 this)))
    (assume : p32,
    show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
        from or.inr (or.inr (or.inr (or.inr (or.inr (and.intro h2 this))))))

lemma first_elim2 (h: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32)) (h1: p12) : 
            (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32) :=
show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32), 
    from or.elim (h.right.left)
        (assume : p21,
        show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
            from second_elim2 h h1 this)
        (assume : p22,
        show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
            from or.inr (or.inr (or.inr (or.inl (and.intro h1 this)))))

lemma first_elim1 (h: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32)) (h1: p11) : 
            (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32) :=
show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32), 
    from or.elim (h.right.left)
        (assume : p21,
        show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
            from or.inl (and.intro h1 this))
        (assume : p22,
        show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
            from second_elim1 h h1 this)

theorem pigeons: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32) → 
         (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨  (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32) :=
assume h: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32),
show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32),
    from or.elim (h.left)
        (assume : p11, 
        show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32), 
            from first_elim1 h this)
        (assume : p12, 
        show (p11 ∧ p21) ∨ (p11 ∧ p31) ∨ (p21 ∧ p31) ∨ (p12 ∧ p22) ∨ (p12 ∧ p32) ∨ (p22 ∧ p32), 
            from first_elim2 h this)