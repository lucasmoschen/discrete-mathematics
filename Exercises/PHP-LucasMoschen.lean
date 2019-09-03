variables {p11 p21 p31 p12 p22 p32 : Prop}

-- esses dois lemas, que eu chamo de segundos, fazem o processo de eliminação para p31 e p32. 
-- O processo nas três eliminações é o mesmo.

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

-- Demonstro supondo p11 no primeiro e p12 no segundo. 
-- Mais uma vez utilizo a ideia da eliminação da união, agora de p21, p22
-- Note que as introduçõs tornam-se complexas pois tenho que inserir um ou no meio de outros.

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

-- Eu quero provar a seguinte aplicação. A ideia é utilizar a eliminação da união de p11 e p12.
-- Para cada um deles, abrir nas possibilidades onde p21 e p22 passam pelo mesmo processo. 

theorem pigeons3: (p11 ∨ p12) ∧ (p21 ∨ p22) ∧ (p31 ∨ p32) → 
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