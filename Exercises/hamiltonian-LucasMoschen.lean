-- Considerarei um grafo de 4 vértices A, B, C, D, com arestas AB, BC, AD e BD
-- Veja que um caminho Hamiltoniano possível é D -> A -> B -> C 
-- Farei A = 1, B = 2, C = 3, D = 4
-- Logo G = ((1,2),(2,3),(1,4),(2,4))

-- Lembrando que xij é: a i-ésima posição no caminho é ocupada pelo j-ésimo nó.  

variables {x11 x12 x13 x14 x21 x22 x23 x24 x31 x32 x33 x34 x41 x42 x43 x44: Prop}

-- Quero provar que esse caminho é Hamiltoniano, logo essa sequência de "And's" é satisfeita. 
variable path:  x14 ∧ x21 ∧ x32 ∧ x43

-- Também queremos que: 
variable not_path: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                   ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44 

-- Vou demostrar que esse caminho satisfaz todas as condições

lemma condition1 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                 ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) : 
(x11 ∨ x21 ∨ x31 ∨ x41) ∧ (x12 ∨ x22 ∨ x32 ∨ x42) ∧ (x13 ∨ x23 ∨ x33 ∨ x43) ∧ (x14 ∨ x24 ∨ x34 ∨ x44) :=
have h1: (x11 ∨ x21 ∨ x31 ∨ x41), from or.inr (or.inl p.right.left),
have h2: (x12 ∨ x22 ∨ x32 ∨ x42), from or.inr (or.inr (or.inl (p.right.right.left))),
have h3: (x13 ∨ x23 ∨ x33 ∨ x43), from or.inr (or.inr (or.inr (p.right.right.right))),
have h4: (x14 ∨ x24 ∨ x34 ∨ x44), from or.inl p.left,
show (x11 ∨ x21 ∨ x31 ∨ x41) ∧ (x12 ∨ x22 ∨ x32 ∨ x42) ∧ 
     (x13 ∨ x23 ∨ x33 ∨ x43) ∧ (x14 ∨ x24 ∨ x34 ∨ x44),
     from  and.intro h1 (and.intro h2 (and.intro h3 h4))
                                    
lemma condition2_node1 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x12 ∨ ¬ x22) ∧ (¬ x12 ∨ ¬ x32) ∧ (¬ x12 ∨ ¬ x42) ∧ (¬ x22 ∨ ¬ x32) ∧ (¬ x22 ∨ ¬ x42) ∧ (¬ x32 ∨ ¬ x42) :=
have h1: ¬ x12, from np.right.left,
have h2: ¬ x22, from np.right.right.right.left,
have h3: ¬ x42, from np.right.right.right.right.right.right.right.right.right.right.left,
show  (¬ x12 ∨ ¬ x22) ∧ (¬ x12 ∨ ¬ x32) ∧ (¬ x12 ∨ ¬ x42) ∧ 
      (¬ x22 ∨ ¬ x32) ∧ (¬ x22 ∨ ¬ x42) ∧ (¬ x32 ∨ ¬ x42), 
      from and.intro (or.inl h1) (and.intro (or.inl h1) (and.intro (or.inl h1) 
           (and.intro (or.inl h2) (and.intro (or.inr h3) (or.inr h3)))))

lemma condition2_node2 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x11 ∨ ¬ x21) ∧ (¬ x11 ∨ ¬ x31) ∧ (¬ x11 ∨ ¬ x41) ∧ (¬ x21 ∨ ¬ x31) ∧ (¬ x21 ∨ ¬ x41) ∧ (¬ x31 ∨ ¬ x41) :=
have h1: ¬ x11, from np.left,
have h2: ¬ x31, from np.right.right.right.right.right.right.left,
have h3: ¬ x41, from np.right.right.right.right.right.right.right.right.right.left,
show  (¬ x11 ∨ ¬ x21) ∧ (¬ x11 ∨ ¬ x31) ∧ (¬ x11 ∨ ¬ x41) ∧ 
      (¬ x21 ∨ ¬ x31) ∧ (¬ x21 ∨ ¬ x41) ∧ (¬ x31 ∨ ¬ x41), 
      from and.intro (or.inl h1) (and.intro (or.inl h1) (and.intro (or.inl h1) 
           (and.intro (or.inr h2) (and.intro (or.inr h3) (or.inl h2)))))

lemma condition2_node3 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x13 ∨ ¬ x23) ∧ (¬ x13 ∨ ¬ x33) ∧ (¬ x13 ∨ ¬ x43) ∧ (¬ x23 ∨ ¬ x33) ∧ (¬ x23 ∨ ¬ x43) ∧ (¬ x33 ∨ ¬ x43) :=
have h1: ¬ x13, from np.right.right.left,
have h2: ¬ x23, from np.right.right.right.right.left,
have h3: ¬ x33, from np.right.right.right.right.right.right.right.left,
show  (¬ x13 ∨ ¬ x23) ∧ (¬ x13 ∨ ¬ x33) ∧ (¬ x13 ∨ ¬ x43) ∧ 
      (¬ x23 ∨ ¬ x33) ∧ (¬ x23 ∨ ¬ x43) ∧ (¬ x33 ∨ ¬ x43), 
      from and.intro (or.inl h1) (and.intro (or.inl h1) (and.intro (or.inl h1) 
           (and.intro (or.inl h2) (and.intro (or.inl h2) (or.inl h3)))))

lemma condition2_node4 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x14 ∨ ¬ x24) ∧ (¬ x14 ∨ ¬ x34) ∧ (¬ x14 ∨ ¬ x44) ∧ (¬ x24 ∨ ¬ x34) ∧ (¬ x24 ∨ ¬ x44) ∧ (¬ x34 ∨ ¬ x44) :=
have h1: ¬ x24, from np.right.right.right.right.right.left,
have h2: ¬ x34, from np.right.right.right.right.right.right.right.right.left,
have h3: ¬ x44, from np.right.right.right.right.right.right.right.right.right.right.right,
show  (¬ x14 ∨ ¬ x24) ∧ (¬ x14 ∨ ¬ x34) ∧ (¬ x14 ∨ ¬ x44) ∧ 
      (¬ x24 ∨ ¬ x34) ∧ (¬ x24 ∨ ¬ x44) ∧ (¬ x34 ∨ ¬ x44), 
      from and.intro (or.inr h1) (and.intro (or.inr h2) (and.intro (or.inr h3) 
           (and.intro (or.inl h1) (and.intro (or.inr h3) (or.inl h2)))))

lemma condition3 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                 ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(x11 ∨ x12 ∨ x13 ∨ x14) ∧ (x21 ∨ x22 ∨ x23 ∨ x24) ∧ (x31 ∨ x32 ∨ x33 ∨ x34) ∧ (x41 ∨ x42 ∨ x43 ∨ x44) :=
show (x11 ∨ x12 ∨ x13 ∨ x14) ∧ (x21 ∨ x22 ∨ x23 ∨ x24) ∧ 
     (x31 ∨ x32 ∨ x33 ∨ x34) ∧ (x41 ∨ x42 ∨ x43 ∨ x44),
     from and.intro (or.inr(or.inr(or.inr(p.left)))) 
                    (and.intro (or.inl(p.right.left))
                               (and.intro (or.inr(or.inl(p.right.right.left)))
                                          (or.inr(or.inr(or.inl(p.right.right.right))))))

lemma condition4_position1 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x11 ∨ ¬ x12) ∧ (¬ x11 ∨ ¬ x13) ∧ (¬ x11 ∨ ¬ x14) ∧ (¬ x12 ∨ ¬ x13) ∧ (¬ x12 ∨ ¬ x14) ∧ (¬ x13 ∨ ¬ x14) :=
have h1: ¬ x11, from np.left,
have h2: ¬ x12, from np.right.left,
have h3: ¬ x13, from np.right.right.left,
show  (¬ x11 ∨ ¬ x12) ∧ (¬ x11 ∨ ¬ x13) ∧ (¬ x11 ∨ ¬ x14) ∧ 
      (¬ x12 ∨ ¬ x13) ∧ (¬ x12 ∨ ¬ x14) ∧ (¬ x13 ∨ ¬ x14), 
      from and.intro (or.inl h1) (and.intro (or.inl h1) (and.intro (or.inl h1) 
           (and.intro (or.inl h2) (and.intro (or.inl h2) (or.inl h3))))) 

lemma condition4_position2 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x21 ∨ ¬ x22) ∧ (¬ x21 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x24) ∧ (¬ x22 ∨ ¬ x23) ∧ (¬ x22 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x24) :=
have h1: ¬ x22, from np.right.right.right.left,
have h2: ¬ x23, from np.right.right.right.right.left,
have h3: ¬ x24, from np.right.right.right.right.right.left,
show  (¬ x21 ∨ ¬ x22) ∧ (¬ x21 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x24) ∧ 
      (¬ x22 ∨ ¬ x23) ∧ (¬ x22 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x24), 
      from and.intro (or.inr h1) (and.intro (or.inr h2) (and.intro (or.inr h3) 
           (and.intro (or.inl h1) (and.intro (or.inl h1) (or.inl h2))))) 

lemma condition4_position3 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x31 ∨ ¬ x32) ∧ (¬ x31 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x34) ∧ (¬ x32 ∨ ¬ x33) ∧ (¬ x32 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x34) :=
have h1: ¬ x31, from np.right.right.right.right.right.right.left,
have h2: ¬ x33, from np.right.right.right.right.right.right.right.left,
have h3: ¬ x34, from np.right.right.right.right.right.right.right.right.left,
show  (¬ x31 ∨ ¬ x32) ∧ (¬ x31 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x34) ∧ 
      (¬ x32 ∨ ¬ x33) ∧ (¬ x32 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x34), 
      from and.intro (or.inl h1) (and.intro (or.inl h1) (and.intro (or.inl h1) 
           (and.intro (or.inr h2) (and.intro (or.inr h3) (or.inr h3))))) 

lemma condition4_position4 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :
(¬ x41 ∨ ¬ x42) ∧ (¬ x41 ∨ ¬ x43) ∧ (¬ x41 ∨ ¬ x44) ∧ (¬ x42 ∨ ¬ x43) ∧ (¬ x42 ∨ ¬ x44) ∧ (¬ x43 ∨ ¬ x44) :=
have h1: ¬ x41, from np.right.right.right.right.right.right.right.right.right.left,
have h2: ¬ x42, from np.right.right.right.right.right.right.right.right.right.right.left,
have h3: ¬ x44, from np.right.right.right.right.right.right.right.right.right.right.right,
show  (¬ x41 ∨ ¬ x42) ∧ (¬ x41 ∨ ¬ x43) ∧ (¬ x41 ∨ ¬ x44) ∧ 
      (¬ x42 ∨ ¬ x43) ∧ (¬ x42 ∨ ¬ x44) ∧ (¬ x43 ∨ ¬ x44), 
      from and.intro (or.inl h1) (and.intro (or.inl h1) (and.intro (or.inl h1) 
           (and.intro (or.inl h2) (and.intro (or.inl h2) (or.inr h3)))))                

-- (1,3) e (3,4) não pertencem ao grafo, portanto não podem ser subsequentes.  

lemma condition5_13 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) : 
(¬ x11 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x43) ∧  (¬ x13 ∨ ¬ x21) ∧ (¬ x23 ∨ ¬ x31) ∧ (¬ x33 ∨ ¬ x41) :=
have h1: ¬ x11, from np.left,
have h2: ¬ x13, from np.right.right.left,
have h3: ¬ x31, from np.right.right.right.right.right.right.left,
have h4: ¬ x33, from np.right.right.right.right.right.right.right.left,
show (¬ x11 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x43) ∧ 
     (¬ x13 ∨ ¬ x21) ∧ (¬ x23 ∨ ¬ x31) ∧ (¬ x33 ∨ ¬ x41),
     from and.intro (or.inl h1) (and.intro (or.inr h4) (and.intro (or.inl h3) 
             (and.intro (or.inl h2) (and.intro (or.inr h3) (or.inl h4)))))

lemma condition5_34 (p: x14 ∧ x21 ∧ x32 ∧ x43) (np: ¬ x11 ∧ ¬ x12 ∧ ¬ x13 ∧ ¬ x22 ∧ ¬ x23 ∧ ¬ x24 ∧ 
                                                       ¬ x31 ∧ ¬ x33 ∧ ¬ x34 ∧ ¬ x41 ∧ ¬ x42 ∧ ¬ x44) :  
(¬ x13 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x44) ∧  (¬ x14 ∨ ¬ x23) ∧ (¬ x24 ∨ ¬ x33) ∧ (¬ x34 ∨ ¬ x43) :=
have h1: ¬ x13, from np.right.right.left,
have h2: ¬ x23, from np.right.right.right.right.left,
have h3: ¬ x33, from np.right.right.right.right.right.right.right.left,
have h4: ¬ x34, from np.right.right.right.right.right.right.right.right.left,
show (¬ x13 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x44) ∧ 
     (¬ x14 ∨ ¬ x23) ∧ (¬ x24 ∨ ¬ x33) ∧ (¬ x34 ∨ ¬ x43),
     from and.intro (or.inl h1) (and.intro (or.inl h2) (and.intro (or.inl h3) 
             (and.intro (or.inr h2) (and.intro (or.inr h3) (or.inl h4)))))


