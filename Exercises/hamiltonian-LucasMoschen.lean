-- Considerarei um grafo de 4 vértices A, B, C, D, com arestas AB, BC, AD e BD
-- Veja que um caminho Hamiltoniano possível é D -> A -> B -> C 
-- Farei A = 1, B = 2, C = 3, D = 4
-- Logo G = ((1,2),(2,3),(1,4),(2,4))

-- Lembrando que xij é: a i-ésima posição no caminho é ocupada pelo j-ésimo nó.  

variables {x11 x12 x13 x14 x21 x22 x23 x24 x31 x32 x33 x34 x41 x42 x43 x44: Prop}

-- Condition 1
variable f1: x11 ∨ x21 ∨ x31 ∨ x41 
variable f2: x12 ∨ x22 ∨ x32 ∨ x42
variable f3: x13 ∨ x23 ∨ x33 ∨ x43
variable f4: x14 ∨ x24 ∨ x34 ∨ x44
-- Condition 2
variable g1: (¬ x11 ∨ ¬ x21) ∧ (¬ x11 ∨ ¬ x31) ∧ (¬ x11 ∨ ¬ x41) ∧ (¬ x21 ∨ ¬ x31) ∧ 
             (¬ x21 ∨ ¬ x41) ∧ (¬ x31 ∨ ¬ x41)
variable g2: (¬ x12 ∨ ¬ x22) ∧ (¬ x12 ∨ ¬ x32) ∧ (¬ x12 ∨ ¬ x42) ∧ (¬ x22 ∨ ¬ x32) ∧ 
             (¬ x22 ∨ ¬ x42) ∧ (¬ x32 ∨ ¬ x42)
variable g3: (¬ x13 ∨ ¬ x23) ∧ (¬ x13 ∨ ¬ x33) ∧ (¬ x13 ∨ ¬ x43) ∧ (¬ x23 ∨ ¬ x33) ∧ 
             (¬ x23 ∨ ¬ x43) ∧ (¬ x33 ∨ ¬ x43)
variable g4: (¬ x14 ∨ ¬ x24) ∧ (¬ x14 ∨ ¬ x34) ∧ (¬ x14 ∨ ¬ x44) ∧ (¬ x24 ∨ ¬ x34) ∧ 
             (¬ x24 ∨ ¬ x44) ∧ (¬ x34 ∨ ¬ x44)
-- Condition 3
variable h1: x11 ∨ x12 ∨ x13 ∨ x14
variable h2: x21 ∨ x22 ∨ x23 ∨ x24
variable h3: x31 ∨ x32 ∨ x33 ∨ x34 
variable h4: x41 ∨ x42 ∨ x43 ∨ x44
-- Consition 4
variable i1: (¬ x11 ∨ ¬ x12) ∧ (¬ x11 ∨ ¬ x13) ∧ (¬ x11 ∨ ¬ x14) ∧ (¬ x12 ∨ ¬ x13) ∧ 
             (¬ x12 ∨ ¬ x14) ∧ (¬ x13 ∨ ¬ x14)
variable i2: (¬ x21 ∨ ¬ x22) ∧ (¬ x21 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x24) ∧ (¬ x22 ∨ ¬ x23) ∧ 
             (¬ x22 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x24)
variable i3: (¬ x31 ∨ ¬ x32) ∧ (¬ x31 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x34) ∧ (¬ x32 ∨ ¬ x33) ∧ 
             (¬ x32 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x34)
variable i4: (¬ x41 ∨ ¬ x42) ∧ (¬ x41 ∨ ¬ x43) ∧ (¬ x41 ∨ ¬ x44) ∧ (¬ x42 ∨ ¬ x43) ∧ 
             (¬ x42 ∨ ¬ x44) ∧ (¬ x43 ∨ ¬ x44)
-- Condition 5: (1,3), (3,4) não pertencem a G
variable j1: (¬ x11 ∨ ¬ x23) ∧ (¬ x21 ∨ ¬ x33) ∧ (¬ x31 ∨ ¬ x43) ∧  
             (¬ x13 ∨ ¬ x21) ∧ (¬ x23 ∨ ¬ x31) ∧ (¬ x33 ∨ ¬ x41)
variable j2: (¬ x13 ∨ ¬ x24) ∧ (¬ x23 ∨ ¬ x34) ∧ (¬ x33 ∨ ¬ x44) ∧  
             (¬ x14 ∨ ¬ x23) ∧ (¬ x24 ∨ ¬ x33) ∧ (¬ x34 ∨ ¬ x43)

theorem hamiltonian : x14 ∧ x21 ∧ x32 ∧ x43 :=
show x14 ∧ x21 ∧ x32 ∧ x43, from sorry

             