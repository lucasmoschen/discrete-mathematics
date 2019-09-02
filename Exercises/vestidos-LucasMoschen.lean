variables AA AB AP MA MB MP CA CB CP : Prop

--estas variáveis são suposições naturais. 
--Existem várias outras, mas não são necessárias no momento. 
variables (h1 : AP ↔ ¬ AA ∧ ¬ AB)
          (h2 : AA ↔ ¬ AB ∧ ¬ AP)
          (h3 : AB ↔ ¬ AA ∧ ¬ AP)
          (h4 : MB ↔ ¬ AB ∧ ¬ CB)
          (h5 : MA ↔ (AP ∧ CB) ∨ (AB ∧ CP))

-- estas variáveis são as falas, vistas do ponto de Ana.
-- Como Ana sempre diz a verdade, todas essas afirmações são verdadeiras.
-- Considerar as falas de Maria não faz sentido do ponto de vista lógico. 
variables (f1: AA → AB)
          (f2: AB → MB)
          (f3: AP → CB)

def triple_and(A B C: Prop): Prop :=
(A ∧ B) ∧ C

example : triple_and AP CB MA :=  -- quero provar que Ana usa preto, 
                                  -- Cláudia usa branco e 
                                  -- Maria usa azul
have  a1: ¬ AA, from
   assume a2: AA, 
   have a3: AB, from f1 a2,
   have a4: ¬AA, from and.left (iff.elim_left h3 a3),
   show false, from a4 a2,
   
have a5: ¬ AB, from 
  assume a6: AB, 
  have a7: MB, from f2 a6,
  have a8: ¬ AB, from and.left (iff.elim_left h4 a7),
  show false, from a8 a6,

have a9: AP, from iff.elim_right h1 (and.intro a1 a5),

have c1: CB, from f3 a9,

have u1: AP ∧ CB, from and.intro a9 c1,

have m1: MA, from iff.elim_right h5 (or.inl u1),

show (AP ∧ CB) ∧ MA, from and.intro u1 m1

