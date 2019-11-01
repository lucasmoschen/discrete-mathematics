-- Lista 7: Capítulo 14

-- Lucas Moschen

-- Exercício 1

section
    parameters {A : Type} {R : A → A → Prop}
    parameter (irreflR : irreflexive R)
    parameter (transR : transitive R)

    variables a b c : A

    local infix < := R

    def R' (a b : A) : Prop := R a b ∨ a = b
    local infix ≤ := R'

    theorem reflR' (a : A) : a ≤ a := 
    begin
        have h1: a = a, from eq.refl a,
        apply or.inr h1
    end

    theorem transR' {a b c : A} (h1 : a ≤ b) (h2 : b ≤ c):
    a ≤ c :=
    or.elim h1
        (assume h3: a < b, or.elim h2 
                (assume h4: b < c, or.inl (transR h3 h4))
                (assume h4: b = c, eq.subst h4 h1))
        (assume h3: a = b, eq.subst (eq.symm h3) h2) 

    theorem antisymmR' {a b : A} (h1 : a ≤ b) (h2 : b ≤ a) :
    a = b :=
    or.elim h1 
        (assume h: a < b, or.elim h2
            (assume h3: b < a, false.elim ((irreflR b) (transR h3 h))) 
            (assume h3: b = a, eq.symm h3))
        (assume h: a = b, h)
end

-- Exercício 2

section
    parameters {A : Type} {R : A → A → Prop}
    parameter (reflR : reflexive R)
    parameter (transR : transitive R)

    def S (a b : A) : Prop := R a b ∧ R b a

    example : transitive S :=
        assume x y z,
        assume h1 h2,
        and.intro (transR h1.left h2.left) (transR h2.right h1.right)
end

-- Exercício 3

section
  parameters {A : Type} {a b c : A} {R : A → A → Prop}
  parameter (Rab : R a b)
  parameter (Rbc : R b c)
  parameter (nRac : ¬ R a c)

  -- Prove one of the following two theorems:

  theorem R_is_not_strict_partial_order :
    ¬(irreflexive R ∧ transitive R) :=
  assume h: irreflexive R ∧ transitive R, 
  show false, from nRac (h.right Rab Rbc)
end

-- Exercício 4
