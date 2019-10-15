import data.set
open set

/- 
alunos:
    - Lucas Machado Moschen
-/

-- ex 1

section
    variable U : Type
    variables A B C : set U

    example : ∀ x, x ∈ A ∩ C → x ∈ A ∪ B :=
    assume x,
    assume h: x ∈ A ∩ C,
    show x ∈ A ∪ B, from or.inl h.left

    example : ∀ x, x ∈ -(A ∪ B) → x ∈ -A :=
    assume x, 
    assume : x ∈ -(A ∪ B),
    have ¬ x ∈ (A ∪ B), from this,
    assume : x ∈ A, 
    show false, from ‹¬ x ∈ (A ∪ B)› (or.inl this)
end


-- ex 2

section
    variable {U : Type}

    /- defining "disjoint" -/

    def disj (A B : set U) : Prop := ∀ ⦃x⦄, x ∈ A → x ∈ B → false

    example (A B : set U) (h : ∀ x, ¬ (x ∈ A ∧ x ∈ B)) :
    disj A B :=
    assume x,
    assume h1 : x ∈ A,
    assume h2 : x ∈ B,
    have h3 : x ∈ A ∧ x ∈ B, from and.intro h1 h2,
    show false, from h x h3

    -- notice that we do not have to mention x when applying
    --   h : disj A B
    example (A B : set U) (h1 : disj A B) (x : U)
        (h2 : x ∈ A) (h3 : x ∈ B) :
    false :=
    h1 h2 h3

    -- the same is true of ⊆
    example (A B : set U) (x : U) (h : A ⊆ B) (h1 : x ∈ A) :
    x ∈ B :=
    h h1

    example (A B C D : set U) (h1 : disj A B) (h2 : C ⊆ A)
        (h3 : D ⊆ B) :
    disj C D :=
    assume x,   
    assume g1: x ∈ C,
    assume g2: x ∈ D,
    have g3: x ∈ A, from h2 g1,
    have g4: x ∈ B, from h3 g2, 
    show false, from h1 g3 g4
end

-- ex 3

section 
    variables {I U : Type}
    variables {A : I → set U} {B : I → set U} {C : set U}

    theorem Inter.intro {x : U} (h : ∀ i, x ∈ A i) : x ∈ ⋂ i, A i :=
        by simp; assumption

    @[elab_simple]
    theorem Inter.elim {x : U} (h : x ∈ ⋂ i, A i) (i : I) : x ∈ A i :=
        by simp at h; apply h

    theorem Union.intro {x : U} (i : I) (h : x ∈ A i) :
    x ∈ ⋃ i, A i :=
        by {simp, existsi i, exact h}

    theorem Union.elim {b : Prop} {x : U}
    (h₁ : x ∈ ⋃ i, A i) (h₂ : ∀ (i : I), x ∈ A i → b) : b :=
        by {simp at h₁, cases h₁ with i h, exact h₂ i h}

    example : (⋂ i, A i) ∩ (⋂ i, B i) ⊆ (⋂ i, A i ∩ B i) :=
        assume x,
        assume h: x ∈ (⋂ i, A i) ∩ (⋂ i, B i), 
        show x ∈ (⋂ i, A i ∩ B i), from 
            Inter.intro 
            (assume i: I,
            have h1: x ∈ A i, from Inter.elim h.left i,
            have h2: x ∈ B i, from Inter.elim h.right i,
            show x ∈ A i ∩ B i, from and.intro h1 h2)

    example : C ∩ (⋃i, A i) ⊆ ⋃i, C ∩ A i :=
        assume x : U,
        assume h : x ∈ C ∩ (⋃i, A i),
        show x ∈ ⋃ i, C ∩ A i, from
            Union.elim h.right 
            (assume i : I,
            assume h1: x ∈ A i,
            show  x ∈ ⋃ i, C ∩ A i, from 
                Union.intro i (and.intro h.left h1))
end

-- ex 4

section 
    variable  {U : Type}
    variables A B C : set U

    example (h1 : A ⊆ B) (h2 : B ⊆ C) : A ⊆ C :=
        subset.trans h1 h2

    example : A ⊆ A :=
        subset.refl A

    example (h : A ⊆ B) : powerset A ⊆ powerset B :=
        assume X : set U,
        assume h1 : X ∈ powerset A,
        show X ∈ powerset B, from subset.trans h1 h

    example (h : powerset A ⊆ powerset B) : A ⊆ B :=
        assume x: U,
        assume h1 : x ∈ A,
        have h2: {y|x = y} ∈ powerset A, from 
            assume z,
            assume : z ∈ {y| x = y},
            have x = z, from this,
            show z ∈ A, from eq.subst this h1, 
        have h3: {y| x = y} ∈ powerset B, from h h2, 
        have h4: x ∈ {y| x = y}, from eq.refl x, 
        show x ∈ B, from h3 h4
end