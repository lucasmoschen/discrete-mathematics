-- Chapter 16

-- Lucas Machado Moschen

-- Exercício 1

open function int algebra

section 

    def f (x : ℤ) : ℤ := x + 3
    def g (x : ℤ) : ℤ := -x
    def h (x : ℤ) : ℤ := 2 * x + 3

    example : injective f :=
    assume x1 x2,
    assume h1 : x1 + 3 = x2 + 3,   -- Lean knows this is the same as f x1 = f x2
    show x1 = x2, from eq_of_add_eq_add_right h1

    example : surjective f :=
    assume y,
    have h1 : f (y - 3) = y, from calc
    f (y - 3) = (y - 3) + 3 : rfl
            ... = y           : by rw sub_add_cancel,
    show ∃ x, f x = y, from exists.intro (y - 3) h1

    example (x y : ℤ) (h : 2 * x = 2 * y) : x = y :=
    have h1 : 2 ≠ (0 : ℤ), from dec_trivial,  -- this tells Lean to figure it out itself
    show x = y, from eq_of_mul_eq_mul_left h1 h

    example (x : ℤ) : -(-x) = x := neg_neg x

    example (A B : Type) (u : A → B) (v : B → A) (h : left_inverse u v) :
    ∀ x, u (v x) = x :=
    h

    example (A B : Type) (u : A → B) (v : B → A) (h : left_inverse u v) :
    right_inverse v u :=
    h

    -- fill in the sorry's in the following proofs

    example : injective h :=
    begin 
        assume x1 x2, 
        assume h1, 
        have h2: 2 ≠ (0 : ℤ), from dec_trivial, 
        apply eq_of_mul_eq_mul_left h2 (eq_of_add_eq_add_right h1),
    end

    example : surjective g :=
    begin
        assume y, 
        have h: g (-y) = y, from calc
            g (-y) = -(-y) : rfl 
            ...    = y : by rw neg_neg, 
        apply exists.intro (-y),
        exact h
    end

    example (A B : Type) (u : A → B) (v1 : B → A) (v2 : B → A)
    (h1 : left_inverse v1 u) (h2 : right_inverse v2 u) : v1 = v2 :=
    funext
    (assume x,
        calc
        v1 x = v1 (u (v2 x)) : by rw h2
        ... = v2 x          : by rw h1)
end