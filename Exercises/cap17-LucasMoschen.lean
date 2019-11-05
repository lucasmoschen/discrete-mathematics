open nat

--1.a.
example : ∀ m n k : nat, m * (n + k) = m * n + m * k := 
assume m n k, 
nat.rec_on k
    (show m*(n + 0) = m*n + m*0, from calc
    m*(n + 0) = m*n : by rw add_zero 
          ... = m*n + 0 : by rw add_zero
          ... = m*n + m*0 : by rw mul_zero
    )
    (assume k, 
    assume ih: m*(n + k) = m*n + m*k, 
    show m*(n + succ k) = m*n + m*(succ k), from calc
    m*(n + succ k) = m*(succ(n + k)) : by rw add_succ
               ... = m*(n + k) + m : by rw mul_succ
               ... = m*n + m*k + m : by rw ih 
               ... = m*n + (m*k + m) : by rw add_assoc
               ... = m*n + m*(succ k) : by rw mul_succ         
    )


--1.b.
theorem mul_zero_left : ∀ n : nat, 0 * n = 0 := 
assume n,
nat.rec_on n
    (show 0*0 = 0, by rw mul_zero)
    (assume n,
    assume ih: 0*n = 0,
    show 0*(succ n) = 0, from calc 
    0*(succ n) = 0*n + 0 : by rw mul_succ
         ...   = 0 + 0 : by rw ih  
         ...   = 0 : by rw add_zero
    )


--1.c.
theorem mul_one_left : ∀ n : nat, 1 * n = n := 
assume n,
nat.rec_on n 
    (show 1*0 = 0, from mul_zero 1)
    (assume n, 
    assume ih: 1*n = n,
    show 1*(succ n) = succ n, from calc
    1*(succ n) = 1*n + 1 : by rw mul_succ
           ... = n + 1 : by rw ih 
           ... = succ n : by simp 
    )

--1.d.
example : ∀ m n k : nat, (m * n) * k = m * (n * k) := 
assume m n k, 
nat.rec_on k
    (show (m*n)*0 = m*(n*0), by rw
    [mul_zero,mul_zero,mul_zero])
    (assume k, 
    assume ih : (m * n) * k = m * (n * k),
    show (m * n) * (succ k) = m * (n * (succ k)), from calc
    (m * n) * (succ k) = (m*n)*k + (m*n) : by rw mul_succ
                   ... = m * (n * k) + m * n : by rw ih 
                   ... = m * (n*k + n) : by rw left_distrib 
                   ... = m * (n*(succ k)) : by rw mul_succ
                   ... = m * (n * succ k) : by simp 
    )

--1.e.
example : ∀ m n : nat, m * n= n * m := 
assume m n, 
nat.rec_on n
    (show m*0 = 0*m, by rw [mul_zero,mul_zero_left])
    (assume n, 
    assume ih : m*n = n*m,
    show m*(succ n) = (succ n)*m, from calc
    m*(succ n) = m*n + m : by rw mul_succ
           ... = n*m + m : by rw ih
           ... = n*m + 1*m : by rw mul_one_left 
           ... = (n + 1)*m : by rw right_distrib 
           ... = (succ n)*m : by simp 
    )

--2.a.
example : ∀ m n k : nat, n ≤ m → n + k ≤ m  + k := 
begin 
    assume m n k, 
    intro h1,
    apply nat.rec_on k,
    exact h1,
    intro k, 
    intro h2, 
    have h3: m+k < succ(m + k), from lt_succ_self (m + k),
    apply lt_of_le_of_lt h2 h3
end

--2.b.
example : ∀ m n k : nat, n + k ≤ m + k → n ≤ m := 
begin 
    assume m n k,
    apply nat.rec_on k, 
        intro h,
        exact h, 
        intros k ih h, 
        repeat {rw add_succ at h},
        have h1: n + k < succ( n + k ), from lt_succ_self (n + k),
        have h2: n + k < succ (m + k), from lt_of_lt_of_le h1 h,  
        have h3: n + k ≤ m + k, from sorry,
    apply ih h3,       
end

/-
--2.c.
example : ∀ m n k : nat, n ≤ m → n * k ≤ m * k := sorry

--2.d.
example : ∀ m n : nat, m ≥ n → m = n ∨ m ≥ n+1 := sorry

--2.e.
example : ∀ n : nat, 0 ≤ n := sorry
-/
