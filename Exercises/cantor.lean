import data.set 
open set function

variables X Y: Type 

def sobrejetiva (f : X → Y) : Prop := ∀ y, ∃ x, f x = y

theorem Cantor : ∀ (A: set X), ¬ ∃ (f: A → set A),  sobrejetiva A (set A) f :=

    begin
        intro A,
        intro h,
        cases h with f h1,
        have h2: ∃ x, f x = {t : A | ¬ (t ∈ f t)}, from h1 {t : A | ¬ (t ∈ f t)},
        cases h2 with x h3,
        apply or.elim (classical.em (x ∈ {t : A | ¬ (t ∈ f t)})),
            intro h4,
                have h5: ¬ (x ∈ f x), from h4,
                rw (eq.symm h3) at h4, 
                apply h5 h4,
            intro h4,
                rw (eq.symm h3) at h4,
                have h5: x ∈ {t : A | ¬ (t ∈ f t)}, from h4,
                rw (eq.symm h3) at h5,
                apply h4 h5,                     
    end


