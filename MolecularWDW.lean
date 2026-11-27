/-
  MolecularWDW.lean
  =================

  Formal verification (Lean 4 core, no external libraries) of the algebraic
  statements underlying the paper

      "Spacetime Molecules: A Pre-geometric Wheeler-DeWitt Model Built from
       Fermionic Chiral Spinor Atoms"

  WHAT IS PROVED HERE
  -------------------
  Work in the normal-mode Fock representation of the model (paper, Sec. IV):
  K normal modes in the left-atom ("/") sector with ladder operators c_k, c_k^dag
  and K mirror modes in the right-atom ("\") sector with d_k, d_k^dag.  THE ATOMS ARE
  FERMIONS.  The Wheeler-DeWitt (Hamiltonian-constraint) operator is

        H = sum_k eps_k ( c_k^dag c_k  -  d_k^dag d_k ) .

  We construct the fermionic ladder operators explicitly on the occupation basis
  (occupations 0 or 1; mode-interleaved Jordan-Wigner signs) and prove, from those
  definitions alone:

   (1) canonical anticommutation relations: {c_k, c_l^dag} = delta_kl,
       {d_k, d_k^dag} = 1, c_k^dag c_l^dag = - c_l^dag c_k^dag, d_k^dag d_l^dag = -d_l^dag d_k^dag,
       c_k^dag d_l^dag = - d_l^dag c_k^dag, and the Pauli principle (c_k^dag)^2 = (d_k^dag)^2 = 0;
   (2) MOLECULES ARE BOSONS: X_k^dag = c_k^dag d_k^dag satisfy X_k^dag X_l^dag = X_l^dag X_k^dag,
       commute with the atom operators of every other mode, [X_k, X_l^dag] = 0 (k /= l),
       and obey the hard-core algebra [X_k, X_k^dag] = 1 - n^c_k - n^d_k, (X_k^dag)^2 = 0;
   (3) H is diagonal with eigenvalue E(m,n) = sum_k eps_k (m_k - n_k);
   (4) mirror antisymmetry  H M = - M H  (M exchanges "/" and "\");
   (5) H commutes with every molecule operator;
   (6) H |0> = 0;
   (7) MAIN THEOREM: every multi-molecule state X_{k_1}^dag ... X_{k_r}^dag |0> satisfies
       the Wheeler-DeWitt equation  H Psi = 0;
   (8) for distinct modes each such state IS the basis vector |occ, occ> (coefficient 1),
       states on different sets of modes are linearly independent, and a repeated mode
       gives zero (Pauli);
   (9) every BCS-type molecular condensate prod_k (u_k + v_k X_k^dag)|0> satisfies H Psi = 0;
  (10) the pair shift [H, d_l c_k] = (eps_l - eps_k) d_l c_k (molecular field equation);
  (11) for any split H = T + V,  H Psi = 0  is equivalent to  T Psi = - V Psi;
  (12) antisymmetric (Weyl) ordering: the fermionic zero-point constants cancel exactly,
       sum_k eps_k[(c^dag c - c c^dag) - (d^dag d - d d^dag)] = 2 H;
  (13) no-go lemma (expectation form);
  (14) scale freedom: for lam /= 0, ker(lam H) = ker H;
  (15) the sign argument of the Stelle-channel proposition;
  (16) rational independence of the mode energies forces m_k = n_k on every
       zero-energy configuration (paper `thm:kernel`(c), per normal mode).

  Further sections (namespaces Spinor, Conformal, FieldIdentities):
  (17) `eq:etaeps`: -eps eps X Y = 2 eta(X,Y) and det X = -eta(X,X) (unnormalized soldering);
  (18) `prop:null`: det(xi xi^dagger) = 0;
  (19) the dyad identity of App. A and `prop:tetrad` in spinor form;
  (20) the chiral trace multiplied by 16; Kramers: sigma_y conj(U) sigma_y = U;
  (21) the boundary conformal algebra) and the Clifford algebra, by exact
       kernel computation with Gaussian-integer matrices;
  (22) cleared-denominator forms of the scalaron mass, Stelle masses, de Sitter
       entropy, Starobinsky potential and R^2 coefficient.
  Polynomial identities are proved over Int.  An identity between polynomials with
  integer coefficients that holds for all integer arguments is an identity of
  polynomials, and therefore holds in every commutative ring, R and C included.

  An independent formalization of the same statements in Rocq (Coq), with a
  different encoding, is in the companion file MolecularWDW.v.

  WHAT IS NOT PROVED HERE (and why)
  ---------------------------------
  * The reduction of the site-basis constraint  H = T + V  to normal modes uses
    the spectral theorem for the 2N x 2N Hermitian one-atom matrix h and the
    isospectrality of h and its complex conjugate. That is standard linear
    algebra (Mathlib: Matrix.IsHermitian.spectral_theorem); it is checked
    numerically in the companion notebook. Lean core has no matrix library.
  * Scalars: Lean core has no real or complex numbers with proofs, so
    amplitudes and energies are taken in the integers.  Every statement below
    is a polynomial identity proved without division, so the identical proof
    goes through over any commutative ring (R or C) in a Mathlib port.

  Build:  lean MolecularWDW.lean      (tested with Lean 4.15.0, core only)
-/

namespace MolecularWDW

/-! ## 1. Configurations, vectors, finite sums -/

/-- Occupation numbers (0 or 1: the atoms are fermions) of the `K` normal modes in each
    sector: `m` for the left-atom ("/") modes, `n` for the right-atom ("\") modes. -/
structure Config (K : Nat) where
  m : Fin K → Bool
  n : Fin K → Bool

/-- A vector in the occupation basis, given by its coefficient function.  The basis vector
    for `s` is `Π_k (c_k†)^{m_k} (d_k†)^{n_k} |0⟩`, with the product ordered by mode
    (mode-interleaved Jordan-Wigner ordering). -/
abbrev Vec (K : Nat) := Config K → Int

/-- Set the occupation of mode `k` to `b`. -/
def setb {K : Nat} (f : Fin K → Bool) (k : Fin K) (b : Bool) : Fin K → Bool :=
  fun j => if j = k then b else f j

@[simp] theorem setb_self {K : Nat} (f : Fin K → Bool) (k : Fin K) (b : Bool) :
    setb f k b k = b := by simp [setb]

theorem setb_ne {K : Nat} (f : Fin K → Bool) {k j : Fin K} (b : Bool) (h : j ≠ k) :
    setb f k b j = f j := by simp [setb, h]

@[simp] theorem setb_setb {K : Nat} (f : Fin K → Bool) (k : Fin K) (b b' : Bool) :
    setb (setb f k b) k b' = setb f k b' := by
  funext j; unfold setb; by_cases h : j = k <;> simp [h]

theorem setb_eq {K : Nat} (f : Fin K → Bool) (k : Fin K) (b : Bool) (h : f k = b) :
    setb f k b = f := by
  funext j; unfold setb
  by_cases hj : j = k
  · subst hj; simp [h]
  · simp [hj]

theorem setb_comm {K : Nat} (f : Fin K → Bool) {k l : Fin K} (b b' : Bool) (h : k ≠ l) :
    setb (setb f k b) l b' = setb (setb f l b') k b := by
  funext j; unfold setb
  by_cases hl : j = l <;> by_cases hk : j = k
  · exact absurd (hk.symm.trans hl) h
  · rw [if_pos hl, if_neg hk, if_pos hl]
  · rw [if_neg hl, if_pos hk, if_pos hk]
  · rw [if_neg hl, if_neg hk, if_neg hk, if_neg hl]

/-- `0`/`1` value of an occupation. -/
def ind (b : Bool) : Int := if b then 1 else 0
@[simp] theorem ind_true : ind true = 1 := rfl
@[simp] theorem ind_false : ind false = 0 := rfl

/-- Finite sum over `Fin K`. -/
def sumFin : (K : Nat) → (Fin K → Int) → Int
  | 0, _ => 0
  | K + 1, f => sumFin K (fun i => f i.castSucc) + f (Fin.last K)

theorem sumFin_congr {K : Nat} {f g : Fin K → Int} (h : ∀ i, f i = g i) :
    sumFin K f = sumFin K g := by
  have : f = g := funext h
  rw [this]

theorem sumFin_zero {K : Nat} (f : Fin K → Int) (h : ∀ i, f i = 0) :
    sumFin K f = 0 := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc) (fun i => h _), h]
    rfl

theorem sumFin_mul_right {K : Nat} (f : Fin K → Int) (x : Int) :
    sumFin K (fun i => f i * x) = sumFin K f * x := by
  induction K with
  | zero => simp [sumFin]
  | succ K ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.add_mul]

theorem sumFin_neg {K : Nat} (f : Fin K → Int) :
    sumFin K (fun i => - f i) = - sumFin K f := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.neg_add]

theorem sumFin_two_mul {K : Nat} (f : Fin K → Int) :
    sumFin K (fun i => 2 * f i) = 2 * sumFin K f := by
  induction K with
  | zero => rfl
  | succ K ih =>
    simp only [sumFin]
    rw [ih (fun i => f i.castSucc), Int.mul_add]

/-- Two functions that agree except at one point have sums differing by the jump there. -/
theorem sumFin_point {K : Nat} (f g : Fin K → Int) (k : Fin K)
    (h : ∀ j, j ≠ k → f j = g j) : sumFin K f = sumFin K g + (f k - g k) := by
  induction K with
  | zero => exact k.elim0
  | succ K ih =>
    simp only [sumFin]
    by_cases hk : k.val < K
    · have e : (⟨k.val, hk⟩ : Fin K).castSucc = k := Fin.eq_of_val_eq rfl
      have h1 := ih (fun i => f i.castSucc) (fun i => g i.castSucc) ⟨k.val, hk⟩ (by
        intro j hj
        apply h
        intro hc
        apply hj
        apply Fin.eq_of_val_eq
        have := congrArg Fin.val hc
        simpa using this)
      have h2 : f (Fin.last K) = g (Fin.last K) := h _ (by
        intro hc; have := congrArg Fin.val hc; simp at this; omega)
      rw [h1, h2]; simp only [e]; omega
    · have e : k = Fin.last K := Fin.eq_of_val_eq (by have := k.isLt; simp; omega)
      subst e
      have h1 : sumFin K (fun i => f i.castSucc) = sumFin K (fun i => g i.castSucc) :=
        sumFin_congr (fun i => h _ (by
          intro hc; have := congrArg Fin.val hc; simp at this; omega))
      rw [h1]; omega

theorem Config.ext' {K : Nat} {a b : Config K} (hm : a.m = b.m) (hn : a.n = b.n) :
    a = b := by
  cases a; cases b; simp_all

/-! ## 2. Fermionic ladder operators (Jordan-Wigner signs)

  Basis ordering: modes in increasing order, and within mode `k` first `c_k†` then `d_k†`.
  Then `c_k†` carries the sign `(-1)^(number of atoms in modes below k)` and `d_k†` the sign
  `(-1)^(atoms below k + m_k)`.
-/

variable {K : Nat}

/-- number of atoms (both species) in modes strictly below `k` -/
def below (s : Config K) (k : Fin K) : Int :=
  sumFin K (fun j => if j.val < k.val then ind (s.m j) + ind (s.n j) else 0)

/-- `(-1)^x` -/
def sgn (x : Int) : Int := if x % 2 = 0 then 1 else -1

theorem sgn_sq (x : Int) : sgn x * sgn x = 1 := by
  unfold sgn; split <;> rfl

theorem sgn_add_one (x : Int) : sgn (x + 1) = - sgn x := by
  unfold sgn; split <;> split <;> omega

theorem sgn_sub_one (x : Int) : sgn (x - 1) = - sgn x := by
  have h := sgn_add_one (x - 1)
  rw [Int.sub_add_cancel] at h
  rw [h, Int.neg_neg]

theorem sgn_sub_two (x : Int) : sgn (x - 2) = sgn x := by
  have h1 := sgn_sub_one x
  have h2 := sgn_sub_one (x - 1)
  rw [show x - 1 - 1 = x - 2 by omega, h1, Int.neg_neg] at h2
  exact h2

/-- changing an occupation at or above `k` does not change `below · k` -/
theorem below_setm_ge (s : Config K) {l k : Fin K} (b : Bool) (h : ¬ l.val < k.val) :
    below ⟨setb s.m l b, s.n⟩ k = below s k := by
  unfold below; apply sumFin_congr; intro j
  by_cases hj : j.val < k.val
  · have : j ≠ l := by intro e; subst e; exact h hj
    simp [hj, setb_ne _ _ this]
  · simp [hj]

theorem below_setn_ge (s : Config K) {l k : Fin K} (b : Bool) (h : ¬ l.val < k.val) :
    below ⟨s.m, setb s.n l b⟩ k = below s k := by
  unfold below; apply sumFin_congr; intro j
  by_cases hj : j.val < k.val
  · have : j ≠ l := by intro e; subst e; exact h hj
    simp [hj, setb_ne _ _ this]
  · simp [hj]

/-- changing an occupation below `k` shifts `below · k` by the change -/
theorem below_setm_lt (s : Config K) {l k : Fin K} (b : Bool) (h : l.val < k.val) :
    below ⟨setb s.m l b, s.n⟩ k = below s k + (ind b - ind (s.m l)) := by
  unfold below
  rw [sumFin_point _ (fun j => if j.val < k.val then ind (s.m j) + ind (s.n j) else 0) l]
  · simp [h]; omega
  · intro j hj; simp [setb_ne _ _ hj]

theorem below_setn_lt (s : Config K) {l k : Fin K} (b : Bool) (h : l.val < k.val) :
    below ⟨s.m, setb s.n l b⟩ k = below s k + (ind b - ind (s.n l)) := by
  unfold below
  rw [sumFin_point _ (fun j => if j.val < k.val then ind (s.m j) + ind (s.n j) else 0) l]
  · simp [h]; omega
  · intro j hj; simp [setb_ne _ _ hj]

/-- sign of `d_k†` -/
def dsg (s : Config K) (k : Fin K) : Int := sgn (below s k + ind (s.m k))

/-- creation of a left atom ("/") in normal mode `k` -/
def cdag (k : Fin K) (ψ : Vec K) : Vec K := fun s =>
  if s.m k then sgn (below s k) * ψ ⟨setb s.m k false, s.n⟩ else 0

/-- annihilation of a left atom in normal mode `k` -/
def c (k : Fin K) (ψ : Vec K) : Vec K := fun s =>
  if s.m k then 0 else sgn (below s k) * ψ ⟨setb s.m k true, s.n⟩

/-- creation of a right atom ("\") in mirror mode `k` -/
def ddag (k : Fin K) (ψ : Vec K) : Vec K := fun s =>
  if s.n k then dsg s k * ψ ⟨s.m, setb s.n k false⟩ else 0

/-- annihilation of a right atom in mirror mode `k` -/
def d (k : Fin K) (ψ : Vec K) : Vec K := fun s =>
  if s.n k then 0 else dsg s k * ψ ⟨s.m, setb s.n k true⟩

/-- (1a) number operator of the "/" sector -/
theorem number_c (k : Fin K) (ψ : Vec K) (s : Config K) :
    cdag k (c k ψ) s = ind (s.m k) * ψ s := by
  unfold cdag c
  cases h : s.m k
  · simp
  · simp only [if_true, setb_self, Bool.false_eq_true, if_false, below_setm_ge s false (Nat.lt_irrefl _),
      setb_setb, setb_eq s.m k true h, ind_true, Int.one_mul]
    rw [← Int.mul_assoc, sgn_sq, Int.one_mul]

theorem number_d (k : Fin K) (ψ : Vec K) (s : Config K) :
    ddag k (d k ψ) s = ind (s.n k) * ψ s := by
  unfold ddag d dsg
  cases h : s.n k
  · simp
  · simp only [if_true, setb_self, Bool.false_eq_true, if_false, below_setn_ge s false (Nat.lt_irrefl _),
      setb_setb, setb_eq s.n k true h, ind_true, Int.one_mul]
    rw [← Int.mul_assoc, sgn_sq, Int.one_mul]

theorem anti_number_c (k : Fin K) (ψ : Vec K) (s : Config K) :
    c k (cdag k ψ) s = (1 - ind (s.m k)) * ψ s := by
  unfold cdag c
  cases h : s.m k
  · simp only [Bool.false_eq_true, if_false, setb_self, if_true, below_setm_ge s true (Nat.lt_irrefl _),
      setb_setb, setb_eq s.m k false h, ind_false, Int.sub_zero, Int.one_mul]
    rw [← Int.mul_assoc, sgn_sq, Int.one_mul]
  · simp

theorem anti_number_d (k : Fin K) (ψ : Vec K) (s : Config K) :
    d k (ddag k ψ) s = (1 - ind (s.n k)) * ψ s := by
  unfold ddag d dsg
  cases h : s.n k
  · simp only [Bool.false_eq_true, if_false, setb_self, if_true, below_setn_ge s true (Nat.lt_irrefl _),
      setb_setb, setb_eq s.n k false h, ind_false, Int.sub_zero, Int.one_mul]
    rw [← Int.mul_assoc, sgn_sq, Int.one_mul]
  · simp

/-- (1b) canonical anticommutation relation `{c_k, c_k†} = 1` -/
theorem car_c (k : Fin K) (ψ : Vec K) (s : Config K) :
    c k (cdag k ψ) s + cdag k (c k ψ) s = ψ s := by
  rw [anti_number_c, number_c, Int.sub_mul, Int.one_mul]; omega

/-- (1b') `{d_k, d_k†} = 1` -/
theorem car_d (k : Fin K) (ψ : Vec K) (s : Config K) :
    d k (ddag k ψ) s + ddag k (d k ψ) s = ψ s := by
  rw [anti_number_d, number_d, Int.sub_mul, Int.one_mul]; omega

/-- (1c) Pauli principle: `(c_k†)^2 = 0`, `(d_k†)^2 = 0` -/
theorem pauli_c (k : Fin K) (ψ : Vec K) : cdag k (cdag k ψ) = fun _ => 0 := by
  funext s; unfold cdag; cases s.m k <;> simp

theorem pauli_d (k : Fin K) (ψ : Vec K) : ddag k (ddag k ψ) = fun _ => 0 := by
  funext s; unfold ddag; cases s.n k <;> simp

theorem fin_lt_or_gt {k l : Fin K} (h : k ≠ l) : k.val < l.val ∨ l.val < k.val := by
  have : k.val ≠ l.val := fun e => h (Fin.eq_of_val_eq e)
  omega

/-- (1d) atoms of different modes anticommute: `c_k† c_l† = - c_l† c_k†` -/
theorem cdag_anticomm (k l : Fin K) (h : k ≠ l) (ψ : Vec K) (s : Config K) :
    cdag k (cdag l ψ) s = - cdag l (cdag k ψ) s := by
  unfold cdag
  have hlk : l ≠ k := fun e => h e.symm
  simp only [setb_ne _ _ hlk, setb_ne _ _ h]
  cases hk : s.m k <;> cases hl : s.m l <;> simp
  rw [setb_comm s.m false false h]
  rcases fin_lt_or_gt h with hlt | hgt
  · rw [below_setm_lt s false hlt, below_setm_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hlt)), hk]
    simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg, sgn_sub_one]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc, Int.mul_comm (sgn (below s k))]
  · rw [below_setm_lt s false hgt, below_setm_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hgt)), hl]
    simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg, sgn_sub_one]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc, Int.mul_comm (sgn (below s l))]

/-- (1d') `{c_k, c_l†} = 0` for `k ≠ l` -/
theorem c_cdag_anticomm (k l : Fin K) (h : k ≠ l) (ψ : Vec K) (s : Config K) :
    c k (cdag l ψ) s = - cdag l (c k ψ) s := by
  unfold cdag c
  have hlk : l ≠ k := fun e => h e.symm
  simp only [setb_ne _ _ hlk, setb_ne _ _ h]
  cases hk : s.m k <;> cases hl : s.m l <;> simp
  rw [setb_comm s.m true false h]
  rcases fin_lt_or_gt h with hlt | hgt
  · rw [below_setm_lt s true hlt, below_setm_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hlt)), hk]
    simp only [ind_false, ind_true, Int.sub_zero, sgn_add_one]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc, Int.mul_comm (sgn (below s k))]
  · rw [below_setm_ge s true (Nat.not_lt.mpr (Nat.le_of_lt hgt)), below_setm_lt s false hgt, hl]
    simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg, sgn_sub_one]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc, Int.mul_comm (sgn (below s l))]

/-- (1d'') `d_k† d_l† = - d_l† d_k†` -/
theorem ddag_anticomm (k l : Fin K) (h : k ≠ l) (ψ : Vec K) (s : Config K) :
    ddag k (ddag l ψ) s = - ddag l (ddag k ψ) s := by
  unfold ddag dsg
  have hlk : l ≠ k := fun e => h e.symm
  simp only [setb_ne _ _ hlk, setb_ne _ _ h]
  cases hk : s.n k <;> cases hl : s.n l <;> simp
  rw [setb_comm s.n false false h]
  rcases fin_lt_or_gt h with hlt | hgt
  · rw [below_setn_lt s false hlt, below_setn_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hlt)), hk]
    simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg]
    rw [show below s l - 1 + ind (s.m l) = below s l + ind (s.m l) - 1 by omega, sgn_sub_one]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc,
      Int.mul_comm (sgn (below s k + ind (s.m k)))]
  · rw [below_setn_lt s false hgt, below_setn_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hgt)), hl]
    simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg]
    rw [show below s k - 1 + ind (s.m k) = below s k + ind (s.m k) - 1 by omega, sgn_sub_one]
    simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc,
      Int.mul_comm (sgn (below s l + ind (s.m l)))]

/-- (1e) "/" and "\" atoms anticommute: `c_k† d_l† = - d_l† c_k†` (all `k, l`) -/
theorem cdag_ddag_anticomm (k l : Fin K) (ψ : Vec K) (s : Config K) :
    cdag k (ddag l ψ) s = - ddag l (cdag k ψ) s := by
  unfold cdag ddag dsg
  dsimp only
  cases hk : s.m k <;> cases hl : s.n l <;> simp
  by_cases hkl : k = l
  · subst hkl
    rw [below_setm_ge s false (Nat.lt_irrefl _), below_setn_ge s false (Nat.lt_irrefl _), hk]
    simp only [setb_self, ind_false, ind_true, Int.add_zero, sgn_add_one, Int.neg_mul, Int.neg_neg]
  · have hlk : l ≠ k := fun e => hkl e.symm
    rw [setb_ne _ _ hlk]
    rcases fin_lt_or_gt hkl with hlt | hgt
    · rw [below_setm_lt s false hlt, below_setn_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hlt)), hk]
      simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg]
      rw [show below s l - 1 + ind (s.m l) = below s l + ind (s.m l) - 1 by omega, sgn_sub_one]
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc,
        Int.mul_comm (sgn (below s k))]
    · rw [below_setm_ge s false (Nat.not_lt.mpr (Nat.le_of_lt hgt)), below_setn_lt s false hgt, hl]
      simp only [ind_false, ind_true, Int.zero_sub, ← Int.sub_eq_add_neg, sgn_sub_one]
      simp only [Int.neg_mul, Int.mul_neg, Int.neg_neg, ← Int.mul_assoc,
        Int.mul_comm (sgn (below s k))]

/-! ## 3. Molecules are bosons

  The molecule operator `X_k† = c_k† d_k†` creates one "/" and one "\" atom in mode `k`.
  In the mode-interleaved ordering its two Jordan-Wigner signs cancel, so it acts on the
  occupation basis with no sign at all. -/

/-- molecule creation `X_k† = c_k† d_k†` -/
def Xdag (k : Fin K) (ψ : Vec K) : Vec K := cdag k (ddag k ψ)

/-- molecule annihilation `X_k = d_k c_k` (the adjoint of `X_k†`) -/
def X (k : Fin K) (ψ : Vec K) : Vec K := d k (c k ψ)

theorem Xdag_apply (k : Fin K) (ψ : Vec K) (s : Config K) :
    Xdag k ψ s = if s.m k then (if s.n k then ψ ⟨setb s.m k false, setb s.n k false⟩ else 0)
                 else 0 := by
  unfold Xdag cdag ddag dsg
  dsimp only
  cases hm : s.m k <;> cases hn : s.n k <;> simp
  rw [below_setm_ge s false (Nat.lt_irrefl _)]
  simp only [setb_self, ind_false, Int.add_zero, ← Int.mul_assoc, sgn_sq, Int.one_mul]

theorem X_apply (k : Fin K) (ψ : Vec K) (s : Config K) :
    X k ψ s = if s.m k then 0 else (if s.n k then 0 else ψ ⟨setb s.m k true, setb s.n k true⟩) := by
  unfold X c d dsg
  dsimp only
  cases hm : s.m k <;> cases hn : s.n k <;> simp [hm]
  rw [below_setn_ge s true (Nat.lt_irrefl _)]
  simp only [ind_false, Int.add_zero, ← Int.mul_assoc, sgn_sq, Int.one_mul]

/-- (2a) MOLECULES ARE BOSONS: molecule creation operators commute, `X_k† X_l† = X_l† X_k†`. -/
theorem molecules_commute (k l : Fin K) (ψ : Vec K) :
    Xdag k (Xdag l ψ) = Xdag l (Xdag k ψ) := by
  funext s
  by_cases h : k = l
  · subst h; rfl
  · have hlk : l ≠ k := fun e => h e.symm
    simp only [Xdag_apply, setb_ne _ _ hlk, setb_ne _ _ h]
    cases s.m k <;> cases s.n k <;> cases s.m l <;> cases s.n l <;> simp
    rw [setb_comm s.m false false h, setb_comm s.n false false h]

/-- (2b) hard core (Pauli): `(X_k†)^2 = 0`, at most one molecule per mode -/
theorem molecule_pauli (k : Fin K) (ψ : Vec K) : Xdag k (Xdag k ψ) = fun _ => 0 := by
  funext s; simp only [Xdag_apply, setb_self]
  cases s.m k <;> cases s.n k <;> simp

/-- (2c) hard-core boson algebra: `[X_k, X_k†] = 1 - n^c_k - n^d_k` -/
theorem molecule_hardcore (k : Fin K) (ψ : Vec K) (s : Config K) :
    X k (Xdag k ψ) s - Xdag k (X k ψ) s = (1 - ind (s.m k) - ind (s.n k)) * ψ s := by
  simp only [X_apply, Xdag_apply, setb_self, setb_setb]
  cases hm : s.m k <;> cases hn : s.n k <;> simp [setb_eq _ _ _ hm, setb_eq _ _ _ hn]

/-- (2d) different modes: `[X_k, X_l†] = 0` for `k ≠ l` -/
theorem molecule_cross (k l : Fin K) (h : k ≠ l) (ψ : Vec K) :
    X k (Xdag l ψ) = Xdag l (X k ψ) := by
  funext s
  have hlk : l ≠ k := fun e => h e.symm
  simp only [X_apply, Xdag_apply, setb_ne _ _ hlk, setb_ne _ _ h]
  cases s.m k <;> cases s.n k <;> cases s.m l <;> cases s.n l <;> simp
  rw [setb_comm s.m true false h, setb_comm s.n true false h]

/-- below is unchanged when a whole molecule is removed from mode `k`, up to an even shift -/
theorem sgn_below_mol (s : Config K) {k l : Fin K} (hm : s.m k = true) (hn : s.n k = true) :
    sgn (below ⟨setb s.m k false, setb s.n k false⟩ l) = sgn (below s l) := by
  by_cases hkl : k.val < l.val
  · have e1 := below_setn_lt (⟨setb s.m k false, s.n⟩ : Config K) false hkl
    have e2 := below_setm_lt s false hkl
    simp only at e1
    rw [e1, e2, hm, hn]
    simp only [ind_false, ind_true]
    rw [show below s l + (0 - 1) + (0 - 1) = below s l - 2 by omega, sgn_sub_two]
  · have e1 := below_setn_ge (⟨setb s.m k false, s.n⟩ : Config K) false hkl
    have e2 := below_setm_ge s false hkl
    simp only at e1
    rw [e1, e2]

/-- (2e) molecules commute with atoms of every other mode: `c_l† X_k† = X_k† c_l†` -/
theorem molecule_atom_comm_c (k l : Fin K) (h : l ≠ k) (ψ : Vec K) :
    cdag l (Xdag k ψ) = Xdag k (cdag l ψ) := by
  funext s
  have hkl : k ≠ l := fun e => h e.symm
  simp only [Xdag_apply, cdag, setb_ne _ _ h, setb_ne _ _ hkl]
  cases hmk : s.m k <;> cases hnk : s.n k <;> cases hml : s.m l <;> simp
  rw [sgn_below_mol s hmk hnk, setb_comm s.m false false hkl]

/-- (2e') `d_l† X_k† = X_k† d_l†` for `l ≠ k` -/
theorem molecule_atom_comm_d (k l : Fin K) (h : l ≠ k) (ψ : Vec K) :
    ddag l (Xdag k ψ) = Xdag k (ddag l ψ) := by
  funext s
  have hkl : k ≠ l := fun e => h e.symm
  simp only [Xdag_apply, ddag, dsg, setb_ne _ _ h, setb_ne _ _ hkl]
  cases hmk : s.m k <;> cases hnk : s.n k <;> cases hnl : s.n l <;> simp
  have e := sgn_below_mol s (l := l) hmk hnk
  have e2 : sgn (below ⟨setb s.m k false, setb s.n k false⟩ l + ind (s.m l))
          = sgn (below s l + ind (s.m l)) := by
    unfold sgn at e ⊢
    split at e <;> split at e <;> split <;> split <;> omega
  rw [e2, setb_comm s.n false false hkl]

/-! ## 4. The Wheeler-DeWitt operator -/

/-- `H = Σ_k ε_k (c_k† c_k − d_k† d_k)`, built from the fermionic ladder operators. -/
def H (ε : Fin K → Int) (ψ : Vec K) : Vec K := fun s =>
  sumFin K (fun k => ε k * (cdag k (c k ψ) s - ddag k (d k ψ) s))

/-- Energy imbalance of a configuration: `E(m,n) = Σ_k ε_k (m_k − n_k)`. -/
def energy (ε : Fin K → Int) (s : Config K) : Int :=
  sumFin K (fun k => ε k * (ind (s.m k) - ind (s.n k)))

/-- (3) `H` is diagonal in the occupation basis with eigenvalue `E(m,n)`. -/
theorem H_diag (ε : Fin K → Int) (ψ : Vec K) (s : Config K) :
    H ε ψ s = energy ε s * ψ s := by
  unfold H energy
  rw [← sumFin_mul_right]
  apply sumFin_congr
  intro k
  rw [number_c, number_d, ← Int.sub_mul, Int.mul_assoc]

/-- Mirror map: exchange the "/" and "\" sectors. -/
def mirror (ψ : Vec K) : Vec K := fun s => ψ ⟨s.n, s.m⟩

theorem energy_mirror (ε : Fin K → Int) (s : Config K) :
    energy ε ⟨s.n, s.m⟩ = - energy ε s := by
  unfold energy
  rw [← sumFin_neg]
  apply sumFin_congr
  intro k
  simp only
  rw [← Int.mul_neg, Int.neg_sub]

/-- (4) mirror antisymmetry of the constraint: `H M = − M H`. -/
theorem H_mirror (ε : Fin K → Int) (ψ : Vec K) (s : Config K) :
    H ε (mirror ψ) s = - (mirror (H ε ψ)) s := by
  rw [H_diag]
  unfold mirror
  rw [H_diag, energy_mirror, Int.neg_mul]
  simp

/-- removing a whole molecule does not change the energy imbalance -/
theorem energy_clear_both (ε : Fin K → Int) (s : Config K) (k : Fin K)
    (hm : s.m k = true) (hn : s.n k = true) :
    energy ε ⟨setb s.m k false, setb s.n k false⟩ = energy ε s := by
  unfold energy
  apply sumFin_congr
  intro j
  simp only
  by_cases hj : j = k
  · subst hj; simp [hm, hn]
  · simp [setb_ne _ _ hj]

/-- (5) `H` commutes with every molecule creation operator. -/
theorem H_Xdag_comm (ε : Fin K → Int) (k : Fin K) (ψ : Vec K) :
    H ε (Xdag k ψ) = Xdag k (H ε ψ) := by
  funext s
  rw [H_diag, Xdag_apply, Xdag_apply]
  cases hm : s.m k <;> cases hn : s.n k <;> simp
  rw [H_diag, energy_clear_both ε s k hm hn]

/-! ## 5. Vacuum, molecular states, condensates -/

/-- the empty configuration -/
def zeroCfg (K : Nat) : Config K := ⟨fun _ => false, fun _ => false⟩

open Classical in
/-- the Fock vacuum `|0⟩` -/
noncomputable def vac (K : Nat) : Vec K := fun s => if s = zeroCfg K then 1 else 0

theorem energy_zero (ε : Fin K → Int) : energy ε (zeroCfg K) = 0 := by
  unfold energy zeroCfg
  apply sumFin_zero
  intro k
  simp

/-- (6) the vacuum solves the constraint -/
theorem H_vac (ε : Fin K → Int) : H ε (vac K) = fun _ => 0 := by
  funext s
  rw [H_diag]
  unfold vac
  by_cases h : s = zeroCfg K
  · subst h; simp [energy_zero]
  · simp [h]

/-- `X_{k_1}† ⋯ X_{k_r}† ψ` -/
def molecules (ks : List (Fin K)) (ψ : Vec K) : Vec K :=
  ks.foldr (fun k φ => Xdag k φ) ψ

theorem Xdag_zero (k : Fin K) : Xdag k (fun _ => (0 : Int)) = fun _ => 0 := by
  funext s
  rw [Xdag_apply]
  split <;> (try split) <;> rfl

/-- (7) MAIN THEOREM: every multi-molecule state solves the Wheeler-DeWitt
    equation `H Ψ = 0`. -/
theorem wdw_molecular_solution (ε : Fin K → Int) (ks : List (Fin K)) :
    H ε (molecules ks (vac K)) = fun _ => 0 := by
  induction ks with
  | nil => exact H_vac ε
  | cons k ks ih =>
    show H ε (Xdag k (molecules ks (vac K))) = _
    rw [H_Xdag_comm, ih, Xdag_zero]

/-- modes occupied by a list of molecules -/
def occ (ks : List (Fin K)) : Fin K → Bool :=
  ks.foldr (fun k f => setb f k true) (fun _ => false)

/-- no mode is used twice -/
def fresh : List (Fin K) → Prop
  | [] => True
  | k :: ks => occ ks k = false ∧ fresh ks

/-- (8a) a molecular state with distinct modes has coefficient 1 on `|occ, occ⟩` -/
theorem molecules_at_occ (ks : List (Fin K)) (hf : fresh ks) :
    molecules ks (vac K) ⟨occ ks, occ ks⟩ = 1 := by
  induction ks with
  | nil => simp [molecules, occ, vac, zeroCfg]
  | cons k ks ih =>
    show Xdag k (molecules ks (vac K)) ⟨setb (occ ks) k true, setb (occ ks) k true⟩ = 1
    rw [Xdag_apply]
    simp only [setb_self, if_true, setb_setb, setb_eq _ _ _ hf.1]
    exact ih hf.2

/-- (8b) ... and vanishes on every other configuration: it IS the basis vector
    `|occ, occ⟩`. -/
theorem molecules_support (ks : List (Fin K)) (s : Config K)
    (h : molecules ks (vac K) s ≠ 0) : s = ⟨occ ks, occ ks⟩ := by
  induction ks generalizing s with
  | nil =>
    simp only [molecules, List.foldr] at h
    unfold vac at h
    by_cases hs : s = zeroCfg K
    · subst hs; rfl
    · simp [hs] at h
  | cons k ks ih =>
    have h' : Xdag k (molecules ks (vac K)) s ≠ 0 := h
    rw [Xdag_apply] at h'
    cases hm : s.m k <;> cases hn : s.n k <;> simp [hm, hn] at h'
    have e := ih _ h'
    have em : setb s.m k false = occ ks := congrArg Config.m e
    have en : setb s.n k false = occ ks := congrArg Config.n e
    apply Config.ext'
    · show s.m = setb (occ ks) k true
      rw [← em, setb_setb, setb_eq _ _ _ hm]
    · show s.n = setb (occ ks) k true
      rw [← en, setb_setb, setb_eq _ _ _ hn]

/-- (8c) molecular states built on different sets of modes are different basis vectors,
    hence linearly independent -/
theorem distinct_solutions (ks ks' : List (Fin K)) (h : occ ks ≠ occ ks') :
    molecules ks (vac K) ⟨occ ks', occ ks'⟩ = 0 := by
  apply Classical.byContradiction
  intro hne
  have e := molecules_support ks _ hne
  exact h (congrArg Config.m e).symm

/-- (8d) Pauli: a mode used twice gives the zero vector -/
theorem molecules_repeat (k : Fin K) (ks : List (Fin K)) (ψ : Vec K) :
    molecules (k :: k :: ks) ψ = fun _ => 0 := by
  show Xdag k (Xdag k (molecules ks ψ)) = _
  exact molecule_pauli k _

/-- BCS-type molecular condensate `Π_k (u_k + v_k X_k†) ψ` -/
def bcs (u v : Fin K → Int) : List (Fin K) → Vec K → Vec K
  | [], ψ => ψ
  | k :: ks, ψ => fun s => u k * bcs u v ks ψ s + v k * Xdag k (bcs u v ks ψ) s

/-- (9) MOLECULAR CONDENSATES SOLVE THE CONSTRAINT: every BCS-type state
    `Π_k (u_k + v_k X_k†)|0⟩` satisfies `H Ψ = 0`. -/
theorem bcs_solution (ε u v : Fin K → Int) (ks : List (Fin K)) :
    H ε (bcs u v ks (vac K)) = fun _ => 0 := by
  induction ks with
  | nil => exact H_vac ε
  | cons k ks ih =>
    funext s
    have h1 : ∀ t, energy ε t * bcs u v ks (vac K) t = 0 := by
      intro t; rw [← H_diag, ih]
    have h2 : ∀ t, energy ε t * Xdag k (bcs u v ks (vac K)) t = 0 := by
      intro t; rw [← H_diag, H_Xdag_comm, ih, Xdag_zero]
    rw [H_diag]
    show energy ε s * (u k * bcs u v ks (vac K) s + v k * Xdag k (bcs u v ks (vac K)) s) = 0
    rw [Int.mul_add, Int.mul_left_comm, h1, Int.mul_left_comm, h2]
    simp

/-- energy change when a "/" atom is added to mode `k` and a "\" atom to mode `l` -/
theorem energy_pair (ε : Fin K → Int) (s : Config K) (k l : Fin K)
    (hm : s.m k = false) (hn : s.n l = false) :
    energy ε ⟨setb s.m k true, setb s.n l true⟩ = energy ε s + ε k - ε l := by
  have step1 : energy ε ⟨setb s.m k true, s.n⟩ = energy ε s + ε k := by
    unfold energy
    rw [sumFin_point _ (fun j => ε j * (ind (s.m j) - ind (s.n j))) k]
    · simp only [setb_self, hm, ind_true, ind_false]
      simp only [Int.mul_sub, Int.mul_one, Int.mul_zero]; omega
    · intro j hj; simp [setb_ne _ _ hj]
  have step2 : energy ε ⟨setb s.m k true, setb s.n l true⟩
             = energy ε ⟨setb s.m k true, s.n⟩ - ε l := by
    unfold energy
    rw [sumFin_point _ (fun j => ε j * (ind (setb s.m k true j) - ind (s.n j))) l]
    · simp only [setb_self, hn, ind_true, ind_false]
      simp only [Int.mul_sub, Int.mul_one, Int.mul_zero]; omega
    · intro j hj; simp [setb_ne _ _ hj]
  rw [step2, step1]

/-- (10) PAIR (MOLECULAR-FIELD) SHIFT: `[H, d_l c_k] = (ε_l − ε_k) d_l c_k`.  Taking the
    expectation value in any physical state gives `(ε_l − ε_k) ⟨d_l c_k⟩ = 0`: the molecular
    order parameter pairs only modes of equal energy. -/
theorem pair_shift (ε : Fin K → Int) (k l : Fin K) (ψ : Vec K) (s : Config K) :
    H ε (d l (c k ψ)) s - d l (c k (H ε ψ)) s = (ε l - ε k) * d l (c k ψ) s := by
  rw [H_diag]
  unfold d c
  dsimp only
  cases hn : s.n l <;> cases hm : s.m k <;> simp
  rw [H_diag, energy_pair ε s k l hm hn]
  simp only [Int.mul_sub, Int.sub_mul, Int.add_mul, Int.mul_add]
  generalize energy ε s = E
  generalize dsg s l = A
  generalize sgn (below ⟨s.m, setb s.n l true⟩ k) = B
  generalize ψ ⟨setb s.m k true, setb s.n l true⟩ = P
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  omega

/-! ## 6. The balanced form, zero-point energy, no-go, scale, sign argument -/

/-- (11) For any decomposition `H = T + V`,  `H Ψ = 0  ↔  T Ψ = − V Ψ`. -/
theorem balance_iff (Hop T V : Vec K → Vec K)
    (hsplit : ∀ ψ s, Hop ψ s = T ψ s + V ψ s) (Ψ : Vec K) :
    (∀ s, Hop Ψ s = 0) ↔ (∀ s, T Ψ s = - V Ψ s) := by
  constructor
  · intro h s; have := h s; rw [hsplit] at this; omega
  · intro h s; rw [hsplit, h s]; omega

/-- Antisymmetrically (Weyl) ordered fermionic constraint, times two:
    `Σ ε_k [(c† c − c c†) − (d† d − d d†)]`. -/
def H_weyl2 (ε : Fin K → Int) (ψ : Vec K) : Vec K := fun s =>
  sumFin K (fun k => ε k * ((cdag k (c k ψ) s - c k (cdag k ψ) s)
                          - (ddag k (d k ψ) s - d k (ddag k ψ) s)))

/-- (12) Zero-point cancellation: each "/" mode carries the fermionic zero-point constant
    `−ε_k/2`, its mirror "\" partner `+ε_k/2`; Weyl ordering gives exactly `2H`. -/
theorem zero_point_cancellation (ε : Fin K → Int) (ψ : Vec K) (s : Config K) :
    H_weyl2 ε ψ s = 2 * H ε ψ s := by
  unfold H_weyl2 H
  rw [← sumFin_two_mul]
  apply sumFin_congr
  intro k
  rw [anti_number_c, anti_number_d, number_c, number_d]
  simp only [Int.sub_mul, Int.one_mul]
  have h1 : ind (s.m k) * ψ s - (ψ s - ind (s.m k) * ψ s)
            - (ind (s.n k) * ψ s - (ψ s - ind (s.n k) * ψ s))
          = 2 * (ind (s.m k) * ψ s - ind (s.n k) * ψ s) := by omega
  rw [h1, ← Int.mul_assoc, Int.mul_comm (ε k) 2, Int.mul_assoc]

/-- (13) No-go lemma (expectation form). -/
theorem no_go (t v : Int) (ht : 0 ≤ t) (hv : 0 ≤ v) (hsum : t + v = 0) :
    t = 0 ∧ v = 0 := by
  omega

/-- (14) Scale freedom (paper, `prop:scale`): `ker(λH) = ker H` for `λ ≠ 0`. -/
theorem kernel_scale (Hop : Vec K → Vec K) (lam : Int) (hl : lam ≠ 0) (Ψ : Vec K) :
    (∀ s, lam * Hop Ψ s = 0) ↔ (∀ s, Hop Ψ s = 0) := by
  constructor
  · intro h s
    rcases Int.mul_eq_zero.mp (h s) with h1 | h1
    · exact absurd h1 hl
    · exact h1
  · intro h s
    rw [h s, Int.mul_zero]

/-- (15) Sign argument of the Stelle-channel proposition: with `a = -c`, `b = 4c` the
    no-tachyon conditions `3a + b > 0` and `b < 0` cannot hold together. -/
theorem stelle_channel_tachyon (c : Int) :
    ¬ (3 * (-c) + 4 * c > 0 ∧ 4 * c < 0) := by
  omega

/-- (16) Rational independence (`thm:kernel`(c), per normal mode): every zero-energy
    configuration has equal occupations in the two mirror sectors. -/
def rat_indep (ε : Fin K → Int) : Prop :=
  ∀ cf : Fin K → Int, sumFin K (fun k => cf k * ε k) = 0 → ∀ k, cf k = 0

theorem kernel_molecular (ε : Fin K → Int) (s : Config K) (RI : rat_indep ε)
    (hE : energy ε s = 0) : ∀ k, s.m k = s.n k := by
  intro k
  have h := RI (fun j => ind (s.m j) - ind (s.n j)) (by
    rw [← hE]; unfold energy; apply sumFin_congr; intro j; exact Int.mul_comm _ _) k
  cases hm : s.m k <;> cases hn : s.n k <;> simp [hm, hn] at h ⊢

/-! ## 7. Sanity checks on a concrete instance (K = 2) -/

section Examples
def ε2 : Fin 2 → Int := fun k => if k = 0 then 3 else 7

-- One molecule in each mode solves the constraint.
example : H ε2 (molecules [0, 1] (vac 2)) = fun _ => 0 :=
  wdw_molecular_solution ε2 _
-- Its energy imbalance is zero; an unpaired atom has non-zero imbalance.
example : energy ε2 ⟨occ [0, 1], occ [0, 1]⟩ = 0 := by decide
example : energy ε2 ⟨fun k => if k = 0 then true else false, fun _ => false⟩ = 3 := by decide
-- Two molecules in the same mode vanish (Pauli).
example : molecules [0, 0] (vac 2) = fun _ => 0 := molecules_repeat 0 [] _
end Examples

end MolecularWDW

/-! ## 9. Spinor kinematics (paper Sec. II, App. A); polynomial identities over Int -/
namespace Spinor
/-- Gaussian-style complex numbers with integer components.  Every statement below is a
    polynomial identity with integer coefficients; one that holds for all integer arguments
    holds as an identity of polynomials, hence in every commutative ring (R, C included). -/
structure Cx where
  re : Int
  im : Int

@[simp] def cadd (a b : Cx) : Cx := ⟨a.re + b.re, a.im + b.im⟩
@[simp] def csub (a b : Cx) : Cx := ⟨a.re - b.re, a.im - b.im⟩
@[simp] def cneg (a : Cx) : Cx := ⟨-a.re, -a.im⟩
@[simp] def cmul (a b : Cx) : Cx := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
@[simp] def cconj (a : Cx) : Cx := ⟨a.re, -a.im⟩
@[simp] def creal (x : Int) : Cx := ⟨x, 0⟩

inductive I2 | i0 | i1
open I2

@[simp] def epsC : I2 → I2 → Cx
  | i0, i1 => ⟨1, 0⟩
  | i1, i0 => ⟨-1, 0⟩
  | _, _ => ⟨0, 0⟩

@[simp] def sum2 (f : I2 → Cx) : Cx := cadd (f i0) (f i1)

@[simp] def Xt (x0 x1 x2 x3 : Int) : I2 → I2 → Cx
  | i0, i0 => creal (x0 + x3)
  | i0, i1 => ⟨x1, -x2⟩
  | i1, i0 => ⟨x1, x2⟩
  | i1, i1 => creal (x0 - x3)

@[simp] def etaI (x0 x1 x2 x3 y0 y1 y2 y3 : Int) : Int := -(x0 * y0) + x1 * y1 + x2 * y2 + x3 * y3

theorem eta_from_pairing (x0 x1 x2 x3 y0 y1 y2 y3 : Int) :
    cneg (sum2 fun A => sum2 fun B => sum2 fun A' => sum2 fun B' =>
      cmul (cmul (epsC A B) (epsC A' B')) (cmul (Xt x0 x1 x2 x3 A A') (Xt y0 y1 y2 y3 B B')))
    = creal (etaI x0 x1 x2 x3 y0 y1 y2 y3 + etaI x0 x1 x2 x3 y0 y1 y2 y3) := by
  simp only [sum2, cadd, cneg, cmul, epsC, Xt, creal, etaI, Cx.mk.injEq]
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

@[simp] def omegaC (psi phi : I2 → Cx) : Cx :=
  sum2 fun A => sum2 fun B => cmul (epsC A B) (cmul (psi A) (phi B))

@[simp] def atom (o0 o1 io0 io1 : Cx) : I2 → I2 → Cx
  | i0, i0 => o0
  | i0, i1 => o1
  | i1, i0 => io0
  | i1, i1 => io1

set_option maxHeartbeats 4000000 in
theorem tetrad_metric_spinor (o0 o1 io0 io1 : Cx) (A A' B B' : I2) :
    cneg (sum2 fun al => sum2 fun be => sum2 fun ga => sum2 fun de =>
      cmul (cmul (epsC al be) (epsC ga de))
        (cmul (cmul (atom o0 o1 io0 io1 al A) (cconj (atom o0 o1 io0 io1 ga A')))
              (cmul (atom o0 o1 io0 io1 be B) (cconj (atom o0 o1 io0 io1 de B')))))
    = cneg (cmul (cmul (omegaC (atom o0 o1 io0 io1 i0) (atom o0 o1 io0 io1 i1))
                       (cconj (omegaC (atom o0 o1 io0 io1 i0) (atom o0 o1 io0 io1 i1))))
                 (cmul (epsC A B) (epsC A' B'))) := by
  obtain ⟨a, b⟩ := o0; obtain ⟨c, d⟩ := o1; obtain ⟨e, f⟩ := io0; obtain ⟨g, h⟩ := io1
  cases A <;> cases A' <;> cases B <;> cases B' <;>
  simp only [sum2, cadd, cneg, cmul, cconj, epsC, atom, omegaC, Cx.mk.injEq] <;>
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero,
    Int.sub_neg, Int.add_zero, Int.zero_add, Int.sub_zero, Int.zero_sub,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega


@[simp] def czero : Cx := ⟨0, 0⟩

theorem det_is_minus_eta (x0 x1 x2 x3 : Int) :
    csub (cmul (Xt x0 x1 x2 x3 i0 i0) (Xt x0 x1 x2 x3 i1 i1)) (cmul (Xt x0 x1 x2 x3 i0 i1) (Xt x0 x1 x2 x3 i1 i0))
    = creal (-(etaI x0 x1 x2 x3 x0 x1 x2 x3)) := by
  simp only [csub, cmul, Xt, creal, etaI, Cx.mk.injEq]
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

/-- `prop:null`: a single molecule xi^A conj(xi^{A'}) has zero determinant (it is null). -/
theorem single_molecule_null (xi0 xi1 : Cx) :
    csub (cmul (cmul xi0 (cconj xi0)) (cmul xi1 (cconj xi1)))
         (cmul (cmul xi0 (cconj xi1)) (cmul xi1 (cconj xi0))) = czero := by
  obtain ⟨a, b⟩ := xi0; obtain ⟨c, d⟩ := xi1
  simp only [csub, cmul, cconj, czero, Cx.mk.injEq]
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero, Int.sub_neg,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

@[simp] def spin2 (p0 p1 : Cx) : I2 → Cx
  | i0 => p0
  | i1 => p1

/-- App. A, dyad identity: psi^A phi^B - phi^A psi^B = omega(psi, phi) eps^{AB}. -/
theorem dyad_identity (p0 p1 q0 q1 : Cx) (A B : I2) :
    csub (cmul (spin2 p0 p1 A) (spin2 q0 q1 B)) (cmul (spin2 q0 q1 A) (spin2 p0 p1 B))
    = cmul (omegaC (spin2 p0 p1) (spin2 q0 q1)) (epsC A B) := by
  obtain ⟨a, b⟩ := p0; obtain ⟨c, d⟩ := p1; obtain ⟨e, f⟩ := q0; obtain ⟨g, h⟩ := q1
  cases A <;> cases B <;>
  simp only [csub, cmul, sum2, cadd, spin2, omegaC, epsC, Cx.mk.injEq] <;>
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero, Int.sub_neg,
    Int.add_zero, Int.zero_add, Int.sub_zero, Int.zero_sub,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega

@[simp] def ci : Cx := ⟨0, 1⟩
inductive I4 | e0 | e1 | e2 | e3
open I4
@[simp] def sum4 (f : I4 → Cx) : Cx := cadd (cadd (f e0) (f e1)) (cadd (f e2) (f e3))
/-- antisymmetric theta_ab from six independent components -/
@[simp] def theta (t01 t02 t03 t12 t13 t23 : Int) : I4 → I4 → Int
  | e0, e1 => t01 | e0, e2 => t02 | e0, e3 => t03 | e1, e2 => t12 | e1, e3 => t13 | e2, e3 => t23
  | e1, e0 => -t01 | e2, e0 => -t02 | e3, e0 => -t03 | e2, e1 => -t12 | e3, e1 => -t13 | e3, e2 => -t23
  | _, _ => 0
@[simp] def etaD : I4 → Int | e0 => -1 | _ => 1
@[simp] def lc3 : I4 → I4 → I4 → Int
  | e1, e2, e3 => 1 | e2, e3, e1 => 1 | e3, e1, e2 => 1
  | e1, e3, e2 => -1 | e3, e2, e1 => -1 | e2, e1, e3 => -1
  | _, _, _ => 0
@[simp] def lc4 : I4 → I4 → I4 → I4 → Int
  | e0,e1,e2,e3 => 1 | e0,e1,e3,e2 => -1 | e0,e2,e1,e3 => -1 | e0,e2,e3,e1 => 1 | e0,e3,e1,e2 => 1 | e0,e3,e2,e1 => -1
  | e1,e0,e2,e3 => -1 | e1,e0,e3,e2 => 1 | e1,e2,e0,e3 => 1 | e1,e2,e3,e0 => -1 | e1,e3,e0,e2 => -1 | e1,e3,e2,e0 => 1
  | e2,e0,e1,e3 => 1 | e2,e0,e3,e1 => -1 | e2,e1,e0,e3 => -1 | e2,e1,e3,e0 => 1 | e2,e3,e0,e1 => 1 | e2,e3,e1,e0 => -1
  | e3,e0,e1,e2 => -1 | e3,e0,e2,e1 => 1 | e3,e1,e0,e2 => 1 | e3,e1,e2,e0 => -1 | e3,e2,e0,e1 => -1 | e3,e2,e1,e0 => 1
  | _,_,_,_ => 0
@[simp] def sigma : I4 → I2 → I2 → Cx
  | e0, i0, i0 => ⟨1, 0⟩ | e0, i1, i1 => ⟨1, 0⟩
  | e1, i0, i1 => ⟨1, 0⟩ | e1, i1, i0 => ⟨1, 0⟩
  | e2, i0, i1 => ⟨0, -1⟩ | e2, i1, i0 => ⟨0, 1⟩
  | e3, i0, i0 => ⟨1, 0⟩ | e3, i1, i1 => ⟨-1, 0⟩
  | _, _, _ => ⟨0, 0⟩
@[simp] def mmul (P Q : I2 → I2 → Cx) (A B : I2) : Cx := sum2 fun C => cmul (P A C) (Q C B)
@[simp] def tr2 (P : I2 → I2 → Cx) : Cx := cadd (P i0 i0) (P i1 i1)
/-- S~ = 4 S(theta) = -2 theta_{0i} sigma_i + i eps_{ijk} theta_{ij} sigma_k  (the self-dual generator `eq:Stheta` times 4) -/
@[simp] def St (t01 t02 t03 t12 t13 t23 : Int) (A B : I2) : Cx :=
  cadd (sum4 fun i => match i with
          | e0 => ⟨0, 0⟩
          | i => cmul (creal (-(theta t01 t02 t03 t12 t13 t23 e0 i + theta t01 t02 t03 t12 t13 t23 e0 i))) (sigma i A B))
       (sum4 fun k => match k with
          | e0 => ⟨0, 0⟩
          | k => cmul (cmul ci (sum4 fun i => sum4 fun j => creal (lc3 i j k * theta t01 t02 t03 t12 t13 t23 i j))) (sigma k A B))
@[simp] def up (th : I4 → I4 → Int) (a b : I4) : Int := etaD a * etaD b * th a b

set_option maxHeartbeats 8000000 in
/-- The chiral-trace identity `eq:chiral_trace` times 16:  tr S~ S~' = -4 theta_ab theta'^ab + 2 i eps_abcd theta^ab theta'^cd -/
theorem chiral_trace_times16 (t01 t02 t03 t12 t13 t23 u01 u02 u03 u12 u13 u23 : Int) :
    let th := theta t01 t02 t03 t12 t13 t23
    let th' := theta u01 u02 u03 u12 u13 u23
    let X := (sum4 fun a => sum4 fun b => creal (th a b * up th' a b)).re
    let E := sum4 fun a => sum4 fun b => sum4 fun c => sum4 fun d => creal (lc4 a b c d * up th a b * up th' c d)
    tr2 (mmul (St t01 t02 t03 t12 t13 t23) (St u01 u02 u03 u12 u13 u23))
      = cadd (creal (-(X + X + X + X))) (cmul ci (cadd E E)) := by
  intro th th' X E
  simp only [th, th', X, E, tr2, mmul, St, sum2, sum4, cadd, cmul, creal, ci, theta, etaD, lc3, lc4, sigma, up, Cx.mk.injEq]
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero,
    Int.sub_neg, Int.add_zero, Int.zero_add, Int.sub_zero, Int.zero_sub, Int.neg_add,
    Int.mul_assoc, Int.mul_comm, Int.mul_left_comm] <;> omega
@[simp] def su2m (a b : Cx) : I2 → I2 → Cx
  | i0, i0 => a
  | i0, i1 => b
  | i1, i0 => ⟨-b.re, b.im⟩
  | i1, i1 => ⟨a.re, -a.im⟩

/-- `prop:kramers`: for U = [[a, b], [-conj b, conj a]] (SU(2) form), sigma_y conj(U) sigma_y = U, the identity
    behind the Kramers degeneracy and the mirror isospectrality hbar = Theta^-1 h Theta. -/
theorem su2_pseudoreal (a b : Cx) (A B : I2) :
    (sum2 fun C => sum2 fun D => cmul (cmul (sigma e2 A C) (cconj (su2m a b C D))) (sigma e2 D B)) = su2m a b A B := by
  obtain ⟨p, q⟩ := a; obtain ⟨r, s⟩ := b
  cases A <;> cases B <;>
  simp only [sum2, cadd, cmul, cconj, sigma, su2m, Cx.mk.injEq] <;>
  constructor <;>
  simp only [Int.add_mul, Int.mul_add, Int.sub_mul, Int.mul_sub, Int.neg_mul, Int.mul_neg,
    Int.mul_one, Int.one_mul, Int.mul_zero, Int.zero_mul, Int.neg_neg, Int.neg_zero, Int.sub_neg,
    Int.add_zero, Int.zero_add, Int.sub_zero, Int.zero_sub] <;> omega
end Spinor

/-! ## 10. Boundary conformal algebra (paper `prop:conformal`), by exact computation -/
namespace Conformal
structure GI where
  re : Int
  im : Int
def gadd (a b : GI) : GI := ⟨a.re + b.re, a.im + b.im⟩
def gsub (a b : GI) : GI := ⟨a.re - b.re, a.im - b.im⟩
def gmul (a b : GI) : GI := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩
def gscale (z : Int) (a : GI) : GI := ⟨z * a.re, z * a.im⟩
def gconj (a : GI) : GI := ⟨a.re, -a.im⟩
def gz : GI := ⟨0, 0⟩
def g1 : GI := ⟨1, 0⟩
def geqb (a b : GI) : Bool := a.re == b.re && a.im == b.im
inductive I4 | e0 | e1 | e2 | e3
open I4
def idx : List I4 := [e0, e1, e2, e3]
abbrev M := I4 → I4 → GI
def msum (f : I4 → GI) : GI := idx.foldr (fun k acc => gadd (f k) acc) gz
def mmul (A B : M) : M := fun i j => msum (fun k => gmul (A i k) (B k j))
def madd (A B : M) : M := fun i j => gadd (A i j) (B i j)
def msub (A B : M) : M := fun i j => gsub (A i j) (B i j)
def mscale (z : Int) (A : M) : M := fun i j => gscale z (A i j)
def comm (A B : M) : M := msub (mmul A B) (mmul B A)
def mzero : M := fun _ _ => gz
def mid : M := fun i j => match i, j with
  | e0, e0 => g1 | e1, e1 => g1 | e2, e2 => g1 | e3, e3 => g1 | _, _ => gz
def meqb (A B : M) : Bool := idx.all fun i => idx.all fun j => geqb (A i j) (B i j)
def adj (A : M) : M := fun i j => gconj (A j i)
/-- Pauli blocks: sigma^a = (1, sx, sy, sz), sigmabar^a = (-1, sx, sy, sz) -/
def sig : I4 → Bool → Bool → GI
  | e0, false, false => g1 | e0, true, true => g1
  | e1, false, true => g1 | e1, true, false => g1
  | e2, false, true => ⟨0, -1⟩ | e2, true, false => ⟨0, 1⟩
  | e3, false, false => g1 | e3, true, true => ⟨-1, 0⟩
  | _, _, _ => gz
def sigbar (a : I4) (r c : Bool) : GI := match a with
  | e0 => gscale (-1) (sig e0 r c) | _ => sig a r c
/-- rows/columns e0,e1: upper block (dual of right atoms); e2,e3: lower block (left atoms) -/
def blk : I4 → Bool | e0 => false | e1 => false | e2 => true | e3 => true
def sub : I4 → Bool | e0 => false | e1 => true | e2 => false | e3 => true
def gam (a : I4) : M := fun i j =>
  match blk i, blk j with
  | false, true => sig a (sub i) (sub j)
  | true, false => sigbar a (sub i) (sub j)
  | _, _ => gz
def g5 : M := fun i j => match i, j with
  | e0, e0 => g1 | e1, e1 => g1 | e2, e2 => ⟨-1, 0⟩ | e3, e3 => ⟨-1, 0⟩ | _, _ => gz
def etaZ : I4 → Int | e0 => -1 | _ => 1
def gamlow (a : I4) : M := mscale (etaZ a) (gam a)
/-- generators times 2: Jt_ab = gamma^a gamma^b (a ≠ b), Pt_a = gamma_a gamma_5 -/
def Jt (a b : I4) : M := mmul (gam a) (gam b)
def Pt (a : I4) : M := mmul (gamlow a) g5
def Dt : M := Pt e0
def Pc (i : I4) : M := madd (Jt e0 i) (Pt i)
def Kc (i : I4) : M := msub (Jt e0 i) (Pt i)
def delta : I4 → I4 → Int | e1, e1 => 1 | e2, e2 => 1 | e3, e3 => 1 | _, _ => 0
def Mt (i j : I4) : M := match i, j with
  | e1, e1 => mzero | e2, e2 => mzero | e3, e3 => mzero | _, _ => Jt i j
def spat : List I4 := [e1, e2, e3]
def etaDiag : I4 → I4 → Int | e0, e0 => -2 | e1, e1 => 2 | e2, e2 => 2 | e3, e3 => 2 | _, _ => 0
def clifford_ok : Bool := idx.all fun a => idx.all fun b =>
  meqb (madd (mmul (gam a) (gam b)) (mmul (gam b) (gam a))) (mscale (etaDiag a b) mid)
def conformal_ok : Bool := spat.all fun i =>
  meqb (comm Dt (Pc i)) (mscale 2 (Pc i)) && meqb (comm Dt (Kc i)) (mscale (-2) (Kc i)) &&
  spat.all fun j =>
    meqb (comm (Kc i) (Pc j)) (mscale 4 (msub (Mt i j) (mscale (delta i j) Dt))) &&
    meqb (comm Dt (Mt i j)) mzero && meqb (comm (Pc i) (Pc j)) mzero && meqb (comm (Kc i) (Kc j)) mzero &&
    spat.all fun k =>
      meqb (comm (Mt i j) (Pc k)) (mscale 2 (msub (mscale (delta j k) (Pc i)) (mscale (delta i k) (Pc j)))) &&
      meqb (comm (Mt i j) (Kc k)) (mscale 2 (msub (mscale (delta j k) (Kc i)) (mscale (delta i k) (Kc j))))
def blockdiag (A : M) : Bool := idx.all fun i => idx.all fun j => if blk i == blk j then true else geqb (A i j) gz
def offdiag (A : M) : Bool := idx.all fun i => idx.all fun j => if blk i == blk j then geqb (A i j) gz else true
/-- M_ij block diagonal and anti-Hermitian (same SU(2) on / and \); D Hermitian, off diagonal, Dt^2 = 1
    (so D = Dt/2 has eigenvalues +-1/2). -/
def structure_ok : Bool :=
  (spat.all fun i => spat.all fun j => blockdiag (Mt i j) && meqb (adj (Mt i j)) (mscale (-1) (Mt i j)))
  && meqb (adj Dt) Dt && offdiag Dt && meqb (mmul Dt Dt) mid
theorem clifford_algebra : clifford_ok = true := by decide
/-- `prop:conformal` with generators doubled (Dt = 2D, Pc = 2P, Kc = 2K, Mt = 2M):
    [Dt,Pc_i] = 2Pc_i, [Dt,Kc_i] = -2Kc_i, [Kc_i,Pc_j] = 4(Mt_ij - delta_ij Dt), [Dt,Mt_ij] = 0,
    [Pc_i,Pc_j] = [Kc_i,Kc_j] = 0, [Mt_ij,X_k] = 2(delta_jk X_i - delta_ik X_j). -/
theorem boundary_conformal_algebra : conformal_ok = true := by decide
theorem conformal_generator_structure : structure_ok = true := by decide
end Conformal

/-! ## 11. Cleared-denominator forms of the field-theory formulas -/
namespace FieldIdentities
/-- Scalaron mass `eq:scalaron_mass`, numerator: f' - Rbar f'' = alpha for f = alpha R + beta R^2, so
    m_f^2 = (f'/f'' - Rbar)/3 = alpha/(3 f'') = alpha/(6 beta). -/
theorem scalaron_numerator (α β R : Int) : (α + 2 * β * R) - R * (2 * β) = α := by
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]; omega
/-- de Sitter entropy `eq:entropy`, cross-multiplied:  3/(64 π G Λ) = S_dS/(64 π^2) with S_dS = 3π/(GΛ). -/
theorem desitter_entropy_cleared (p G L : Int) :
    3 * (64 * (p * p)) * (G * L) = (3 * p) * (64 * p * G * L) := by
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
/-- R^2 coefficient `eq:R2coef`, cross-multiplied: with A_s (24 π^2 M_P^2) = N^2 M^2, M_P^2 (288 π^2 A_s) = 12 M^2 N^2. -/
theorem R2_coefficient_cleared (N M Mp p As : Int) (hAs : 24 * (p * p) * (Mp * Mp) * As = N * N * (M * M)) :
    Mp * Mp * (288 * (p * p) * As) = 12 * (M * M) * (N * N) := by
  have h12 : Mp * Mp * (288 * (p * p) * As) = 12 * (24 * (p * p) * (Mp * Mp) * As) := by
    rw [show (288 : Int) = 12 * 24 from rfl]; simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
  rw [h12, hAs]; simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
/-- Starobinsky potential (`sec:inflation`), cleared: with R = 3 M^2 (F - 1), i.e. F = f'(R) for f = R + R^2/(6 M^2),
    6 M^2 (R F - f) = R^2, so (M_P^2/2)(R F - f)/F^2 = (3/4) M^2 M_P^2 (1 - 1/F)^2. -/
theorem starobinsky_cleared (M F R : Int) (hR : 3 * (M * M) * (F - 1) = R) :
    6 * (M * M) * (R * F) - (6 * (M * M) * R + R * R) = R * R := by
  have key : 6 * (M * M) * (R * F) - (6 * (M * M) * R + R * R) - R * R
           = R * (3 * (M * M) * (F - 1) - R) + R * (3 * (M * M) * (F - 1) - R) := by
    rw [show (6 : Int) = 3 + 3 from rfl]
    simp only [Int.mul_sub, Int.sub_mul, Int.mul_add, Int.add_mul, Int.mul_one, Int.one_mul, Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]
    omega
  rw [hR, Int.sub_self, Int.mul_zero, Int.add_zero] at key; omega
/-- Stelle masses `eq:stelle_masses`: Ricci basis a = -c, b = 4c and Weyl basis beta_R = c/3, alpha_W = 2c give the same
    masses: 2(3a+b) = 6 beta_R = 2c (scalar) and b = 2 alpha_W = 4c (spin 2). -/
theorem stelle_bases_agree (c bR aW : Int) (h1 : 3 * bR = c) (h2 : aW = 2 * c) :
    2 * (3 * (-c) + 4 * c) = 2 * c ∧ 6 * bR = 2 * c ∧ 4 * c = 2 * aW := by omega
theorem scalaron_numerator_FL (xi Phi2 β R : Int) : ((1 - xi * Phi2) + 2 * β * R) - R * (2 * β) = 1 - xi * Phi2 := by
  simp only [Int.mul_comm, Int.mul_assoc, Int.mul_left_comm]; omega
end FieldIdentities

/-! ## 12. Audit: no `sorry`, only Lean's standard axioms -/
#print axioms MolecularWDW.car_c
#print axioms MolecularWDW.car_d
#print axioms MolecularWDW.pauli_c
#print axioms MolecularWDW.cdag_anticomm
#print axioms MolecularWDW.c_cdag_anticomm
#print axioms MolecularWDW.ddag_anticomm
#print axioms MolecularWDW.cdag_ddag_anticomm
#print axioms MolecularWDW.molecules_commute
#print axioms MolecularWDW.molecule_pauli
#print axioms MolecularWDW.molecule_hardcore
#print axioms MolecularWDW.molecule_cross
#print axioms MolecularWDW.molecule_atom_comm_c
#print axioms MolecularWDW.molecule_atom_comm_d
#print axioms MolecularWDW.H_diag
#print axioms MolecularWDW.H_mirror
#print axioms MolecularWDW.H_Xdag_comm
#print axioms MolecularWDW.wdw_molecular_solution
#print axioms MolecularWDW.molecules_at_occ
#print axioms MolecularWDW.molecules_support
#print axioms MolecularWDW.distinct_solutions
#print axioms MolecularWDW.molecules_repeat
#print axioms MolecularWDW.bcs_solution
#print axioms MolecularWDW.pair_shift
#print axioms MolecularWDW.balance_iff
#print axioms MolecularWDW.zero_point_cancellation
#print axioms MolecularWDW.no_go
#print axioms MolecularWDW.kernel_scale
#print axioms MolecularWDW.stelle_channel_tachyon
#print axioms MolecularWDW.kernel_molecular
#print axioms Spinor.eta_from_pairing
#print axioms Spinor.det_is_minus_eta
#print axioms Spinor.single_molecule_null
#print axioms Spinor.dyad_identity
#print axioms Spinor.tetrad_metric_spinor
#print axioms Spinor.chiral_trace_times16
#print axioms Spinor.su2_pseudoreal
#print axioms Conformal.clifford_algebra
#print axioms Conformal.boundary_conformal_algebra
#print axioms Conformal.conformal_generator_structure
#print axioms FieldIdentities.scalaron_numerator
#print axioms FieldIdentities.scalaron_numerator_FL
#print axioms FieldIdentities.stelle_bases_agree
#print axioms FieldIdentities.desitter_entropy_cleared
#print axioms FieldIdentities.R2_coefficient_cleared
#print axioms FieldIdentities.starobinsky_cleared
