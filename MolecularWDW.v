(* ===========================================================================
   MolecularWDW.v
   Independent Rocq (Coq >= 8.18) formalization accompanying the paper

     "Spacetime Molecules: A Pre-geometric Wheeler-DeWitt Model
      Built from Fermionic Chiral Spinor Atoms"

   This file was written separately from the companion Lean 4 file
   MolecularWDW.lean and uses a different encoding (occupations are
   finite lists of booleans, not Fin-indexed functions; Jordan-Wigner signs from
   prefix counts, not Fin sums; polynomial identities are proved
   over an arbitrary commutative ring, not over the integers).  Only the
   informal statements are shared.

   CONTENTS (paper labels in brackets)
   Part A  Exact solution of the constraint with FERMIONIC atoms (Secs. III-IV)
     A1  fermionic ladder operators on occupation lists (mode-interleaved
         Jordan-Wigner signs): {c_k,c_k^dag} = {d_k,d_k^dag} = 1, {c_k,c_j^dag} = 0,
         c^dag c^dag, d^dag d^dag and c^dag d^dag anticommute, Pauli (c_k^dag)^2 = 0
     A2  MOLECULES ARE BOSONS: X_k^dag = c_k^dag d_k^dag commute with each other and with
         the atoms of other modes; hard-core algebra [X_k, X_k^dag] = 1 - n^c_k - n^d_k,
         [X_k, X_j^dag] = 0 (k <> j), (X_k^dag)^2 = 0               [prop:hardcore]
     A3  H = sum_k eps_k (c_k^dag c_k - d_k^dag d_k) is diagonal, eigenvalue E(m,n);
         mirror antisymmetry H M = - M H; [H, X_k^dag] = 0
     A4  H|0> = 0; every multi-molecule state solves H Psi = 0; molecular states on
         different sets of modes are distinct basis vectors; a repeated mode gives
         zero; every BCS condensate prod (u + v X^dag)|0> solves H Psi = 0;
         pair shift [H, d_j c_k] = (eps_j - eps_k) d_j c_k  [thm:kernel, prop:condensate,
         prop:fieldeq]
     A5  H Psi = 0 <-> T Psi = - V Psi; fermionic zero-point cancellation [prop:zp];
         no-go [thm:nogo]; scale freedom [prop:scale]; Stelle sign [prop:stelle];
         rational independence forces m_k = n_k [thm:kernel(c)]
   Part B  Spinor kinematics, over an arbitrary commutative ring (Sec. II, App. A)
     B1  [eq:etaeps]: -eps eps X Y = 2 eta(X,Y) and det X = -eta(X,X) (unnormalized soldering)
     B2  [prop:null]: det(xi xi^dagger) = 0
     B3  dyad identity (App. A) and [prop:tetrad] in spinor form
     B4  [eq:chiral_trace], the chiral trace, multiplied by 16
     B5  [prop:kramers]: sigma_y conj(U) sigma_y = U for U of SU(2) form
   Part C  Boundary conformal algebra [prop:conformal], by exact computation with
           Gaussian-integer matrices; Clifford algebra of the Weyl-basis gammas
   Part D  Field identities over the real numbers (scalaron mass, Stelle masses,
           de Sitter entropy, Starobinsky potential, R^2 coefficient)

   Normalizations: the paper's soldering carries a factor 1/sqrt 2; Part B uses
   X~ = X^0 1 + X^i sigma_i, which multiplies [eq:etaeps] by 2.  Part C uses the
   generators multiplied by 2 so that all entries are Gaussian integers.

   Build:  coqc MolecularWDW.v      (tested with Coq 8.18.0, standard library only)
   The final section prints the assumptions of every main theorem.
   =========================================================================== *)

From Coq Require Import ZArith Lia List Arith Bool Ring Field.
From Coq Require Import Reals Lra.
Import ListNotations.

(* ===================================================================== *)
(** * Part A. Exact solution of the constraint                           *)
(* ===================================================================== *)

Module FockSpace.
Open Scope nat_scope.

(** Occupation lists of booleans (fermions: each mode is empty or singly occupied).
    Mode k of a list l has occupation [get l k]. *)
Fixpoint upd (l : list bool) (k : nat) (b : bool) : list bool :=
  match l, k with
  | [], _ => []
  | x :: t, O => b :: t
  | x :: t, S k' => x :: upd t k' b
  end.

Definition get (l : list bool) (k : nat) : bool := nth k l false.
Definition b2n (b : bool) : nat := if b then 1 else 0.
Fixpoint cnt (l : list bool) : nat :=
  match l with [] => 0 | x :: t => b2n x + cnt t end.

Lemma length_upd : forall l k b, length (upd l k b) = length l.
Proof. induction l as [|x t IH]; intros [|k] b; simpl; auto. Qed.

Lemma get_upd_same : forall l k b, k < length l -> get (upd l k b) k = b.
Proof.
  unfold get; induction l as [|x t IH]; intros k b H; simpl in *; [lia|].
  destruct k as [|k]; simpl; [reflexivity|]. apply IH; lia.
Qed.

Lemma get_upd_other : forall l k j b, j <> k -> get (upd l k b) j = get l j.
Proof.
  unfold get; induction l as [|x t IH]; intros k j b H; simpl; [reflexivity|].
  destruct k as [|k], j as [|j]; simpl; try reflexivity; try lia.
  apply IH; lia.
Qed.

Lemma get_true_lt : forall l k, get l k = true -> k < length l.
Proof.
  unfold get; induction l as [|x t IH]; intros k H; simpl in *.
  - destruct k; discriminate.
  - destruct k as [|k]; [lia|]. apply IH in H. lia.
Qed.

Lemma upd_upd : forall l k b b', upd (upd l k b) k b' = upd l k b'.
Proof. induction l as [|x t IH]; intros [|k] b b'; simpl; try rewrite IH; reflexivity. Qed.

Lemma upd_get : forall l k, upd l k (get l k) = l.
Proof. unfold get; induction l as [|x t IH]; intros [|k]; simpl; try rewrite IH; reflexivity. Qed.

Lemma upd_eq : forall l k b, get l k = b -> upd l k b = l.
Proof. intros l k b <-. apply upd_get. Qed.

Lemma upd_comm : forall l k j b b', k <> j -> upd (upd l k b) j b' = upd (upd l j b') k b.
Proof.
  induction l as [|x t IH]; intros k j b b' H; simpl; [reflexivity|].
  destruct k as [|k], j as [|j]; simpl; try reflexivity; try lia.
  rewrite IH by lia. reflexivity.
Qed.

Lemma firstn_upd : forall l k j b, firstn k (upd l j b) = upd (firstn k l) j b.
Proof.
  induction l as [|x t IH]; intros k j b.
  - destruct k; simpl; reflexivity.
  - destruct k as [|k]; simpl; [reflexivity|].
    destruct j as [|j]; simpl; [reflexivity|]. rewrite IH. reflexivity.
Qed.

Lemma upd_oob : forall l j b, length l <= j -> upd l j b = l.
Proof.
  induction l as [|x t IH]; intros j b H; simpl in *; [reflexivity|].
  destruct j as [|j]; [lia|]. rewrite IH by lia. reflexivity.
Qed.

Lemma cnt_upd : forall l j b, j < length l -> cnt (upd l j b) + b2n (get l j) = cnt l + b2n b.
Proof.
  unfold get; induction l as [|x t IH]; intros j b H; simpl in *; [lia|].
  destruct j as [|j]; simpl.
  - lia.
  - specialize (IH j b ltac:(lia)). lia.
Qed.

Lemma get_firstn : forall l k j, j < k -> get (firstn k l) j = get l j.
Proof.
  unfold get; induction l as [|x t IH]; intros k j H.
  - destruct k, j; reflexivity.
  - destruct k as [|k]; [lia|]. destruct j as [|j]; simpl; [reflexivity|]. apply IH; lia.
Qed.

Lemma cnt_firstn_upd_ge : forall l k j b, k <= j -> cnt (firstn k (upd l j b)) = cnt (firstn k l).
Proof.
  intros l k j b H. rewrite firstn_upd, upd_oob; [reflexivity|]. rewrite firstn_length. lia.
Qed.

Lemma cnt_firstn_upd_lt : forall l k j b, j < k -> j < length l ->
  cnt (firstn k (upd l j b)) + b2n (get l j) = cnt (firstn k l) + b2n b.
Proof.
  intros l k j b Hjk Hj. rewrite firstn_upd. rewrite <- (get_firstn l k j Hjk).
  apply cnt_upd. rewrite firstn_length. lia.
Qed.

Lemma get_repeat_false : forall K k, get (repeat false K) k = false.
Proof. unfold get; induction K as [|K IH]; intros [|k]; simpl; auto. Qed.

Close Scope nat_scope.
Open Scope Z_scope.

Definition Config : Type := (list bool * list bool)%type.
Definition Vec : Type := Config -> Z.
Definition b2z (b : bool) : Z := if b then 1 else 0.

(** Basis ordering: modes in increasing order, within mode k first c_k^dag then d_k^dag
    (mode-interleaved Jordan-Wigner).  [below s k] counts the atoms in modes below k. *)
Definition below (s : Config) (k : nat) : nat :=
  (cnt (firstn k (fst s)) + cnt (firstn k (snd s)))%nat.

Definition sgn (x : nat) : Z := if Nat.even x then 1 else -1.

Lemma sgn_S : forall x, sgn (S x) = - sgn x.
Proof. intros x. unfold sgn. rewrite Nat.even_succ, <- Nat.negb_even. destruct (Nat.even x); reflexivity. Qed.

Lemma sgn_sq : forall x, sgn x * sgn x = 1.
Proof. intros x. unfold sgn. destruct (Nat.even x); reflexivity. Qed.

Lemma sgn_SS : forall x, sgn (S (S x)) = sgn x.
Proof. intros x. rewrite !sgn_S. ring. Qed.

Lemma below_m_ge : forall m n k j b, (k <= j)%nat -> below (upd m j b, n) k = below (m, n) k.
Proof. intros. unfold below; cbn [fst snd]. rewrite cnt_firstn_upd_ge by assumption. reflexivity. Qed.

Lemma below_n_ge : forall m n k j b, (k <= j)%nat -> below (m, upd n j b) k = below (m, n) k.
Proof. intros. unfold below; cbn [fst snd]. rewrite cnt_firstn_upd_ge by assumption. reflexivity. Qed.

Lemma below_m_lt : forall m n k j b, (j < k)%nat -> (j < length m)%nat ->
  (below (upd m j b, n) k + b2n (get m j) = below (m, n) k + b2n b)%nat.
Proof. intros m n k j b H1 H2. unfold below; cbn [fst snd]. pose proof (cnt_firstn_upd_lt m k j b H1 H2). lia. Qed.

Lemma below_n_lt : forall m n k j b, (j < k)%nat -> (j < length n)%nat ->
  (below (m, upd n j b) k + b2n (get n j) = below (m, n) k + b2n b)%nat.
Proof. intros m n k j b H1 H2. unfold below; cbn [fst snd]. pose proof (cnt_firstn_upd_lt n k j b H1 H2). lia. Qed.

Definition cdag (k : nat) (psi : Vec) : Vec := fun s =>
  if get (fst s) k then sgn (below s k) * psi (upd (fst s) k false, snd s) else 0.
Definition c (k : nat) (psi : Vec) : Vec := fun s =>
  if get (fst s) k then 0 else sgn (below s k) * psi (upd (fst s) k true, snd s).
Definition dsg (s : Config) (k : nat) : Z := sgn (below s k + b2n (get (fst s) k)).
Definition ddag (k : nat) (psi : Vec) : Vec := fun s =>
  if get (snd s) k then dsg s k * psi (fst s, upd (snd s) k false) else 0.
Definition d (k : nat) (psi : Vec) : Vec := fun s =>
  if get (snd s) k then 0 else dsg s k * psi (fst s, upd (snd s) k true).

(** A1: canonical anticommutation relations and the Pauli principle *)
Lemma number_c : forall k psi s, cdag k (c k psi) s = b2z (get (fst s) k) * psi s.
Proof.
  intros k psi [m n]; unfold cdag, c; cbn [fst snd].
  destruct (get m k) eqn:E; [|unfold b2z; ring].
  pose proof (get_true_lt m k E) as Hk.
  rewrite get_upd_same by exact Hk. rewrite below_m_ge by lia.
  rewrite upd_upd, upd_eq by exact E.
  unfold b2z. rewrite Z.mul_assoc, sgn_sq. ring.
Qed.

Lemma number_d : forall k psi s, ddag k (d k psi) s = b2z (get (snd s) k) * psi s.
Proof.
  intros k psi [m n]; unfold ddag, d, dsg; cbn [fst snd].
  destruct (get n k) eqn:E; [|unfold b2z; ring].
  pose proof (get_true_lt n k E) as Hk.
  rewrite get_upd_same by exact Hk. rewrite below_n_ge by lia.
  rewrite upd_upd, upd_eq by exact E.
  unfold b2z. rewrite Z.mul_assoc, sgn_sq. ring.
Qed.

Lemma anti_number_c : forall k psi s, (k < length (fst s))%nat ->
  c k (cdag k psi) s = (1 - b2z (get (fst s) k)) * psi s.
Proof.
  intros k psi [m n] H; simpl in H; unfold cdag, c; cbn [fst snd].
  destruct (get m k) eqn:E; [unfold b2z; ring|].
  rewrite get_upd_same by exact H. rewrite below_m_ge by lia.
  rewrite upd_upd, upd_eq by exact E.
  unfold b2z. rewrite Z.mul_assoc, sgn_sq. ring.
Qed.

Lemma anti_number_d : forall k psi s, (k < length (snd s))%nat ->
  d k (ddag k psi) s = (1 - b2z (get (snd s) k)) * psi s.
Proof.
  intros k psi [m n] H; simpl in H; unfold ddag, d, dsg; cbn [fst snd].
  destruct (get n k) eqn:E; [unfold b2z; ring|].
  rewrite get_upd_same by exact H. rewrite below_n_ge by lia.
  rewrite upd_upd, upd_eq by exact E.
  unfold b2z. rewrite Z.mul_assoc, sgn_sq. ring.
Qed.

Theorem car_c : forall k psi s, (k < length (fst s))%nat ->
  c k (cdag k psi) s + cdag k (c k psi) s = psi s.
Proof. intros. rewrite anti_number_c, number_c by assumption. ring. Qed.

Theorem car_d : forall k psi s, (k < length (snd s))%nat ->
  d k (ddag k psi) s + ddag k (d k psi) s = psi s.
Proof. intros. rewrite anti_number_d, number_d by assumption. ring. Qed.

Theorem pauli_c : forall k psi s, cdag k (cdag k psi) s = 0.
Proof.
  intros k psi [m n]; unfold cdag; cbn [fst snd].
  destruct (get m k) eqn:E; [|reflexivity].
  rewrite get_upd_same by (apply get_true_lt; exact E). ring.
Qed.

Theorem pauli_d : forall k psi s, ddag k (ddag k psi) s = 0.
Proof.
  intros k psi [m n]; unfold ddag; cbn [fst snd].
  destruct (get n k) eqn:E; [|reflexivity].
  rewrite get_upd_same by (apply get_true_lt; exact E). ring.
Qed.

Theorem cdag_anticomm : forall k j psi s, k <> j ->
  cdag k (cdag j psi) s = - cdag j (cdag k psi) s.
Proof.
  intros k j psi [m n] Hkj; unfold cdag; cbn [fst snd].
  rewrite (get_upd_other m k j false) by lia. rewrite (get_upd_other m j k false) by lia.
  destruct (get m k) eqn:Ek, (get m j) eqn:Ej; try ring.
  pose proof (get_true_lt m k Ek) as Hk. pose proof (get_true_lt m j Ej) as Hj.
  rewrite (upd_comm m k j false false) by lia.
  destruct (Nat.lt_ge_cases k j) as [Hlt|Hge].
  - pose proof (below_m_lt m n j k false Hlt Hk) as B. rewrite Ek in B. simpl b2n in B.
    rewrite (below_m_ge m n k j false) by lia.
    replace (below (m, n) j) with (S (below (upd m k false, n) j)) by lia.
    rewrite sgn_S. ring.
  - assert (Hlt : (j < k)%nat) by lia.
    pose proof (below_m_lt m n k j false Hlt Hj) as B. rewrite Ej in B. simpl b2n in B.
    rewrite (below_m_ge m n j k false) by lia.
    replace (below (m, n) k) with (S (below (upd m j false, n) k)) by lia.
    rewrite sgn_S. ring.
Qed.

Theorem c_cdag_anticomm : forall k j psi s, k <> j ->
  c k (cdag j psi) s = - cdag j (c k psi) s.
Proof.
  intros k j psi [m n] Hkj; unfold cdag, c; cbn [fst snd].
  rewrite (get_upd_other m k j true) by lia. rewrite (get_upd_other m j k false) by lia.
  destruct (get m k) eqn:Ek, (get m j) eqn:Ej; try ring.
  pose proof (get_true_lt m j Ej) as Hj.
  rewrite (upd_comm m k j true false) by lia.
  destruct (Nat.lt_ge_cases k j) as [Hlt|Hge].
  - pose proof (below_m_lt m n j k true Hlt ltac:(lia)) as B. rewrite Ek in B. simpl b2n in B.
    rewrite (below_m_ge m n k j false) by lia.
    replace (below (upd m k true, n) j) with (S (below (m, n) j)) by lia.
    rewrite sgn_S. ring.
  - assert (Hlt : (j < k)%nat) by lia.
    pose proof (below_m_lt m n k j false Hlt Hj) as B. rewrite Ej in B. simpl b2n in B.
    rewrite (below_m_ge m n j k true) by lia.
    replace (below (m, n) k) with (S (below (upd m j false, n) k)) by lia.
    rewrite sgn_S. ring.
Qed.

Theorem ddag_anticomm : forall k j psi s, k <> j ->
  ddag k (ddag j psi) s = - ddag j (ddag k psi) s.
Proof.
  intros k j psi [m n] Hkj; unfold ddag, dsg; cbn [fst snd].
  rewrite (get_upd_other n k j false) by lia. rewrite (get_upd_other n j k false) by lia.
  destruct (get n k) eqn:Ek, (get n j) eqn:Ej; try ring.
  pose proof (get_true_lt n k Ek) as Hk. pose proof (get_true_lt n j Ej) as Hj.
  rewrite (upd_comm n k j false false) by lia.
  destruct (Nat.lt_ge_cases k j) as [Hlt|Hge].
  - pose proof (below_n_lt m n j k false Hlt Hk) as B. rewrite Ek in B. simpl b2n in B.
    rewrite (below_n_ge m n k j false) by lia.
    replace (below (m, n) j) with (S (below (m, upd n k false) j)) by lia.
    rewrite Nat.add_succ_l, sgn_S. ring.
  - assert (Hlt : (j < k)%nat) by lia.
    pose proof (below_n_lt m n k j false Hlt Hj) as B. rewrite Ej in B. simpl b2n in B.
    rewrite (below_n_ge m n j k false) by lia.
    replace (below (m, n) k) with (S (below (m, upd n j false) k)) by lia.
    rewrite Nat.add_succ_l, sgn_S. ring.
Qed.

Theorem cdag_ddag_anticomm : forall k j psi s,
  cdag k (ddag j psi) s = - ddag j (cdag k psi) s.
Proof.
  intros k j psi [m n]; unfold cdag, ddag, dsg; cbn [fst snd].
  destruct (get m k) eqn:Ek, (get n j) eqn:Ej; try ring.
  pose proof (get_true_lt m k Ek) as Hk. pose proof (get_true_lt n j Ej) as Hj.
  destruct (Nat.lt_total k j) as [Hlt|[Heq|Hgt]].
  - pose proof (below_m_lt m n j k false Hlt Hk) as B. rewrite Ek in B. simpl b2n in B.
    rewrite (get_upd_other m k j false) by lia.
    rewrite (below_n_ge m n k j false) by lia.
    replace (below (m, n) j) with (S (below (upd m k false, n) j)) by lia.
    rewrite Nat.add_succ_l, sgn_S. ring.
  - subst j. rewrite get_upd_same by exact Hk. rewrite Ek.
    rewrite (below_m_ge m n k k false), (below_n_ge m n k k false) by lia.
    simpl b2n. rewrite Nat.add_0_r, Nat.add_1_r, sgn_S. ring.
  - pose proof (below_n_lt m n k j false Hgt Hj) as B. rewrite Ej in B. simpl b2n in B.
    rewrite (get_upd_other m k j false) by lia.
    rewrite (below_m_ge m n j k false) by lia.
    replace (below (m, n) k) with (S (below (m, upd n j false) k)) by lia.
    rewrite sgn_S. ring.
Qed.

(** A2: molecules are bosons *)
Definition Xdag (k : nat) (psi : Vec) : Vec := cdag k (ddag k psi).
Definition X (k : nat) (psi : Vec) : Vec := d k (c k psi).

Lemma Xdag_apply : forall k psi s, Xdag k psi s =
  if get (fst s) k then (if get (snd s) k then psi (upd (fst s) k false, upd (snd s) k false) else 0)
  else 0.
Proof.
  intros k psi [m n]. unfold Xdag, cdag, ddag, dsg; cbn [fst snd].
  destruct (get m k) eqn:Em; [|reflexivity].
  destruct (get n k) eqn:En; [|ring].
  rewrite get_upd_same by (apply get_true_lt; exact Em).
  rewrite below_m_ge by lia. simpl b2n. rewrite Nat.add_0_r, Z.mul_assoc, sgn_sq. ring.
Qed.

Lemma X_apply : forall k psi s, X k psi s =
  if get (snd s) k then 0
  else (if get (fst s) k then 0 else psi (upd (fst s) k true, upd (snd s) k true)).
Proof.
  intros k psi [m n]. unfold X, c, d, dsg; cbn [fst snd].
  destruct (get n k) eqn:En; [reflexivity|].
  destruct (get m k) eqn:Em; [ring|].
  rewrite below_n_ge by lia. simpl b2n. rewrite Nat.add_0_r, Z.mul_assoc, sgn_sq. ring.
Qed.

(** MOLECULES ARE BOSONS: molecule creation operators commute. *)
Theorem molecules_commute : forall k j psi s, Xdag k (Xdag j psi) s = Xdag j (Xdag k psi) s.
Proof.
  intros k j psi [m n].
  destruct (Nat.eq_dec k j) as [->|Hkj]; [reflexivity|].
  rewrite !Xdag_apply; cbn [fst snd].
  rewrite (get_upd_other m k j), (get_upd_other n k j), (get_upd_other m j k), (get_upd_other n j k) by lia.
  destruct (get m k), (get n k), (get m j), (get n j); try reflexivity.
  rewrite (upd_comm m k j), (upd_comm n k j) by lia. reflexivity.
Qed.

Theorem molecule_pauli : forall k psi s, Xdag k (Xdag k psi) s = 0.
Proof.
  intros k psi [m n]. rewrite !Xdag_apply; cbn [fst snd].
  destruct (get m k) eqn:Em; [|reflexivity]. destruct (get n k); [|reflexivity].
  rewrite get_upd_same by (apply get_true_lt; exact Em). reflexivity.
Qed.

Theorem molecule_hardcore : forall k psi s,
  (k < length (fst s))%nat -> (k < length (snd s))%nat ->
  X k (Xdag k psi) s - Xdag k (X k psi) s = (1 - b2z (get (fst s) k) - b2z (get (snd s) k)) * psi s.
Proof.
  intros k psi [m n] Hm Hn; simpl in Hm, Hn.
  rewrite (X_apply k (Xdag k psi)), (Xdag_apply k (X k psi)); cbn [fst snd].
  destruct (get m k) eqn:Em, (get n k) eqn:En; unfold b2z.
  - rewrite X_apply; cbn [fst snd]. rewrite !get_upd_same by assumption.
    rewrite !upd_upd, !upd_eq by assumption. ring.
  - ring.
  - ring.
  - rewrite Xdag_apply; cbn [fst snd]. rewrite !get_upd_same by assumption.
    rewrite !upd_upd, !upd_eq by assumption. ring.
Qed.

Theorem molecule_cross : forall k j psi s, k <> j -> X k (Xdag j psi) s = Xdag j (X k psi) s.
Proof.
  intros k j psi [m n] Hkj. rewrite (X_apply k (Xdag j psi)), (Xdag_apply j (X k psi)); cbn [fst snd].
  destruct (get n k) eqn:Enk, (get m k) eqn:Emk, (get m j) eqn:Emj, (get n j) eqn:Enj;
    rewrite ?Xdag_apply, ?X_apply; cbn [fst snd];
    rewrite ?(get_upd_other m k j), ?(get_upd_other n k j), ?(get_upd_other m j k), ?(get_upd_other n j k) by lia;
    rewrite ?Enk, ?Emk, ?Emj, ?Enj; try reflexivity.
  rewrite (upd_comm m k j), (upd_comm n k j) by lia. reflexivity.
Qed.

Lemma below_mol : forall m n k j, get m k = true -> get n k = true ->
  sgn (below (upd m k false, upd n k false) j) = sgn (below (m, n) j).
Proof.
  intros m n k j Em En.
  pose proof (get_true_lt m k Em) as Hm. pose proof (get_true_lt n k En) as Hn.
  destruct (Nat.lt_ge_cases k j) as [Hlt|Hge].
  - pose proof (below_n_lt (upd m k false) n j k false Hlt Hn) as B1.
    pose proof (below_m_lt m n j k false Hlt Hm) as B2.
    rewrite En in B1. rewrite Em in B2. simpl b2n in B1, B2.
    replace (below (m, n) j) with (S (S (below (upd m k false, upd n k false) j))) by lia.
    apply eq_sym, sgn_SS.
  - rewrite (below_n_ge (upd m k false) n j k false Hge), (below_m_ge m n j k false Hge). reflexivity.
Qed.

Theorem molecule_atom_comm_c : forall k j psi s, j <> k ->
  cdag j (Xdag k psi) s = Xdag k (cdag j psi) s.
Proof.
  intros k j psi [m n] Hjk. unfold cdag at 1; rewrite Xdag_apply; cbn [fst snd].
  destruct (get m j) eqn:Emj, (get m k) eqn:Emk, (get n k) eqn:Enk;
    rewrite ?Xdag_apply; unfold cdag; cbn [fst snd];
    rewrite ?(get_upd_other m j k), ?(get_upd_other m k j), ?(get_upd_other n k j) by lia;
    rewrite ?Emj, ?Emk, ?Enk; try ring.
  rewrite below_mol by assumption. rewrite (upd_comm m j k) by lia. reflexivity.
Qed.

Theorem molecule_atom_comm_d : forall k j psi s, j <> k ->
  ddag j (Xdag k psi) s = Xdag k (ddag j psi) s.
Proof.
  intros k j psi [m n] Hjk. unfold ddag at 1; rewrite Xdag_apply; unfold dsg; cbn [fst snd].
  destruct (get n j) eqn:Enj, (get m k) eqn:Emk, (get n k) eqn:Enk;
    rewrite ?Xdag_apply; unfold ddag, dsg; cbn [fst snd];
    rewrite ?(get_upd_other n j k), ?(get_upd_other m k j), ?(get_upd_other n k j) by lia;
    rewrite ?Enj, ?Emk, ?Enk; try ring.
  assert (E : sgn (below (upd m k false, upd n k false) j + b2n (get m j))
            = sgn (below (m, n) j + b2n (get m j))).
  { pose proof (below_mol m n k j Emk Enk) as B. unfold sgn in *.
    rewrite !Nat.even_add. destruct (Nat.even (below (upd m k false, upd n k false) j)),
      (Nat.even (below (m, n) j)); try discriminate; reflexivity. }
  rewrite E, (upd_comm n j k) by lia. reflexivity.
Qed.

(** Finite sums over the mode list [seq 0 K]. *)
Definition sumZ (f : nat -> Z) (l : list nat) : Z := fold_right (fun k acc => f k + acc) 0 l.
Lemma sumZ_cons : forall f a l, sumZ f (a :: l) = f a + sumZ f l.
Proof. reflexivity. Qed.

Lemma sumZ_ext : forall f g l, (forall k, In k l -> f k = g k) -> sumZ f l = sumZ g l.
Proof.
  intros f g l; induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite !sumZ_cons, H by (left; reflexivity).
  rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma sumZ_mul_r : forall f x l, sumZ (fun k => f k * x) l = sumZ f l * x.
Proof. intros f x l; induction l as [|a l IH]; [reflexivity|]. rewrite !sumZ_cons, IH. ring. Qed.

Lemma sumZ_opp : forall f l, sumZ (fun k => - f k) l = - sumZ f l.
Proof. intros f l; induction l as [|a l IH]; [reflexivity|]. rewrite !sumZ_cons, IH. ring. Qed.

Lemma sumZ_zero : forall f l, (forall k, In k l -> f k = 0) -> sumZ f l = 0.
Proof.
  intros f l; induction l as [|a l IH]; intros H; [reflexivity|].
  rewrite sumZ_cons, H by (left; reflexivity).
  rewrite IH by (intros; apply H; right; assumption). reflexivity.
Qed.

Lemma sumZ_scale_2 : forall f l, sumZ (fun k => 2 * f k) l = 2 * sumZ f l.
Proof. intros f l; induction l as [|a l IH]; [reflexivity|]. rewrite !sumZ_cons, IH. ring. Qed.

Lemma sumZ_point : forall f g l k, NoDup l -> In k l -> (forall j, j <> k -> f j = g j) ->
  sumZ f l = sumZ g l + (f k - g k).
Proof.
  intros f g l k ND; induction ND as [|a l Ha ND IH]; intros Hin Hfg; [destruct Hin|].
  rewrite !sumZ_cons. destruct (Nat.eq_dec a k) as [->|Hak].
  - rewrite (sumZ_ext f g l) by (intros j Hj; apply Hfg; intros ->; contradiction). ring.
  - destruct Hin as [->|Hin]; [contradiction|].
    rewrite (Hfg a Hak), IH by assumption. ring.
Qed.

(** A3: the Wheeler-DeWitt operator *)
Definition H (eps : nat -> Z) (K : nat) (psi : Vec) : Vec := fun s =>
  sumZ (fun k => eps k * (cdag k (c k psi) s - ddag k (d k psi) s)) (seq 0 K).

Definition energy (eps : nat -> Z) (K : nat) (s : Config) : Z :=
  sumZ (fun k => eps k * (b2z (get (fst s) k) - b2z (get (snd s) k))) (seq 0 K).

Theorem H_diag : forall eps K psi s, H eps K psi s = energy eps K s * psi s.
Proof.
  intros. unfold H, energy. rewrite <- sumZ_mul_r. apply sumZ_ext; intros k _.
  rewrite number_c, number_d. ring.
Qed.

Definition mirror (psi : Vec) : Vec := fun s => psi (snd s, fst s).

Lemma energy_mirror : forall eps K s, energy eps K (snd s, fst s) = - energy eps K s.
Proof.
  intros. unfold energy. rewrite <- sumZ_opp. apply sumZ_ext; intros k _. cbn [fst snd]. ring.
Qed.

Theorem H_mirror : forall eps K psi s, H eps K (mirror psi) s = - mirror (H eps K psi) s.
Proof.
  intros eps K psi [m n]. rewrite H_diag. unfold mirror; cbn [fst snd].
  rewrite H_diag. pose proof (energy_mirror eps K (m, n)) as E; simpl in E. rewrite E. ring.
Qed.

Lemma energy_clear_both : forall eps K m n k, get m k = true -> get n k = true ->
  energy eps K (upd m k false, upd n k false) = energy eps K (m, n).
Proof.
  intros eps K m n k Hm Hn. unfold energy. apply sumZ_ext; intros j _. cbn [fst snd]. f_equal.
  destruct (Nat.eq_dec j k) as [->|Hjk].
  - rewrite !get_upd_same by (apply get_true_lt; assumption). rewrite Hm, Hn. reflexivity.
  - rewrite !get_upd_other by exact Hjk. reflexivity.
Qed.

Theorem H_Xdag_comm : forall eps K k psi s, H eps K (Xdag k psi) s = Xdag k (H eps K psi) s.
Proof.
  intros eps K k psi [m n]. rewrite H_diag, !Xdag_apply; cbn [fst snd].
  destruct (get m k) eqn:E1; [|ring].
  destruct (get n k) eqn:E2; [|ring].
  rewrite H_diag, energy_clear_both by assumption. reflexivity.
Qed.

(** A4: vacuum, molecular states, condensates *)
Definition vac (K : nat) : Vec := fun s =>
  if list_eq_dec bool_dec (fst s) (repeat false K) then
    if list_eq_dec bool_dec (snd s) (repeat false K) then 1 else 0
  else 0.

Theorem H_vac : forall eps K s, H eps K (vac K) s = 0.
Proof.
  intros eps K [m n]. rewrite H_diag. unfold vac; cbn [fst snd].
  destruct (list_eq_dec bool_dec m (repeat false K)) as [Em|]; [|ring].
  destruct (list_eq_dec bool_dec n (repeat false K)) as [En|]; [|ring].
  subst. replace (energy eps K (repeat false K, repeat false K)) with 0; [ring|].
  symmetry. unfold energy. apply sumZ_zero; intros k _. cbn [fst snd]. rewrite get_repeat_false. ring.
Qed.

Definition molecules (ks : list nat) (psi : Vec) : Vec := fold_right Xdag psi ks.

(** MAIN THEOREM: every multi-molecule state solves the Wheeler-DeWitt equation. *)
Theorem wdw_molecular_solution : forall eps K ks s, H eps K (molecules ks (vac K)) s = 0.
Proof.
  intros eps K ks; induction ks as [|k ks IH]; intros s; simpl.
  - apply H_vac.
  - rewrite H_Xdag_comm, Xdag_apply.
    destruct (get (fst s) k); [|reflexivity].
    destruct (get (snd s) k); [|reflexivity]. apply IH.
Qed.

Definition occ (K : nat) (ks : list nat) : list bool :=
  fold_right (fun k l => upd l k true) (repeat false K) ks.

Lemma length_occ : forall K ks, length (occ K ks) = K.
Proof.
  intros K ks; induction ks as [|k ks IH]; simpl.
  - apply repeat_length.
  - rewrite length_upd. exact IH.
Qed.

Fixpoint fresh (K : nat) (ks : list nat) : Prop :=
  match ks with
  | [] => True
  | k :: t => (k < K)%nat /\ get (occ K t) k = false /\ fresh K t
  end.

Theorem molecules_at_occ : forall K ks, fresh K ks ->
  molecules ks (vac K) (occ K ks, occ K ks) = 1.
Proof.
  intros K ks; induction ks as [|k ks IH]; intros Hf; simpl.
  - unfold vac; cbn [fst snd].
    destruct (list_eq_dec bool_dec (repeat false K) (repeat false K)); [|congruence]. reflexivity.
  - destruct Hf as [Hk [Hocc Hf]].
    assert (Hk' : (k < length (occ K ks))%nat) by (rewrite length_occ; exact Hk).
    rewrite Xdag_apply; cbn [fst snd]. rewrite get_upd_same by exact Hk'.
    rewrite upd_upd, upd_eq by exact Hocc. apply IH, Hf.
Qed.

Theorem molecules_support : forall K ks s, molecules ks (vac K) s <> 0 -> s = (occ K ks, occ K ks).
Proof.
  intros K ks; induction ks as [|k ks IH]; intros [m n] Hs; cbn [molecules fold_right occ] in *.
  - unfold vac in Hs; cbn [fst snd] in Hs.
    destruct (list_eq_dec bool_dec m (repeat false K)) as [->|]; [|congruence].
    destruct (list_eq_dec bool_dec n (repeat false K)) as [->|]; [|congruence]. reflexivity.
  - rewrite Xdag_apply in Hs; cbn [fst snd] in Hs.
    destruct (get m k) eqn:E1; [|congruence].
    destruct (get n k) eqn:E2; [|congruence].
    apply IH in Hs. injection Hs as Hm Hn.
    rewrite <- (upd_eq m k true E1), <- (upd_eq n k true E2).
    rewrite <- (upd_upd m k false true), <- (upd_upd n k false true), Hm, Hn. reflexivity.
Qed.

Theorem distinct_solutions : forall K ks ks', occ K ks <> occ K ks' ->
  molecules ks (vac K) (occ K ks', occ K ks') = 0.
Proof.
  intros K ks ks' Hne.
  destruct (Z.eq_dec (molecules ks (vac K) (occ K ks', occ K ks')) 0) as [E|E]; [exact E|].
  exfalso. apply molecules_support in E. injection E as E1 _. congruence.
Qed.

Theorem molecules_repeat : forall k ks psi s, molecules (k :: k :: ks) psi s = 0.
Proof. intros. apply molecule_pauli. Qed.

Fixpoint bcs (u v : nat -> Z) (ks : list nat) (psi : Vec) : Vec :=
  match ks with
  | [] => psi
  | k :: t => fun s => u k * bcs u v t psi s + v k * Xdag k (bcs u v t psi) s
  end.

(** MOLECULAR CONDENSATES SOLVE THE CONSTRAINT. *)
Theorem bcs_solution : forall eps K u v ks s, H eps K (bcs u v ks (vac K)) s = 0.
Proof.
  intros eps K u v ks; induction ks as [|k ks IH]; intros s; simpl.
  - apply H_vac.
  - rewrite H_diag.
    assert (h1 : energy eps K s * bcs u v ks (vac K) s = 0) by (rewrite <- H_diag; apply IH).
    assert (h2 : energy eps K s * Xdag k (bcs u v ks (vac K)) s = 0).
    { rewrite <- H_diag, H_Xdag_comm, Xdag_apply.
      destruct (get (fst s) k); [|reflexivity]. destruct (get (snd s) k); [|reflexivity]. apply IH. }
    transitivity (u k * (energy eps K s * bcs u v ks (vac K) s)
                  + v k * (energy eps K s * Xdag k (bcs u v ks (vac K)) s)); [ring|].
    rewrite h1, h2. ring.
Qed.

Lemma energy_pair : forall eps K m n k j, length m = K -> length n = K -> (k < K)%nat -> (j < K)%nat ->
  get m k = false -> get n j = false ->
  energy eps K (upd m k true, upd n j true) = energy eps K (m, n) + eps k - eps j.
Proof.
  intros eps K m n k j Lm Ln Hk Hj Em En.
  assert (S1 : energy eps K (upd m k true, n) = energy eps K (m, n) + eps k).
  { unfold energy; cbn [fst snd].
    rewrite (sumZ_point _ (fun i => eps i * (b2z (get m i) - b2z (get n i))) (seq 0 K) k).
    - rewrite get_upd_same by lia. rewrite Em. unfold b2z. ring.
    - apply seq_NoDup.
    - apply in_seq; lia.
    - intros i Hi. rewrite get_upd_other by exact Hi. reflexivity. }
  assert (S2 : energy eps K (upd m k true, upd n j true) = energy eps K (upd m k true, n) - eps j).
  { unfold energy; cbn [fst snd].
    rewrite (sumZ_point _ (fun i => eps i * (b2z (get (upd m k true) i) - b2z (get n i))) (seq 0 K) j).
    - rewrite (get_upd_same n j) by lia. rewrite En. unfold b2z. ring.
    - apply seq_NoDup.
    - apply in_seq; lia.
    - intros i Hi. rewrite (get_upd_other n j i) by exact Hi. reflexivity. }
  rewrite S2, S1. ring.
Qed.

(** PAIR (MOLECULAR-FIELD) SHIFT: [H, d_j c_k] = (eps_j - eps_k) d_j c_k. *)
Theorem pair_shift : forall eps K k j psi s,
  length (fst s) = K -> length (snd s) = K -> (k < K)%nat -> (j < K)%nat ->
  H eps K (d j (c k psi)) s - d j (c k (H eps K psi)) s = (eps j - eps k) * d j (c k psi) s.
Proof.
  intros eps K k j psi [m n] Lm Ln Hk Hj; cbn [fst snd] in Lm, Ln.
  rewrite H_diag. unfold d, c; cbn [fst snd].
  destruct (get n j) eqn:En; [ring|].
  destruct (get m k) eqn:Em; [ring|].
  rewrite H_diag, energy_pair by assumption. ring.
Qed.

(** A5: balanced form, zero point, no-go, scale, Stelle sign, rational independence *)
Theorem balance_iff : forall (Hop T V : Vec -> Vec) psi,
  (forall phi s, Hop phi s = T phi s + V phi s) ->
  ((forall s, Hop psi s = 0) <-> (forall s, T psi s = - V psi s)).
Proof. intros Hop T V psi Hs; split; intros Hz s; specialize (Hz s); rewrite Hs in *; lia. Qed.

Definition H_weyl2 (eps : nat -> Z) (K : nat) (psi : Vec) : Vec := fun s =>
  sumZ (fun k => eps k * ((cdag k (c k psi) s - c k (cdag k psi) s)
                        - (ddag k (d k psi) s - d k (ddag k psi) s))) (seq 0 K).

Theorem zero_point_cancellation : forall eps K psi s,
  length (fst s) = K -> length (snd s) = K -> H_weyl2 eps K psi s = 2 * H eps K psi s.
Proof.
  intros eps K psi s L1 L2. unfold H_weyl2, H. rewrite <- sumZ_scale_2. apply sumZ_ext; intros k Hk.
  apply in_seq in Hk.
  rewrite anti_number_c, anti_number_d, number_c, number_d by lia. ring.
Qed.

Theorem no_go : forall t v : Z, 0 <= t -> 0 <= v -> t + v = 0 -> t = 0 /\ v = 0.
Proof. lia. Qed.

Theorem kernel_scale : forall (Hop : Vec -> Vec) (lam : Z) psi, lam <> 0 ->
  ((forall s, lam * Hop psi s = 0) <-> (forall s, Hop psi s = 0)).
Proof.
  intros Hop lam psi Hl; split; intros Hz s; specialize (Hz s).
  - apply Z.mul_eq_0 in Hz. destruct Hz; [contradiction|assumption].
  - rewrite Hz. ring.
Qed.

Theorem stelle_channel_tachyon : forall cS : Z, ~ (3 * (- cS) + 4 * cS > 0 /\ 4 * cS < 0).
Proof. lia. Qed.

Definition rat_indep (eps : nat -> Z) (K : nat) : Prop :=
  forall cf : nat -> Z, sumZ (fun k => cf k * eps k) (seq 0 K) = 0 -> forall k, (k < K)%nat -> cf k = 0.

Theorem kernel_molecular : forall eps K s, rat_indep eps K -> energy eps K s = 0 ->
  forall k, (k < K)%nat -> get (fst s) k = get (snd s) k.
Proof.
  intros eps K s RI E k Hk.
  pose proof (RI (fun j => b2z (get (fst s) j) - b2z (get (snd s) j))) as R.
  assert (Hsum : sumZ (fun j => (b2z (get (fst s) j) - b2z (get (snd s) j)) * eps j) (seq 0 K) = 0).
  { rewrite <- E. unfold energy. apply sumZ_ext; intros; ring. }
  specialize (R Hsum k Hk). cbn beta in R. unfold b2z in R.
  destruct (get (fst s) k), (get (snd s) k); try reflexivity; lia.
Qed.

End FockSpace.

(* ===================================================================== *)
(** * Part B. Spinor kinematics over an arbitrary commutative ring        *)
(* ===================================================================== *)

Module SpinorIdentities.
Section Generic.
Variable R : Type.
Variables (rO rI : R) (radd rmul rsub : R -> R -> R) (ropp : R -> R).
Hypothesis Rth : ring_theory rO rI radd rmul rsub ropp (@eq R).
Add Ring GenericRing : Rth.

Declare Scope cr_scope.
Delimit Scope cr_scope with cr.
Local Infix "+" := radd : cr_scope.
Local Infix "*" := rmul : cr_scope.
Local Infix "-" := rsub : cr_scope.
Local Notation "- x" := (ropp x) : cr_scope.
Local Notation "0" := rO : cr_scope.
Local Notation "1" := rI : cr_scope.
Local Open Scope cr_scope.

(** Complex numbers over R *)
Record cx := mkC { re : R; im : R }.
Definition cadd (a b : cx) := mkC (re a + re b) (im a + im b).
Definition csub (a b : cx) := mkC (re a - re b) (im a - im b).
Definition cneg (a : cx) := mkC (- re a) (- im a).
Definition cmul (a b : cx) := mkC (re a * re b - im a * im b) (re a * im b + im a * re b).
Definition cconj (a : cx) := mkC (re a) (- im a).
Definition c0 := mkC 0 0.
Definition c1 := mkC 1 0.
Definition ci := mkC 0 1.
Definition creal (x : R) := mkC x 0.

Lemma cx_eq : forall a b, re a = re b -> im a = im b -> a = b.
Proof. intros [a1 a2] [b1 b2]; simpl; intros -> ->; reflexivity. Qed.

(** Two-component spinor index and the antisymmetric pairing eps_01 = +1 *)
Inductive I2 := i0 | i1.
Definition epsC (A B : I2) : cx :=
  match A, B with i0, i1 => c1 | i1, i0 => cneg c1 | _, _ => c0 end.
Definition sum2 (f : I2 -> cx) : cx := cadd (f i0) (f i1).

(** B1: [eq:etaeps].  X~^{AA'} = X^0 1 + X^i sigma_i (unnormalized soldering). *)
Definition Xt (x0 x1 x2 x3 : R) (A A' : I2) : cx :=
  match A, A' with
  | i0, i0 => creal (x0 + x3) | i0, i1 => mkC x1 (- x2)
  | i1, i0 => mkC x1 x2       | i1, i1 => creal (x0 - x3)
  end.
Definition etaR (x0 x1 x2 x3 y0 y1 y2 y3 : R) : R := - (x0 * y0) + x1 * y1 + x2 * y2 + x3 * y3.

Theorem eta_from_pairing : forall x0 x1 x2 x3 y0 y1 y2 y3,
  cneg (sum2 (fun A => sum2 (fun B => sum2 (fun A' => sum2 (fun B' =>
     cmul (cmul (epsC A B) (epsC A' B')) (cmul (Xt x0 x1 x2 x3 A A') (Xt y0 y1 y2 y3 B B')))))))
  = creal ((1 + 1) * etaR x0 x1 x2 x3 y0 y1 y2 y3).
Proof. intros; apply cx_eq; cbv; ring. Qed.

Theorem det_is_minus_eta : forall x0 x1 x2 x3,
  csub (cmul (Xt x0 x1 x2 x3 i0 i0) (Xt x0 x1 x2 x3 i1 i1)) (cmul (Xt x0 x1 x2 x3 i0 i1) (Xt x0 x1 x2 x3 i1 i0))
  = creal (- etaR x0 x1 x2 x3 x0 x1 x2 x3).
Proof. intros; apply cx_eq; cbv; ring. Qed.

(** B2: [prop:null], a single molecule xi xi^dagger has zero determinant (is null). *)
Theorem single_molecule_null : forall xi : I2 -> cx,
  csub (cmul (cmul (xi i0) (cconj (xi i0))) (cmul (xi i1) (cconj (xi i1))))
       (cmul (cmul (xi i0) (cconj (xi i1))) (cmul (xi i1) (cconj (xi i0)))) = c0.
Proof. intros; apply cx_eq; cbv; ring. Qed.

(** B3: dyad identity (App. A) and [prop:tetrad] in spinor form *)
Definition omega (psi phi : I2 -> cx) : cx :=
  sum2 (fun A => sum2 (fun B => cmul (epsC A B) (cmul (psi A) (phi B)))).

Theorem dyad_identity : forall (psi phi : I2 -> cx) (A B : I2),
  csub (cmul (psi A) (phi B)) (cmul (phi A) (psi B)) = cmul (omega psi phi) (epsC A B).
Proof. intros psi phi A B; destruct A, B; apply cx_eq; cbv; ring. Qed.

(** Atoms of two flavors: alpha = i0 is o, alpha = i1 is iota.  The molecule
    X_{alpha gamma}^{A A'} = atom_alpha^A * conj(atom_gamma^{A'}).  [prop:tetrad] states
    - eps^{alpha beta} eps^{gamma delta} X_{alpha gamma} X_{beta delta}
      = - |omega_12|^2 eps^{AB} eps^{A'B'},
    which by [eq:etaeps] is |omega_12|^2 eta^{ab}. *)
Definition atom (o io : I2 -> cx) (alpha : I2) : I2 -> cx := match alpha with i0 => o | i1 => io end.

Theorem tetrad_metric_spinor : forall (o io : I2 -> cx) (A A' B B' : I2),
  cneg (sum2 (fun al => sum2 (fun be => sum2 (fun ga => sum2 (fun de =>
     cmul (cmul (epsC al be) (epsC ga de))
          (cmul (cmul (atom o io al A) (cconj (atom o io ga A')))
                (cmul (atom o io be B) (cconj (atom o io de B')))))))))
  = cneg (cmul (cmul (omega o io) (cconj (omega o io))) (cmul (epsC A B) (epsC A' B'))).
Proof. intros o io A A' B B'; destruct A, A', B, B'; apply cx_eq; cbv; ring. Qed.

(** B4: [eq:chiral_trace] times 16.  S~ = 4 S(theta) = -2 theta_{0i} sigma_i + i eps_{ijk} theta_{ij} sigma_k. *)
Inductive I4 := e0 | e1 | e2 | e3.
Definition sum4 (f : I4 -> cx) : cx := cadd (cadd (f e0) (f e1)) (cadd (f e2) (f e3)).

(* antisymmetric theta_{ab} from six independent components *)
Definition theta (t01 t02 t03 t12 t13 t23 : R) (a b : I4) : R :=
  match a, b with
  | e0, e1 => t01 | e0, e2 => t02 | e0, e3 => t03 | e1, e2 => t12 | e1, e3 => t13 | e2, e3 => t23
  | e1, e0 => - t01 | e2, e0 => - t02 | e3, e0 => - t03 | e2, e1 => - t12 | e3, e1 => - t13 | e3, e2 => - t23
  | _, _ => 0
  end.
Definition etaD (a : I4) : R := match a with e0 => - (1) | _ => 1 end.
(* Levi-Civita symbols eps_{0123} = +1 and eps_{123} = +1 (spatial indices e1 e2 e3) *)
Definition lc3 (i j k : I4) : R :=
  match i, j, k with
  | e1, e2, e3 => 1 | e2, e3, e1 => 1 | e3, e1, e2 => 1
  | e1, e3, e2 => - (1) | e3, e2, e1 => - (1) | e2, e1, e3 => - (1)
  | _, _, _ => 0
  end.
(** We define eps_{abcd} directly by its value on all 24 permutations of (0,1,2,3). *)
Definition lc4 (a b c d : I4) : R :=
  match a, b, c, d with
  | e0,e1,e2,e3 => 1 | e0,e1,e3,e2 => - (1) | e0,e2,e1,e3 => - (1) | e0,e2,e3,e1 => 1 | e0,e3,e1,e2 => 1 | e0,e3,e2,e1 => - (1)
  | e1,e0,e2,e3 => - (1) | e1,e0,e3,e2 => 1 | e1,e2,e0,e3 => 1 | e1,e2,e3,e0 => - (1) | e1,e3,e0,e2 => - (1) | e1,e3,e2,e0 => 1
  | e2,e0,e1,e3 => 1 | e2,e0,e3,e1 => - (1) | e2,e1,e0,e3 => - (1) | e2,e1,e3,e0 => 1 | e2,e3,e0,e1 => 1 | e2,e3,e1,e0 => - (1)
  | e3,e0,e1,e2 => - (1) | e3,e0,e2,e1 => 1 | e3,e1,e0,e2 => 1 | e3,e1,e2,e0 => - (1) | e3,e2,e0,e1 => - (1) | e3,e2,e1,e0 => 1
  | _,_,_,_ => 0
  end.

(* 2 x 2 complex matrices *)
Definition M2 := I2 -> I2 -> cx.
Definition madd (P Q : M2) : M2 := fun A B => cadd (P A B) (Q A B).
Definition mmul (P Q : M2) : M2 := fun A B => sum2 (fun C => cmul (P A C) (Q C B)).
Definition mscal (z : cx) (P : M2) : M2 := fun A B => cmul z (P A B).
Definition mzero : M2 := fun _ _ => c0.
Definition tr2 (P : M2) : cx := cadd (P i0 i0) (P i1 i1).
Definition sigma (k : I4) : M2 := fun A B =>
  match k, A, B with
  | e1, i0, i1 => c1 | e1, i1, i0 => c1
  | e2, i0, i1 => cneg ci | e2, i1, i0 => ci
  | e3, i0, i0 => c1 | e3, i1, i1 => cneg c1
  | e0, i0, i0 => c1 | e0, i1, i1 => c1
  | _, _, _ => c0
  end.
Definition sumM (f : I4 -> M2) : M2 := fun A B => sum4 (fun k => f k A B).
Definition spatial (k : I4) : bool := match k with e0 => false | _ => true end.

Definition St (t01 t02 t03 t12 t13 t23 : R) : M2 :=
  madd (sumM (fun i => if spatial i then mscal (creal (- (1 + 1) * theta t01 t02 t03 t12 t13 t23 e0 i)) (sigma i) else mzero))
       (sumM (fun k => if spatial k then
          mscal (cmul ci (sum4 (fun i => sum4 (fun j => creal (lc3 i j k * theta t01 t02 t03 t12 t13 t23 i j))))) (sigma k)
        else mzero)).

Definition up (th : I4 -> I4 -> R) (a b : I4) : R := etaD a * etaD b * th a b.

Theorem chiral_trace_times16 : forall t01 t02 t03 t12 t13 t23 u01 u02 u03 u12 u13 u23,
  let th := theta t01 t02 t03 t12 t13 t23 in let th' := theta u01 u02 u03 u12 u13 u23 in
  tr2 (mmul (St t01 t02 t03 t12 t13 t23) (St u01 u02 u03 u12 u13 u23))
  = cadd (creal (- (1 + 1 + 1 + 1) * re (sum4 (fun a => sum4 (fun b => creal (th a b * up th' a b))))))
         (cmul (creal (1 + 1)) (cmul ci (sum4 (fun a => sum4 (fun b => sum4 (fun c => sum4 (fun d =>
            creal (lc4 a b c d * up th a b * up th' c d)))))))).
Proof. intros; apply cx_eq; cbv; ring. Qed.

(** [prop:kramers]: for U = [[a, b], [-conj b, conj a]] (the SU(2) form), sigma_y conj(U) sigma_y = U.
    This is the identity behind the Kramers degeneracy and the mirror isospectrality hbar = Theta^-1 h Theta. *)
Definition su2m (a b : cx) (A B : I2) : cx :=
  match A, B with i0, i0 => a | i0, i1 => b | i1, i0 => cneg (cconj b) | i1, i1 => cconj a end.

Theorem su2_pseudoreal : forall (a b : cx) (A B : I2),
  sum2 (fun C => sum2 (fun D => cmul (cmul (sigma e2 A C) (cconj (su2m a b C D))) (sigma e2 D B))) = su2m a b A B.
Proof. intros a b A B; destruct A, B; apply cx_eq; cbv; ring. Qed.

End Generic.
End SpinorIdentities.

(* ===================================================================== *)
(** * Part C. Boundary conformal algebra by exact computation [prop:conformal] *)
(* ===================================================================== *)

Module Conformal.
Open Scope Z_scope.

(* Gaussian integers *)
Record gi := G { gre : Z; gim : Z }.
Definition gadd a b := G (gre a + gre b) (gim a + gim b).
Definition gsub a b := G (gre a - gre b) (gim a - gim b).
Definition gmul a b := G (gre a * gre b - gim a * gim b) (gre a * gim b + gim a * gre b).
Definition gscale (z : Z) a := G (z * gre a) (z * gim a).
Definition gconj a := G (gre a) (- gim a).
Definition gz := G 0 0.  Definition g1 := G 1 0.  Definition gi1 := G 0 1.
Definition geqb a b := Z.eqb (gre a) (gre b) && Z.eqb (gim a) (gim b).

Inductive I4 := e0 | e1 | e2 | e3.
Definition idx := [e0; e1; e2; e3].
Definition M := I4 -> I4 -> gi.
Definition msum (f : I4 -> gi) : gi := fold_right (fun k acc => gadd (f k) acc) gz idx.
Definition mmul (A B : M) : M := fun i j => msum (fun k => gmul (A i k) (B k j)).
Definition madd (A B : M) : M := fun i j => gadd (A i j) (B i j).
Definition msub (A B : M) : M := fun i j => gsub (A i j) (B i j).
Definition mscale (z : Z) (A : M) : M := fun i j => gscale z (A i j).
Definition comm (A B : M) : M := msub (mmul A B) (mmul B A).
Definition mzero : M := fun _ _ => gz.
Definition mid : M := fun i j => match i, j with e0,e0 | e1,e1 | e2,e2 | e3,e3 => g1 | _,_ => gz end.
Definition meqb (A B : M) : bool := forallb (fun i => forallb (fun j => geqb (A i j) (B i j)) idx) idx.
Definition adj (A : M) : M := fun i j => gconj (A j i).

Lemma geqb_eq : forall a b, geqb a b = true -> a = b.
Proof.
  intros [a1 a2] [b1 b2]; unfold geqb; simpl; intros Hb.
  apply andb_true_iff in Hb as [H1 H2]. apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst; reflexivity.
Qed.

Lemma meqb_sound : forall A B, meqb A B = true -> forall i j, A i j = B i j.
Proof.
  intros A B Hb i j; unfold meqb in Hb. rewrite forallb_forall in Hb.
  assert (Hi : In i idx) by (destruct i; simpl; tauto). specialize (Hb i Hi).
  rewrite forallb_forall in Hb. assert (Hj : In j idx) by (destruct j; simpl; tauto).
  apply geqb_eq, Hb, Hj.
Qed.

(* Weyl-basis gamma matrices gamma^a = [[0, sigma^a], [sigmabar^a, 0]], sigma = (1, s), sigmabar = (-1, s);
   rows/columns 0,1 = upper block (dual of right atoms), 2,3 = lower block (left atoms). *)
Definition sig (a : I4) (r c : nat) : gi :=
  match a, r, c with
  | e0, 0%nat, 0%nat => g1 | e0, 1%nat, 1%nat => g1
  | e1, 0%nat, 1%nat => g1 | e1, 1%nat, 0%nat => g1
  | e2, 0%nat, 1%nat => G 0 (-1) | e2, 1%nat, 0%nat => gi1
  | e3, 0%nat, 0%nat => g1 | e3, 1%nat, 1%nat => G (-1) 0
  | _, _, _ => gz end.
Definition sigbar (a : I4) (r c : nat) : gi := match a with e0 => gscale (-1) (sig e0 r c) | _ => sig a r c end.
Definition blk (i : I4) : nat := match i with e0 | e1 => 0%nat | e2 | e3 => 1%nat end.
Definition sub (i : I4) : nat := match i with e0 | e2 => 0%nat | e1 | e3 => 1%nat end.
Definition gam (a : I4) : M := fun i j =>
  match blk i, blk j with
  | 0%nat, 1%nat => sig a (sub i) (sub j)
  | 1%nat, 0%nat => sigbar a (sub i) (sub j)
  | _, _ => gz end.
Definition g5 : M := fun i j => match i, j with e0,e0 | e1,e1 => g1 | e2,e2 | e3,e3 => G (-1) 0 | _,_ => gz end.
Definition etaZ (a : I4) : Z := match a with e0 => -1 | _ => 1 end.
Definition gamlow (a : I4) : M := mscale (etaZ a) (gam a).

(* Generators multiplied by 2: Jt_ab = 2 J_ab = gamma^a gamma^b (a <> b), Pt_a = 2 P_a = gamma_a gamma_5 *)
Definition Jt (a b : I4) : M := mmul (gam a) (gam b).
Definition Pt (a : I4) : M := mmul (gamlow a) g5.
Definition Dt : M := Pt e0.
Definition Pc (i : I4) : M := madd (Jt e0 i) (Pt i).
Definition Kc (i : I4) : M := msub (Jt e0 i) (Pt i).
Definition delta (i j : I4) : Z := match i, j with e1,e1 | e2,e2 | e3,e3 => 1 | _,_ => 0 end.
Definition Mt (i j : I4) : M := match i, j with e1,e1 | e2,e2 | e3,e3 => mzero | _,_ => Jt i j end.
Definition spat := [e1; e2; e3].

(* Clifford algebra {gamma^a, gamma^b} = 2 eta^{ab} 1 *)
Definition clifford_ok : bool :=
  forallb (fun a => forallb (fun b =>
    meqb (madd (mmul (gam a) (gam b)) (mmul (gam b) (gam a)))
         (mscale (match a, b with e0,e0 => -2 | e1,e1 | e2,e2 | e3,e3 => 2 | _,_ => 0 end) mid)) idx) idx.

(* [prop:conformal], scaled: [Dt,Pc_i] = 2 Pc_i, [Dt,Kc_i] = -2 Kc_i, [Kc_i,Pc_j] = 4 (Mt_ij - delta_ij Dt),
   [Dt,Mt_ij] = 0, [Pc_i,Pc_j] = [Kc_i,Kc_j] = 0, [Mt_ij, X_k] = 2 (delta_jk X_i - delta_ik X_j) *)
Definition conformal_ok : bool :=
  forallb (fun i =>
    meqb (comm Dt (Pc i)) (mscale 2 (Pc i)) && meqb (comm Dt (Kc i)) (mscale (-2) (Kc i)) &&
    forallb (fun j =>
      meqb (comm (Kc i) (Pc j)) (mscale 4 (msub (Mt i j) (mscale (delta i j) Dt))) &&
      meqb (comm Dt (Mt i j)) mzero && meqb (comm (Pc i) (Pc j)) mzero && meqb (comm (Kc i) (Kc j)) mzero &&
      forallb (fun k =>
        meqb (comm (Mt i j) (Pc k)) (mscale 2 (msub (mscale (delta j k) (Pc i)) (mscale (delta i k) (Pc j)))) &&
        meqb (comm (Mt i j) (Kc k)) (mscale 2 (msub (mscale (delta j k) (Kc i)) (mscale (delta i k) (Kc j))))) spat) spat) spat.

(* block structure: Mt block diagonal and anti-Hermitian; Dt Hermitian and off diagonal; Dt^2 = 1 (eigenvalues of D = Dt/2 are +-1/2) *)
Definition blockdiag (A : M) : bool := forallb (fun i => forallb (fun j =>
  if Nat.eqb (blk i) (blk j) then true else geqb (A i j) gz) idx) idx.
Definition offdiag (A : M) : bool := forallb (fun i => forallb (fun j =>
  if Nat.eqb (blk i) (blk j) then geqb (A i j) gz else true) idx) idx.
Definition structure_ok : bool :=
  forallb (fun i => forallb (fun j => blockdiag (Mt i j) && meqb (adj (Mt i j)) (mscale (-1) (Mt i j))) spat) spat
  && meqb (adj Dt) Dt && offdiag Dt && meqb (mmul Dt Dt) mid.

Theorem clifford_algebra : clifford_ok = true.  Proof. vm_compute. reflexivity. Qed.
Theorem boundary_conformal_algebra : conformal_ok = true.  Proof. vm_compute. reflexivity. Qed.
Theorem conformal_generator_structure : structure_ok = true.  Proof. vm_compute. reflexivity. Qed.

(* Unpacked form of one representative relation, to show what the boolean checks mean *)
Theorem dilatation_translation : forall i, In i spat -> forall r s, comm Dt (Pc i) r s = mscale 2 (Pc i) r s.
Proof.
  intros i Hi r s. apply meqb_sound.
  destruct Hi as [<-|[<-|[<-|[]]]]; vm_compute; reflexivity.
Qed.

End Conformal.

(* ===================================================================== *)
(** * Part D. Field identities over the real numbers                       *)
(* ===================================================================== *)

Module FieldIdentities.
Open Scope R_scope.

(* [eq:scalaron_mass]: for f = alpha R + beta R^2, m_f^2 = (f'/f'' - Rbar)/3 = alpha/(6 beta) *)
Theorem scalaron_mass : forall alpha beta Rb : R, beta <> 0 ->
  ((alpha + 2 * beta * Rb) / (2 * beta) - Rb) / 3 = alpha / (6 * beta).
Proof. intros; field; auto. Qed.

(* Farmer-Larson form f = R (1 - xi Phi^2) + beta R^2 *)
Theorem scalaron_mass_FL : forall xi Phi beta Rb : R, beta <> 0 ->
  (((1 - xi * Phi ^ 2) + 2 * beta * Rb) / (2 * beta) - Rb) / 3 = (1 - xi * Phi ^ 2) / (6 * beta).
Proof. intros; field; auto. Qed.

(* [eq:stelle_masses]: Ricci basis (a = -c, b = 4c; Stelle) and Weyl basis (beta_R = c/3, alpha_W = 2c) agree *)
Theorem stelle_masses : forall c : R, c <> 0 ->
  let a := - c in let b := 4 * c in let betaR := c / 3 in let alphaW := 2 * c in
  1 / (2 * (3 * a + b)) = 1 / (2 * c) /\ 1 / (6 * betaR) = 1 / (2 * c) /\
  - 1 / b = - 1 / (4 * c) /\ - 1 / (2 * alphaW) = - 1 / (4 * c).
Proof.
  intros c Hc a b betaR alphaW; subst a b betaR alphaW.
  repeat split; field; repeat split; auto; lra.
Qed.

Theorem stelle_no_stable_c : forall c : R, ~ (0 < 1 / (2 * c) /\ 0 < - 1 / (4 * c)).
Proof.
  intros c [H1 H2]. destruct (Rlt_or_le 0 c) as [Hc|Hc].
  - assert (0 < 1 / (4 * c)) by (apply Rdiv_lt_0_compat; lra).
    assert (- 1 / (4 * c) = - (1 / (4 * c))) by (field; lra). lra.
  - destruct (Req_dec c 0) as [->|Hc0].
    + replace (2 * 0) with 0 in H1 by ring. unfold Rdiv in H1. rewrite Rinv_0, Rmult_0_r in H1. lra.
    + assert (0 < 1 / (- (2 * c))) by (apply Rdiv_lt_0_compat; lra).
      assert (1 / (2 * c) = - (1 / (- (2 * c)))) by (field; lra). lra.
Qed.

(* [eq:entropy]: 3/(64 pi G Lambda) = S_dS/(64 pi^2), with S_dS = A/(4G) = pi l^2/G and l^2 = 3/Lambda *)
Theorem desitter_entropy : forall G Lam : R, G <> 0 -> Lam <> 0 ->
  let l2 := 3 / Lam in let SdS := 4 * PI * l2 / (4 * G) in
  3 / (64 * PI * G * Lam) = SdS / (64 * PI ^ 2) /\ SdS = 3 * PI / (G * Lam).
Proof.
  intros G Lam HG HL l2 SdS; subst l2 SdS. pose proof PI_RGT_0.
  split; field; repeat split; auto; lra.
Qed.

(* [sec:inflation]: Einstein-frame potential of f = R + R^2/(6 M^2).  With F = f'(R) = 1 + R/(3M^2),
   V = (Mp^2/2) (R F - f)/F^2 = (3/4) M^2 Mp^2 (1 - 1/F)^2. *)
Theorem starobinsky_potential : forall M Mp F : R, M <> 0 -> F <> 0 ->
  let Rc := 3 * M ^ 2 * (F - 1) in let f := Rc + Rc ^ 2 / (6 * M ^ 2) in
  F = 1 + Rc / (3 * M ^ 2) /\ Mp ^ 2 / 2 * (Rc * F - f) / F ^ 2 = 3 / 4 * M ^ 2 * Mp ^ 2 * (1 - 1 / F) ^ 2.
Proof. intros M Mp F HM HF Rc f; subst Rc f. split; field; auto. Qed.

(* [eq:R2coef]: the R^2 coefficient M_P^2/(12 M^2) equals N^2/(288 pi^2 A_s) when A_s = N^2 M^2/(24 pi^2 M_P^2) *)
Theorem R2_coefficient : forall N M Mp : R, N <> 0 -> M <> 0 -> Mp <> 0 ->
  let As := N ^ 2 * M ^ 2 / (24 * PI ^ 2 * Mp ^ 2) in Mp ^ 2 / (12 * M ^ 2) = N ^ 2 / (288 * PI ^ 2 * As).
Proof. intros N M Mp HN HM HP As; subst As. pose proof PI_RGT_0. field; repeat split; auto; lra. Qed.

End FieldIdentities.

(* ===================================================================== *)
(** * Audit                                                                *)
(* ===================================================================== *)
Print Assumptions FockSpace.car_c.
Print Assumptions FockSpace.car_d.
Print Assumptions FockSpace.pauli_c.
Print Assumptions FockSpace.cdag_anticomm.
Print Assumptions FockSpace.c_cdag_anticomm.
Print Assumptions FockSpace.ddag_anticomm.
Print Assumptions FockSpace.cdag_ddag_anticomm.
Print Assumptions FockSpace.molecules_commute.
Print Assumptions FockSpace.molecule_pauli.
Print Assumptions FockSpace.molecule_hardcore.
Print Assumptions FockSpace.molecule_cross.
Print Assumptions FockSpace.molecule_atom_comm_c.
Print Assumptions FockSpace.molecule_atom_comm_d.
Print Assumptions FockSpace.H_diag.
Print Assumptions FockSpace.H_mirror.
Print Assumptions FockSpace.H_Xdag_comm.
Print Assumptions FockSpace.wdw_molecular_solution.
Print Assumptions FockSpace.molecules_at_occ.
Print Assumptions FockSpace.molecules_support.
Print Assumptions FockSpace.distinct_solutions.
Print Assumptions FockSpace.molecules_repeat.
Print Assumptions FockSpace.bcs_solution.
Print Assumptions FockSpace.pair_shift.
Print Assumptions FockSpace.balance_iff.
Print Assumptions FockSpace.zero_point_cancellation.
Print Assumptions FockSpace.no_go.
Print Assumptions FockSpace.kernel_scale.
Print Assumptions FockSpace.stelle_channel_tachyon.
Print Assumptions FockSpace.kernel_molecular.
Print Assumptions SpinorIdentities.eta_from_pairing.
Print Assumptions SpinorIdentities.single_molecule_null.
Print Assumptions SpinorIdentities.tetrad_metric_spinor.
Print Assumptions SpinorIdentities.chiral_trace_times16.
Print Assumptions SpinorIdentities.su2_pseudoreal.
Print Assumptions Conformal.boundary_conformal_algebra.
Print Assumptions Conformal.clifford_algebra.
Print Assumptions Conformal.conformal_generator_structure.
Print Assumptions FieldIdentities.scalaron_mass.
Print Assumptions FieldIdentities.stelle_masses.
Print Assumptions FieldIdentities.stelle_no_stable_c.
Print Assumptions FieldIdentities.desitter_entropy.
Print Assumptions FieldIdentities.starobinsky_potential.
Print Assumptions FieldIdentities.R2_coefficient.
