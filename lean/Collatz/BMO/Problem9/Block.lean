/-
Copyright (c) 2026 Trevor Morris. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Trevor Morris
-/
import Mathlib.Tactic

/-!
# BMO #9, port of Rocq `Module Block` (BMO9.v lines 237-592, ccz181078)

Summary records for compositions of affine kernel calls, the integer three-call identity,
`|θ| ≤ 1/2`, and exact descent.  Pure integer algebra.
-/

namespace BMO9.Block

structure Kernel where
  den : ℤ
  num : ℤ
  bias : ℤ
  gain : ℤ
  deriving DecidableEq, Repr

def Kernel.Good (k : Kernel) : Prop :=
  0 < k.den ∧ 0 < k.num ∧ 2*k.num ≤ k.den ∧ 1 ≤ k.bias ∧ k.bias + 2 ≤ k.gain

def call (k : Kernel) (S H S' H' : ℤ) : Prop :=
  S' = S + k.gain ∧ k.den*H' = 2*k.den*S - k.num*H + k.den*(2*k.gain + 3 - k.bias)

structure Summary where
  scale : ℤ
  sc : ℤ
  hc : ℤ
  offset : ℤ
  added : ℤ
  deriving DecidableEq, Repr

def identity : Summary := ⟨1, 0, 1, 0, 0⟩

def push (k : Kernel) (z : Summary) : Summary :=
  ⟨k.den*z.scale, 2*k.den*z.scale - k.num*z.sc, -k.num*z.hc,
    k.den*z.scale*(2*z.added + 2*k.gain + 3 - k.bias) - k.num*z.offset, z.added + k.gain⟩

def denotes (z : Summary) (S H S' H' : ℤ) : Prop :=
  S' = S + z.added ∧ z.scale*H' = z.sc*S + z.hc*H + z.offset

def Summary.Bounded (z : Summary) : Prop :=
  0 < z.scale ∧ 0 ≤ z.sc ∧ z.sc ≤ 2*z.scale ∧ 0 ≤ z.added ∧ 0 ≤ z.offset ∧
    z.offset ≤ z.scale*(2*z.added + 2)

theorem identity_bounded : identity.Bounded := by
  simp [Summary.Bounded, identity]

theorem push_bounded (k : Kernel) (z : Summary) (hk : k.Good) (hz : z.Bounded) :
    (push k z).Bounded ∧ (push k z).scale ≤ (push k z).sc ∧ 0 < (push k z).offset := by
  obtain ⟨q, p, b, lam⟩ := k
  obtain ⟨Q, A, B, C, M⟩ := z
  simp only [Kernel.Good, Summary.Bounded, push] at *
  obtain ⟨Hq, Hp, Hqp, Hb, Hl⟩ := hk
  obtain ⟨HQ, HA0, HA, HM, HC0, HC⟩ := hz
  have HpA : p*A ≤ q*Q := by nlinarith
  have HpC : p*C ≤ q*Q*(M+1) := by nlinarith [mul_le_mul_of_nonneg_left HC Hp.le]
  have Hprod : 0 < q*Q := by positivity
  refine ⟨⟨by positivity, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem push_sound (k : Kernel) (z : Summary) (S H S1 H1 S2 H2 : ℤ)
    (h1 : denotes z S H S1 H1) (h2 : call k S1 H1 S2 H2) : denotes (push k z) S H S2 H2 := by
  obtain ⟨q, p, b, lam⟩ := k
  obtain ⟨Q, A, B, C, M⟩ := z
  simp only [denotes, call, push] at *
  obtain ⟨HS1, HH1⟩ := h1
  obtain ⟨HS2, HH2⟩ := h2
  subst HS1
  refine ⟨by linarith, ?_⟩
  have e1 := congrArg (fun x ↦ Q*x) HH2
  have e2 := congrArg (fun x ↦ p*x) HH1
  linear_combination e1 - e2

inductive Calls : List Kernel → ℤ → ℤ → ℤ → ℤ → Prop
  | nil (S H : ℤ) : Calls [] S H S H
  | cons {k ks S H S1 H1 S2 H2} : call k S H S1 H1 → Calls ks S1 H1 S2 H2 →
      Calls (k :: ks) S H S2 H2

def fold (ks : List Kernel) (z : Summary) : Summary := ks.foldl (fun z k ↦ push k z) z

theorem fold_sound {ks S H S' H'} (h : Calls ks S H S' H') :
    ∀ z S0 H0, denotes z S0 H0 S H → denotes (fold ks z) S0 H0 S' H' := by
  induction h with
  | nil => intro z S0 H0 hz; exact hz
  | cons hc _ ih => intro z S0 H0 hz; exact ih _ _ _ (push_sound _ _ _ _ _ _ _ _ hz hc)

theorem fold_bounded (ks : List Kernel) (hks : ∀ k ∈ ks, k.Good) :
    ∀ z : Summary, z.Bounded → (fold ks z).Bounded := by
  induction ks with
  | nil => intro z hz; exact hz
  | cons k ks ih =>
      intro z hz
      exact ih (fun k' hk' ↦ hks k' (by simp [hk'])) _
        (push_bounded k z (hks k (by simp)) hz).1

/-! Low coordinates `(S, u)`. -/

def low_call (k : Kernel) (S u S' u' : ℤ) : Prop :=
  S' = S + k.gain ∧ k.den*u' = k.num*(2*S - u + 3) + k.den*k.bias

def low_push (k : Kernel) (z : Summary) : Summary :=
  ⟨k.den*z.scale, k.num*(2*z.scale - z.sc), -k.num*z.hc,
    k.num*z.scale*(2*z.added + 3) - k.num*z.offset + k.den*z.scale*k.bias, z.added + k.gain⟩

def Summary.LowBounded (z : Summary) : Prop :=
  0 < z.scale ∧ 0 ≤ z.sc ∧ z.sc ≤ z.scale ∧ -z.scale ≤ z.hc ∧ z.hc ≤ z.scale ∧
    0 ≤ z.added ∧ 0 ≤ z.offset ∧ z.offset ≤ z.scale*z.added

theorem call_coordinates (k : Kernel) (S u S' u' : ℤ) :
    call k S (2*S - u + 3) S' (2*S' - u' + 3) ↔ low_call k S u S' u' := by
  simp only [call, low_call]
  constructor
  · rintro ⟨rfl, h⟩; exact ⟨rfl, by linarith⟩
  · rintro ⟨rfl, h⟩; exact ⟨rfl, by linarith⟩

theorem low_identity_bounded : identity.LowBounded := by
  simp [Summary.LowBounded, identity]

theorem low_push_bounded (k : Kernel) (z : Summary) (hk : k.Good) (hz : z.LowBounded) :
    (low_push k z).LowBounded ∧
      -(low_push k z).scale ≤ 2*(low_push k z).hc ∧
      2*(low_push k z).hc ≤ (low_push k z).scale := by
  obtain ⟨q, p, b, lam⟩ := k
  obtain ⟨Q, E, T, V, K⟩ := z
  simp only [Kernel.Good, Summary.LowBounded, low_push] at *
  obtain ⟨Hq, Hp, Hqp, Hb, Hl⟩ := hk
  obtain ⟨HQ, HE0, HE, HT0, HT, HK, HV0, HV⟩ := hz
  have HpE : p*E ≤ p*Q := mul_le_mul_of_nonneg_left HE Hp.le
  have HpT1 : -(p*Q) ≤ p*T := by nlinarith
  have HpT2 : p*T ≤ p*Q := mul_le_mul_of_nonneg_left HT Hp.le
  have HpV : p*V ≤ p*(Q*K) := mul_le_mul_of_nonneg_left HV Hp.le
  have HQK : 0 ≤ Q*K := by positivity
  have H2K : 2*p*(Q*K) ≤ q*(Q*K) := mul_le_mul_of_nonneg_right Hqp HQK
  have Hbias : 3*p + q*b ≤ q*lam := by nlinarith
  have Hbias' : (3*p + q*b)*Q ≤ q*lam*Q := mul_le_mul_of_nonneg_right Hbias HQ.le
  have HqQ : 0 < q*Q := by positivity
  refine ⟨⟨by positivity, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;> nlinarith

theorem low_push_sound (k : Kernel) (z : Summary) (S u S1 u1 S2 u2 : ℤ)
    (h1 : denotes z S u S1 u1) (h2 : low_call k S1 u1 S2 u2) :
    denotes (low_push k z) S u S2 u2 := by
  obtain ⟨q, p, b, lam⟩ := k
  obtain ⟨Q, E, T, V, K⟩ := z
  simp only [denotes, low_call, low_push] at *
  obtain ⟨HS1, Hu1⟩ := h1
  obtain ⟨HS2, Hu2⟩ := h2
  subst HS1
  refine ⟨by linarith, ?_⟩
  linear_combination Q*Hu2 - p*Hu1

def low_fold (ks : List Kernel) (z : Summary) : Summary := ks.foldl (fun z k ↦ low_push k z) z

theorem low_fold_bounded (ks : List Kernel) (hks : ∀ k ∈ ks, k.Good) :
    ∀ z : Summary, z.LowBounded → (low_fold ks z).LowBounded := by
  induction ks with
  | nil => intro z hz; exact hz
  | cons k ks ih =>
      intro z hz
      exact ih (fun k' hk' ↦ hks k' (by simp [hk'])) _
        (low_push_bounded k z (hks k (by simp)) hz).1

def high_low (k : Kernel) (z : Summary) : Summary :=
  ⟨k.den*z.scale, k.den*(2*z.scale - z.sc), -k.num*z.hc,
    k.den*((2*z.scale - z.sc)*k.gain + 2*z.scale*z.added - z.offset + 3*z.scale - z.hc*k.bias),
    k.gain + z.added⟩

theorem high_low_identity (k : Kernel) : high_low k identity = push k identity := by
  simp only [high_low, push, identity, Summary.mk.injEq]
  refine ⟨trivial, ?_, trivial, ?_, ?_⟩ <;> ring

theorem high_low_push (h k : Kernel) (z : Summary) :
    push k (high_low h z) = high_low h (low_push k z) := by
  simp only [high_low, push, low_push, Summary.mk.injEq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem high_low_fold (h : Kernel) (ks : List Kernel) (z : Summary) :
    fold ks (high_low h z) = high_low h (low_fold ks z) := by
  induction ks generalizing z with
  | nil => rfl
  | cons k ks ih =>
      simp only [fold, low_fold, List.foldl_cons] at ih ⊢
      rw [high_low_push, ih]

theorem high_low_word (h : Kernel) (ks : List Kernel) :
    fold (h :: ks) identity = high_low h (low_fold ks identity) := by
  simp only [fold, List.foldl_cons]
  rw [← high_low_identity]
  exact high_low_fold h ks identity

theorem low_fold_half (ks : List Kernel) (hks : ∀ k ∈ ks, k.Good) (hne : ks ≠ []) :
    ∀ z : Summary, z.LowBounded →
      -(low_fold ks z).scale ≤ 2*(low_fold ks z).hc ∧
        2*(low_fold ks z).hc ≤ (low_fold ks z).scale := by
  induction ks with
  | nil => exact absurd rfl hne
  | cons k ks ih =>
      intro z hz
      have hp := low_push_bounded k z (hks k (by simp)) hz
      rcases ks with _ | ⟨k', ks'⟩
      · exact hp.2
      · exact ih (fun k'' hk'' ↦ hks k'' (by simp_all)) (by simp) _ hp.1

theorem divisible_small (m z : ℤ) (hm : 0 < m) (hd : m ∣ z) (hz : |z| < m) : z = 0 := by
  obtain ⟨k, rfl⟩ := hd
  rw [abs_mul, abs_of_pos hm] at hz
  have : |k| < 1 := by nlinarith [abs_nonneg k]
  have : k = 0 := by rw [abs_lt] at this; omega
  simp [this]

/-- Integer form of the three-high-call identity. -/
theorem exact_descent (m S H0 H1 H2 Q0 Q1 A0 A1 B0 B1 C0 C1 mass : ℤ)
    (hm : 0 < m) (hd0 : m ∣ H0) (hd1 : m ∣ H1) (hd2 : m ∣ H2)
    (E0 : Q0*H1 = A0*S + B0*H0 + C0) (E1 : Q1*H2 = A1*(S+mass) + B1*H1 + C1)
    (hb : |A0*A1*mass + A0*C1 - A1*C0| < m) :
    A0*C1 = A1*(C0 - A0*mass) := by
  have E : A0*A1*mass + A0*C1 - A1*C0 = A0*Q1*H2 - (A1*Q0 + A0*B1)*H1 + A1*B0*H0 := by
    linear_combination A1*E0 - A0*E1
  have hd : m ∣ A0*A1*mass + A0*C1 - A1*C0 := by
    rw [E]
    exact dvd_add (dvd_sub (dvd_mul_of_dvd_right hd2 _) (dvd_mul_of_dvd_right hd1 _))
      (dvd_mul_of_dvd_right hd0 _)
  have := divisible_small _ _ hm hd hb
  linarith

theorem cross_bound (Q0 Q1 A0 A1 C0 C1 mass M : ℤ) (hQ0 : 0 < Q0) (hQ1 : 0 < Q1)
    (hm0 : 0 ≤ mass) (hm : mass ≤ M) (hA0' : 0 ≤ A0) (hA0 : A0 ≤ 2*Q0)
    (hA1' : 0 ≤ A1) (hA1 : A1 ≤ 2*Q1)
    (hC0' : 0 ≤ C0) (hC0 : C0 ≤ Q0*(2*M+2)) (hC1' : 0 ≤ C1) (hC1 : C1 ≤ Q1*(2*M+2)) :
    |A0*A1*mass + A0*C1 - A1*C0| ≤ Q0*Q1*(12*M+8) := by
  have haa : A0*A1 ≤ 4*(Q0*Q1) := by nlinarith
  have h1 : A0*A1*mass ≤ 4*(Q0*Q1)*M := mul_le_mul haa hm hm0 (by positivity)
  have h2 : A0*C1 ≤ 2*Q0*(Q1*(2*M+2)) := mul_le_mul hA0 hC1 hC1' (by positivity)
  have h3 : A1*C0 ≤ 2*Q1*(Q0*(2*M+2)) := mul_le_mul hA1 hC0 hC0' (by positivity)
  have p1 : 0 ≤ A0*A1*mass := by positivity
  have p2 : 0 ≤ A0*C1 := by positivity
  have p3 : 0 ≤ A1*C0 := by positivity
  rw [abs_le]; constructor <;> nlinarith [mul_pos hQ0 hQ1]

theorem dyadic_descent (m D d0 d1 : ℕ) (S H0 H1 H2 A0 A1 B0 B1 C0 C1 mass M : ℤ)
    (hd0 : d0 ≤ D) (hd1 : d1 ≤ D) (hm0 : 0 ≤ mass) (hm : mass ≤ M)
    (hA0' : 0 ≤ A0) (hA0 : A0 ≤ 2*2^d0) (hA1' : 0 ≤ A1) (hA1 : A1 ≤ 2*2^d1)
    (hC0' : 0 ≤ C0) (hC0 : C0 ≤ 2^d0*(2*M+2)) (hC1' : 0 ≤ C1) (hC1 : C1 ≤ 2^d1*(2*M+2))
    (hH0 : (2:ℤ)^(m+1) ∣ H0) (hH1 : (2:ℤ)^(m+1) ∣ H1) (hH2 : (2:ℤ)^(m+1) ∣ H2)
    (E0 : 2^d0*H1 = A0*S + B0*H0 + C0) (E1 : 2^d1*H2 = A1*(S+mass) + B1*H1 + C1)
    (hb : 2^(2*D)*(12*M+8) < (2:ℤ)^(m+1)) :
    A0*C1 = A1*(C0 - A0*mass) := by
  have HQ : (2:ℤ)^d0*2^d1 ≤ 2^(2*D) := by
    rw [← pow_add]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hM : 0 ≤ 12*M+8 := by linarith
  refine exact_descent _ S H0 H1 H2 (2^d0) (2^d1) A0 A1 B0 B1 C0 C1 mass (by positivity)
    hH0 hH1 hH2 E0 E1 ?_
  calc _ ≤ (2:ℤ)^d0*2^d1*(12*M+8) :=
        cross_bound _ _ _ _ _ _ _ _ (by positivity) (by positivity) hm0 hm hA0' hA0 hA1' hA1
          hC0' hC0 hC1' hC1
    _ ≤ 2^(2*D)*(12*M+8) := mul_le_mul_of_nonneg_right HQ hM
    _ < _ := hb

/-- In a nonempty low block, `|θ| ≤ 1/2` (scaled by the common denominator `Q`). -/
theorem contraction_nonempty (Q A T V K b lam C : ℤ) (hQ : 0 < Q) (hQA : Q ≤ A)
    (hT1 : -Q ≤ 2*T) (_hT2 : 2*T ≤ Q) (hV : 0 ≤ V) (hK : 0 ≤ K) (hb0 : 0 ≤ b) (hb : b ≤ lam)
    (hC : C = A*lam + 2*Q*K - V + 3*Q - T*b) :
    2*C ≤ A*(3*(lam+K) + 2*K + 6) := by
  have h1 : -2*T*b ≤ Q*b := by nlinarith
  have h2 : Q*b ≤ A*lam := by nlinarith
  subst hC; nlinarith

theorem contraction_empty (Q b lam C : ℤ) (hQ : 0 < Q) (hb : 1 ≤ b) (hbl : b ≤ lam)
    (hC : C = 2*Q*lam + 3*Q - Q*b) : 2*C ≤ (2*Q)*(3*lam + 6) := by
  subst hC; nlinarith

theorem word_contraction (h : Kernel) (ks : List Kernel) (hh : h.Good)
    (hks : ∀ k ∈ ks, k.Good) :
    2*(fold (h :: ks) identity).offset ≤ (fold (h :: ks) identity).sc *
      (3*(fold (h :: ks) identity).added + 2*(low_fold ks identity).added + 6) := by
  rw [high_low_word]
  have hz := low_fold_bounded ks hks identity low_identity_bounded
  rcases ks with _ | ⟨k, ks⟩
  · obtain ⟨q, p, b, lam⟩ := h
    simp only [low_fold, List.foldl_nil, high_low, identity, Kernel.Good] at hh ⊢
    obtain ⟨Hq, Hp, Hqp, Hb, Hl⟩ := hh
    nlinarith
  · have hhalf := low_fold_half (k :: ks) hks (by simp) identity low_identity_bounded
    generalize low_fold (k :: ks) identity = z at hz hhalf ⊢
    obtain ⟨q, p, b, lam⟩ := h
    obtain ⟨Q, E, T, V, K⟩ := z
    simp only [high_low, Kernel.Good, Summary.LowBounded] at hh hz hhalf ⊢
    obtain ⟨Hq, Hp, Hqp, Hb, Hl⟩ := hh
    obtain ⟨HQ, HE0, HE, HT0, HT, HK, HV0, HV⟩ := hz
    have hc := contraction_nonempty Q (2*Q - E) T V K b lam
      ((2*Q - E)*lam + 2*Q*K - V + 3*Q - T*b) HQ (by linarith) hhalf.1 hhalf.2 HV0 HK
      (by linarith) (by linarith) rfl
    have := mul_le_mul_of_nonneg_left hc Hq.le
    nlinarith

theorem contract (A0 A1 C0 C1 mass K : ℤ) (hA : 0 < A1) (E : A0*C1 = A1*(C0 - A0*mass))
    (h : 2*C0 ≤ A0*(3*mass + 2*K + 6)) :
    3*A0*C1 ≤ A1*C0 + (2*K+6)*A0*A1 := by
  have := mul_le_mul_of_nonneg_left h hA.le
  nlinarith

/-- Successive roots share the denominator of the first root. -/
theorem propagate_root (A C A0 C0 A1 C1 T mass : ℤ) (hA : 0 < A0)
    (H0 : A*C0 = A0*(C - A*T)) (H1 : A0*C1 = A1*(C0 - A0*mass)) :
    A*C1 = A1*(C - A*(T+mass)) := by
  have h : A0*(A*C1 - A1*(C - A*(T+mass))) = 0 := by
    linear_combination A*H1 + A1*H0
  rcases mul_eq_zero.1 h with h | h
  · omega
  · linarith

theorem shrink_bound (f : ℕ → ℤ) (C : ℤ) (n : ℕ)
    (h : ∀ i < n, 3*f (i+1) ≤ f i + 2*C) :
    3^n*f n ≤ f 0 + (3^n - 1)*C := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih := ih (fun i hi ↦ h i (by omega))
      have hs := h n (by omega)
      have hp : (0:ℤ) < 3^n := by positivity
      have := mul_le_mul_of_nonneg_left hs hp.le
      rw [pow_succ]; nlinarith

theorem linear_descent (f : ℕ → ℤ) (gap : ℤ) (n : ℕ) (h : ∀ i < n, f (i+1) < f i - gap) :
    f n ≤ f 0 - n*(gap+1) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ih := ih (fun i hi ↦ h i (by omega))
      have := h n (by omega)
      push_cast; linarith

theorem high_count (f : ℕ → ℤ) (A B V m : ℤ) (t q n : ℕ) (hA : 0 < A) (hB : 0 ≤ B)
    (hm : 0 < m) (_hV : 0 ≤ V) (hpow : V ≤ 3^t) (hq : B + 4 ≤ q*m)
    (hstart : f 0 ≤ A*V) (hend : 0 < f n)
    (hshrink : ∀ i < n, 3*f (i+1) ≤ f i + 2*A*(B+3))
    (hdrop : ∀ i < n, f (i+1) < f i - A*m) : n < t + q := by
  by_contra hnt
  push Not at hnt
  have Ht := shrink_bound f (A*(B+3)) t (fun i hi ↦ by
    have := hshrink i (by omega); linarith)
  have hp : (0:ℤ) < 3^t := by positivity
  have hinit : f 0 ≤ A*3^t := le_trans hstart (mul_le_mul_of_nonneg_left hpow hA.le)
  have hmid : f t ≤ A*(B+4) := by
    by_contra hc; push Not at hc
    have : (3:ℤ)^t*(A*(B+4)) < 3^t*f t := mul_lt_mul_of_pos_left hc hp
    nlinarith
  have Htail := linear_descent (fun i ↦ f (t+i)) (A*m) (n-t) (fun i hi ↦ by
    have := hdrop (t+i) (by omega); simpa [Nat.add_assoc] using this)
  simp only [Nat.add_zero, Nat.add_sub_cancel' (show t ≤ n by omega)] at Htail
  have hcount : (q:ℤ) ≤ ((n-t : ℕ) : ℤ) := by omega
  have hb := mul_le_mul_of_nonneg_left hq hA.le
  have hl := mul_le_mul_of_nonneg_right hcount (by positivity : (0:ℤ) ≤ A*m)
  nlinarith

end BMO9.Block
