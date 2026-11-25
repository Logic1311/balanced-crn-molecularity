import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.Bernstein
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators
namespace FixedPopulation.Cuts
noncomputable section

def bal (D : ℕ) (w : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.range (D+1), (∑ j ∈ Finset.range (D+1), w i j) =
    ∑ j ∈ Finset.range (D+1), w j i

def net (D : ℕ) (w : ℕ → ℕ → ℝ) (i : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (D+1), w i j * ((j:ℝ)-(i:ℝ))

def pre (v : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, v i

theorem potential_balance (D : ℕ) (w : ℕ → ℕ → ℝ) (hw : bal D w)
    (g : ℕ → ℝ) :
    (∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
      w i j * (g j - g i)) = 0 := by
  classical
  simp only [mul_sub, Finset.sum_sub_distrib]
  apply sub_eq_zero.mpr
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  rw [← Finset.sum_mul, ← Finset.sum_mul, hw i hi]

theorem net_total (D : ℕ) (w : ℕ → ℕ → ℝ) (hw : bal D w) :
    pre (net D w) (D+1) = 0 := by
  exact potential_balance D w hw (fun i => (i:ℝ))

theorem min_cut_bound (i j k : ℕ) :
    min (j:ℝ) (k:ℝ) - min (i:ℝ) (k:ℝ) ≤
      if i < k then (j:ℝ)-(i:ℝ) else 0 := by
  by_cases hi : i < k
  · rw [if_pos hi, min_eq_left (by exact_mod_cast hi.le : (i:ℝ)≤k)]
    have hj := min_le_left (j:ℝ) (k:ℝ)
    linarith
  · have hn : k ≤ i := Nat.le_of_not_gt hi
    have hr : (k:ℝ) ≤ (i:ℝ) := by exact_mod_cast hn
    rw [if_neg hi, min_eq_right hr]
    have hj := min_le_right (j:ℝ) (k:ℝ)
    linarith

theorem pre_nonneg (D : ℕ) (w : ℕ → ℕ → ℝ)
    (hw : bal D w) (hpos : ∀ i j, 0 ≤ w i j)
    (k : ℕ) (hk : k ≤ D+1) :
    0 ≤ pre (net D w) k := by
  classical
  have hzero := potential_balance D w hw (fun i => min (i:ℝ) (k:ℝ))
  have hle : (∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
      w i j * (min (j:ℝ) (k:ℝ) - min (i:ℝ) (k:ℝ))) ≤
      ∑ i ∈ Finset.range (D+1), if i < k then net D w i else 0 := by
    apply Finset.sum_le_sum
    intro i hi
    by_cases h : i < k
    · rw [if_pos h]
      unfold net
      apply Finset.sum_le_sum
      intro j hj
      have hbound := min_cut_bound i j k
      rw [if_pos h] at hbound
      exact mul_le_mul_of_nonneg_left hbound (hpos i j)
    · rw [if_neg h, ← Finset.sum_const_zero]
      apply Finset.sum_le_sum
      intro j hj
      have hbound := min_cut_bound i j k
      rw [if_neg h] at hbound
      simpa using mul_le_mul_of_nonneg_left hbound (hpos i j)
  rw [hzero] at hle
  have hf : (Finset.range (D+1)).filter (fun i => i < k) = Finset.range k := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range]
    omega
  rw [← Finset.sum_filter, hf] at hle
  exact hle

theorem summation_by_parts (D : ℕ) (v b : ℕ → ℝ) :
    (∑ i ∈ Finset.range (D+1), v i * b i) =
      (∑ i ∈ Finset.range D, pre v (i+1) * (b i - b (i+1))) +
      pre v (D+1) * b D := by
  induction D with
  | zero => simp [pre]
  | succ D ih =>
    rw [Finset.sum_range_succ (fun i => v i * b i) (D+1), Finset.sum_range_succ (fun i => pre v (i+1) * (b i - b (i+1))) D, ih]
    have h : pre v (D+1+1) = pre v (D+1) + v (D+1) := by
      unfold pre
      rw [Finset.sum_range_succ]
    rw [h]
    ring

def basis (N : ℝ) (D i : ℕ) (t : ℝ) : ℝ :=
  t^i * (N-t)^(D-i)
def wb (N a : ℝ) (D i : ℕ) (t : ℝ) : ℝ :=
  basis N D i t / basis N D i a

theorem basis_pos (N a : ℝ) (ha : 0 < a) (haN : a < N) (D i : ℕ) :
    0 < basis N D i a := by
  unfold basis
  exact mul_pos (pow_pos ha _) (pow_pos (sub_pos.mpr haN) _)

theorem wb_sub (N a t : ℝ) (ha : 0 < a) (haN : a < N) (D i : ℕ) (hi : i < D) :
    wb N a D i t - wb N a D (i+1) t =
      (a-t) * (N / (a^(i+1)*(N-a)^(D-i))) * basis N (D-1) i t := by
  have hD : D-i = (D-1-i)+1 := by omega
  have hD' : D-(i+1) = D-1-i := by omega
  have h₁ : a^i ≠ 0 := pow_ne_zero _ ha.ne'
  have h₂ : (N-a)^(D-1-i) ≠ 0 := pow_ne_zero _ (sub_pos.mpr haN).ne'
  unfold wb basis
  rw [hD', hD]
  simp only [pow_succ]
  field_simp [ha.ne', (sub_pos.mpr haN).ne']
  <;> ring

def fluxField (N a : ℝ) (D : ℕ) (w : ℕ → ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (D+1), net D w i * wb N a D i t

theorem cb_factor (N a : ℝ) (ha : 0 < a) (haN : a < N)
    (D : ℕ) (w : ℕ → ℕ → ℝ) (hw : bal D w)
    (hpos : ∀ i j, 0 ≤ w i j) :
    ∃ c : ℕ → ℝ, (∀ i ∈ Finset.range D, 0 ≤ c i) ∧
      ∀ t, fluxField N a D w t =
        (a-t) * ∑ i ∈ Finset.range D, c i * basis N (D-1) i t := by
  refine ⟨fun i => pre (net D w) (i+1) * (N/(a^(i+1)*(N-a)^(D-i))), ?_, ?_⟩
  · intro i hi
    have hN : 0 < N := lt_trans ha haN
    have hna : 0 < N-a := sub_pos.mpr haN
    have hh := pre_nonneg D w hw hpos (i+1) (by have := Finset.mem_range.mp hi; omega)
    exact mul_nonneg hh (div_nonneg hN.le (mul_nonneg (pow_nonneg ha.le _) (pow_nonneg hna.le _)))
  · intro t
    unfold fluxField
    rw [summation_by_parts, net_total D w hw, zero_mul, add_zero, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    rw [wb_sub N a t ha haN D i (Finset.mem_range.mp hi)]
    ring

-- Direct physical rate conversion: w is equilibrium flux, not a rate.
def ratesFromFlux (N a : ℝ) (D : ℕ) (w : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  w i j / basis N D i a
def rateField (N : ℝ) (D : ℕ) (k : ℕ → ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
    k i j * basis N D i t * ((j:ℝ)-(i:ℝ))

theorem rates_flux_field (N a : ℝ) (ha : 0<a) (haN : a<N) (D : ℕ)
    (w : ℕ → ℕ → ℝ) (t : ℝ) :
    rateField N D (ratesFromFlux N a D w) t = fluxField N a D w t := by
  unfold rateField fluxField
  apply Finset.sum_congr rfl
  intro i hi
  unfold net wb ratesFromFlux
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem rates_flux_balance (N a : ℝ) (ha : 0<a) (haN : a<N) (D : ℕ)
    (w : ℕ → ℕ → ℝ) (i j : ℕ) :
    ratesFromFlux N a D w i j * basis N D i a = w i j := by
  unfold ratesFromFlux
  exact div_mul_cancel₀ _ (basis_pos N a ha haN D i).ne'

theorem cb_rate_factor (N a : ℝ) (ha : 0<a) (haN : a<N) (D : ℕ)
    (k : ℕ → ℕ → ℝ) (hk : ∀ i j, 0 ≤ k i j)
    (hb : bal D (fun i j => k i j * basis N D i a)) :
    ∃ c : ℕ → ℝ, (∀ i ∈ Finset.range D, 0 ≤ c i) ∧
      ∀ t, rateField N D k t = (a-t) * ∑ i ∈ Finset.range D, c i * basis N (D-1) i t := by
  let w := fun i j => k i j * basis N D i a
  have hw : ∀ i j, 0 ≤ w i j := fun i j => mul_nonneg (hk i j) (basis_pos N a ha haN D i).le
  obtain ⟨c,hc,he⟩ := cb_factor N a ha haN D w hb hw
  refine ⟨c,hc,fun t => ?_⟩
  rw [← he, ← rates_flux_field N a ha haN D w t]
  unfold rateField
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have h : ratesFromFlux N a D w i j = k i j := by
    unfold ratesFromFlux w
    exact mul_div_cancel_right₀ _ (basis_pos N a ha haN D i).ne'
  rw [h]

#print axioms pre_nonneg
#print axioms cb_factor
#print axioms cb_rate_factor

def detailed (N a : ℝ) (D : ℕ) (k : ℕ → ℕ → ℝ) : Prop :=
  ∀ i ∈ Finset.range (D+1), ∀ j ∈ Finset.range (D+1),
    k i j * basis N D i a = k j i * basis N D j a

theorem detailed_bal (N a : ℝ) (D : ℕ) (k : ℕ → ℕ → ℝ)
    (h : detailed N a D k) :
    bal D (fun i j => k i j * basis N D i a) := by
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  exact h i hi j hj

def pairRate (N a : ℝ) (c : ℕ → ℝ) (r i j : ℕ) : ℝ :=
  (if i=r ∧ j=r+1 then c r * (a/N) else 0) +
  (if i=r+1 ∧ j=r then c r * (1-a/N) else 0)

def chainRate (N a : ℝ) (D : ℕ) (c : ℕ → ℝ) (i j : ℕ) : ℝ :=
  ∑ r ∈ Finset.range D, pairRate N a c r i j

theorem pairRate_nonneg (N a : ℝ) (c : ℕ → ℝ) (r i j : ℕ)
    (ha : 0 < a) (haN : a < N) (hc : 0 ≤ c r) :
    0 ≤ pairRate N a c r i j := by
  have hN : 0<N := lt_trans ha haN
  have h1 : 0 ≤ c r * (a/N) := mul_nonneg hc (div_nonneg ha.le hN.le)
  have h2 : 0 ≤ c r * (1-a/N) := mul_nonneg hc (sub_nonneg.mpr ((div_le_one hN).2 haN.le))
  unfold pairRate
  split_ifs <;> linarith

theorem chainRate_nonneg (N a : ℝ) (D : ℕ) (c : ℕ → ℝ)
    (ha : 0<a) (haN : a<N) (hc : ∀ r ∈ Finset.range D, 0 ≤ c r) :
    ∀ i j, 0 ≤ chainRate N a D c i j := by
  intro i j
  apply Finset.sum_nonneg
  intro r hr
  exact pairRate_nonneg N a c r i j ha haN (hc r hr)

theorem pair_equilibrium (N a : ℝ) (D r : ℕ) (c : ℕ → ℝ)
    (ha : 0<a) (haN : a<N) (hr : r<D) :
    c r*(a/N)*basis N D r a = c r*(1-a/N)*basis N D (r+1) a := by
  have hN : 0<N := lt_trans ha haN
  have hD : D-r=(D-(r+1))+1 := by omega
  unfold basis
  rw [hD]
  simp only [pow_succ]
  field_simp [hN.ne'] <;> ring

theorem pair_detailed (N a : ℝ) (D r : ℕ) (c : ℕ → ℝ)
    (ha : 0<a) (haN : a<N) (hr : r<D) :
    detailed N a D (pairRate N a c r) := by
  intro i hi j hj
  by_cases h1 : i=r ∧ j=r+1
  · obtain ⟨hI,hJ⟩ := h1
    subst i; subst j
    simpa [pairRate] using pair_equilibrium N a D r c ha haN hr
  · by_cases h2 : i=r+1 ∧ j=r
    · obtain ⟨hI,hJ⟩ := h2
      subst i; subst j
      simpa [pairRate] using (pair_equilibrium N a D r c ha haN hr).symm
    · have h3 : ¬ (j=r ∧ i=r+1) := fun h => h2 ⟨h.2,h.1⟩
      have h4 : ¬ (j=r+1 ∧ i=r) := fun h => h1 ⟨h.2,h.1⟩
      simp [pairRate,h1,h2,h3,h4]

theorem chain_detailed (N a : ℝ) (D : ℕ) (c : ℕ → ℝ)
    (ha : 0<a) (haN : a<N) : detailed N a D (chainRate N a D c) := by
  intro i hi j hj
  unfold chainRate
  rw [Finset.sum_mul,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro r hr
  exact pair_detailed N a D r c ha haN (Finset.mem_range.mp hr) i hi j hj

theorem pair_field (N a t : ℝ) (D r : ℕ) (c : ℕ → ℝ)
    (hN : 0<N) (hr : r<D) :
    rateField N D (pairRate N a c r) t = (a-t)*c r*basis N (D-1) r t := by
  classical
  have hD : D-r=(D-1-r)+1 := by omega
  have hD' : D-(r+1)=D-1-r := by omega
  have hrm : r ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
  have hrm' : r+1 ∈ Finset.range (D+1) := Finset.mem_range.mpr (by omega)
  unfold rateField
  simp only [pairRate, add_mul, Finset.sum_add_distrib]
  have h1 :
    (∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
       (if i=r ∧ j=r+1 then c r*(a/N) else 0) * basis N D i t * ((j:ℝ)-(i:ℝ))) =
      c r*(a/N)*basis N D r t := by
    rw [Finset.sum_eq_single r]
    · simp only [true_and, ite_mul, zero_mul]
      rw [Finset.sum_eq_single (r+1)]
      · simp <;> ring
      · intro j hj hne
        simp [hne]
      · intro hn; exact False.elim (hn hrm')
    · intro i hi hne
      simp [hne]
    · intro hn; exact False.elim (hn hrm)
  have h2 :
    (∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
       (if i=r+1 ∧ j=r then c r*(1-a/N) else 0) * basis N D i t * ((j:ℝ)-(i:ℝ))) =
      -(c r*(1-a/N)*basis N D (r+1) t) := by
    rw [Finset.sum_eq_single (r+1)]
    · simp only [true_and, ite_mul, zero_mul]
      rw [Finset.sum_eq_single r]
      · simp <;> ring
      · intro j hj hne
        simp [hne]
      · intro hn; exact False.elim (hn hrm)
    · intro i hi hne
      simp [hne]
    · intro hn; exact False.elim (hn hrm')
  rw [h1,h2]
  unfold basis
  rw [hD',hD]
  simp only [pow_succ]
  field_simp [hN.ne'] <;> ring

theorem chain_field (N a t : ℝ) (D : ℕ) (c : ℕ → ℝ) (hN : 0<N) :
    rateField N D (chainRate N a D c) t =
      (a-t) * ∑ i ∈ Finset.range D, c i * basis N (D-1) i t := by
  unfold rateField chainRate
  simp_rw [Finset.sum_mul]
  calc
    _ = ∑ i ∈ Finset.range (D+1), ∑ r ∈ Finset.range D, ∑ j ∈ Finset.range (D+1),
        pairRate N a c r i j * basis N D i t * ((j:ℝ)-(i:ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
    _ = ∑ r ∈ Finset.range D, ∑ i ∈ Finset.range (D+1), ∑ j ∈ Finset.range (D+1),
        pairRate N a c r i j * basis N D i t * ((j:ℝ)-(i:ℝ)) := Finset.sum_comm
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      change rateField N D (pairRate N a c r) t = _
      rw [pair_field N a t D r c hN (Finset.mem_range.mp hr)]
      ring

def CBRealizable (N a : ℝ) (D : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ k : ℕ → ℕ → ℝ, (∀ i j, 0 ≤ k i j) ∧
    bal D (fun i j => k i j * basis N D i a) ∧
    ∀ t, 0<t → t<N → rateField N D k t=f t
def DBRealizable (N a : ℝ) (D : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ k : ℕ → ℕ → ℝ, (∀ i j, 0 ≤ k i j) ∧
    detailed N a D k ∧ ∀ t, 0<t → t<N → rateField N D k t=f t
def PositiveFactor (N a : ℝ) (D : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ c : ℕ → ℝ, (∀ i ∈ Finset.range D, 0 ≤ c i) ∧
    ∀ t, 0<t → t<N → f t = (a-t) * ∑ i ∈ Finset.range D, c i * basis N (D-1) i t

theorem fixed_degree_exact (N a : ℝ) (ha : 0<a) (haN : a<N)
    (D : ℕ) (f : ℝ → ℝ) :
    (CBRealizable N a D f ↔ PositiveFactor N a D f) ∧
    (DBRealizable N a D f ↔ PositiveFactor N a D f) := by
  have hcb : CBRealizable N a D f → PositiveFactor N a D f := by
    rintro ⟨k,hk,hb,hf⟩
    obtain ⟨c,hc,he⟩ := cb_rate_factor N a ha haN D k hk hb
    exact ⟨c,hc,fun t ht htN => (hf t ht htN).symm.trans (he t)⟩
  have hdb : PositiveFactor N a D f → DBRealizable N a D f := by
    rintro ⟨c,hc,hf⟩
    refine ⟨chainRate N a D c,chainRate_nonneg N a D c ha haN hc,chain_detailed N a D c ha haN,?_⟩
    intro t ht htN
    rw [chain_field N a t D c (lt_trans ha haN)]
    exact (hf t ht htN).symm
  have hdbcb : DBRealizable N a D f → CBRealizable N a D f := by
    rintro ⟨k,hk,hd,hf⟩
    exact ⟨k,hk,detailed_bal N a D k hd,hf⟩
  exact ⟨⟨hcb,hdbcb ∘ hdb⟩,⟨hcb ∘ hdbcb,hdb⟩⟩

#print axioms chain_field
#print axioms fixed_degree_exact


-- Nonnegative coefficient representations can be elevated without changing the field.
theorem basis_elevate (N t : ℝ) (d i : ℕ) (hi : i≤d) :
    N*basis N d i t = basis N (d+1) i t + basis N (d+1) (i+1) t := by
  have h1 : d+1-i = d-i+1 := by omega
  have h2 : d+1-(i+1) = d-i := by omega
  unfold basis
  rw [h1,h2]
  simp only [pow_succ]
  ring

def elevateCoef (N : ℝ) (D : ℕ) (c : ℕ → ℝ) (i : ℕ) : ℝ :=
  (if i<D then c i/N else 0) + (if 0 < i then c (i-1)/N else 0)

theorem elevateCoef_nonneg (N : ℝ) (hN : 0<N) (D : ℕ) (c : ℕ → ℝ)
    (hc : ∀ i ∈ Finset.range D, 0 ≤ c i) :
    ∀ i ∈ Finset.range (D+1), 0 ≤ elevateCoef N D c i := by
  intro i hi
  unfold elevateCoef
  apply add_nonneg
  · split_ifs with h
    · exact div_nonneg (hc i (Finset.mem_range.mpr h)) hN.le
    · rfl
  · split_ifs with h
    · have h' : i-1<D := by have := Finset.mem_range.mp hi; omega
      exact div_nonneg (hc (i-1) (Finset.mem_range.mpr h')) hN.le
    · rfl

theorem elevate_field_sum (N t : ℝ) (hN : 0<N) (D : ℕ) (c : ℕ → ℝ)
    (hD : 0<D) :
    (∑ i ∈ Finset.range D, c i*basis N (D-1) i t) =
      ∑ i ∈ Finset.range (D+1), elevateCoef N D c i*basis N D i t := by
  classical
  have hA :
      (∑ i ∈ Finset.range (D+1), (if i<D then c i/N else 0)*basis N D i t) =
      ∑ i ∈ Finset.range D, c i/N*basis N D i t := by
    rw [Finset.sum_range_succ]
    simp only [lt_irrefl, if_false, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro i hi
    rw [if_pos (Finset.mem_range.mp hi)]
  have hB :
      (∑ i ∈ Finset.range (D+1), (if 0 < i then c (i-1)/N else 0)*basis N D i t) =
      ∑ i ∈ Finset.range D, c i/N*basis N D (i+1) t := by
    rw [Finset.sum_range_succ']
    simp
  unfold elevateCoef
  simp only [add_mul, Finset.sum_add_distrib]
  rw [hA,hB,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i≤D-1 := by have := Finset.mem_range.mp hi; omega
  have e := basis_elevate N t (D-1) i hi'
  have he : D-1+1=D := by omega
  rw [he] at e
  rw [←mul_add,←e]
  field_simp [hN.ne']

theorem factor_elevate (N a : ℝ) (hN : 0<N) (D : ℕ) (f : ℝ → ℝ)
    (hf : PositiveFactor N a D f) : PositiveFactor N a (D+1) f := by
  obtain ⟨c,hc,he⟩ := hf
  by_cases hD : D=0
  · subst D
    refine ⟨fun _ => 0, by simp, ?_⟩
    intro t ht htN
    simpa using he t ht htN
  · refine ⟨elevateCoef N D c, elevateCoef_nonneg N hN D c hc, ?_⟩
    intro t ht htN
    rw [he t ht htN,elevate_field_sum N t hN D c (by omega)]
    simp

theorem factor_add (N a : ℝ) (D : ℕ) (f g : ℝ → ℝ)
    (hf : PositiveFactor N a D f) (hg : PositiveFactor N a D g) :
    PositiveFactor N a D (fun t => f t+g t) := by
  obtain ⟨c,hc,he⟩ := hf
  obtain ⟨d,hd,hg'⟩ := hg
  refine ⟨fun i => c i+d i, fun i hi => add_nonneg (hc i hi) (hd i hi), ?_⟩
  intro t ht htN
  dsimp only
  rw [he t ht htN,hg' t ht htN]
  simp only [add_mul,Finset.sum_add_distrib,mul_add]

def mixedField (N : ℝ) (D : ℕ) (k : ℕ → ℕ → ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ Finset.range (D+1), rateField N d (k d) t

def MixedCB (N a : ℝ) (D : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ k : ℕ → ℕ → ℕ → ℝ, (∀ d i j, 0≤k d i j) ∧
    (∀ d≤D, bal d (fun i j => k d i j * basis N d i a)) ∧
    ∀ t, 0<t → t<N → mixedField N D k t=f t

theorem mixed_factor (N a : ℝ) (ha : 0<a) (haN : a<N)
    (D : ℕ) (k : ℕ → ℕ → ℕ → ℝ) (hk : ∀ d i j, 0≤k d i j)
    (hb : ∀ d≤D, bal d (fun i j => k d i j*basis N d i a)) :
    PositiveFactor N a D (mixedField N D k) := by
  induction D with
  | zero =>
    have h := cb_rate_factor N a ha haN 0 (k 0) (hk 0) (hb 0 (by omega))
    obtain ⟨c,hc,he⟩ := h
    exact ⟨c,hc,fun t _ _ => by simpa [mixedField] using he t⟩
  | succ D ih =>
    have h1 := factor_elevate N a (lt_trans ha haN) D (mixedField N D k)
      (ih (fun d hd => hb d (by omega)))
    obtain ⟨c,hc,he⟩ := cb_rate_factor N a ha haN (D+1) (k (D+1)) (hk (D+1))
      (hb (D+1) (by omega))
    have h2 : PositiveFactor N a (D+1) (rateField N (D+1) (k (D+1))) :=
      ⟨c,hc,fun t _ _ => he t⟩
    have h3 := factor_add N a (D+1) _ _ h1 h2
    obtain ⟨v,hv,h⟩ := h3
    refine ⟨v,hv,?_⟩
    intro t ht htN
    unfold mixedField
    rw [Finset.sum_range_succ]
    exact h t ht htN

theorem mixed_exact (N a : ℝ) (ha : 0<a) (haN : a<N)
    (D : ℕ) (f : ℝ → ℝ) :
    MixedCB N a D f ↔ PositiveFactor N a D f := by
  constructor
  · rintro ⟨k,hk,hb,hf⟩
    obtain ⟨c,hc,h⟩ := mixed_factor N a ha haN D k hk hb
    exact ⟨c,hc,fun t ht htN => (hf t ht htN).symm.trans (h t ht htN)⟩
  · intro hf
    obtain ⟨k,hk,hb,he⟩ := (fixed_degree_exact N a ha haN D f).1.mpr hf
    let k' := fun (d i j : ℕ) => if d=D then k i j else 0
    refine ⟨k',?_,?_,?_⟩
    · intro d i j
      dsimp [k']; split_ifs <;> simp [hk]
    · intro d hd
      by_cases h : d=D
      · subst d
        simpa [k'] using hb
      · simp [bal,k',h]
    · intro t ht htN
      unfold mixedField
      rw [Finset.sum_eq_single D]
      · simpa [k'] using he t ht htN
      · intro d hd hne
        simp [rateField,k',hne]
      · intro hn
        exact False.elim (hn (Finset.mem_range.mpr (by omega)))

#print axioms factor_elevate
#print axioms mixed_exact


open Polynomial in
theorem basis_coeff_unique (N l : ℝ) (hl : 0≤l) (hlN : l<N) (D : ℕ) (c d : ℕ → ℝ)
    (he : ∀ t, l<t → t<N →
      (∑ i ∈ Finset.range (D+1), c i * basis N D i t) =
      ∑ i ∈ Finset.range (D+1), d i * basis N D i t) :
    ∀ i≤D, c i=d i := by
  have hN : 0<N := lt_of_le_of_lt hl hlN
  let p : ℝ[X] := ∑ i ∈ Finset.range (D+1), C (c i)*X^i
  let q : ℝ[X] := ∑ i ∈ Finset.range (D+1), C (d i)*X^i
  have hpq : p=q := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ioi_infinite (l/(N-l))).mono
    intro x hx
    have hxl : l/(N-l)<x := hx
    have hx0 : 0<x := lt_of_le_of_lt (div_nonneg hl (sub_pos.mpr hlN).le) hxl
    let t : ℝ := N*x/(1+x)
    have hden : 0<1+x := by linarith
    have ht : 0<t := div_pos (mul_pos hN hx0) hden
    have htN : t<N := by
      dsimp [t]
      apply (div_lt_iff₀ hden).2
      nlinarith
    have hs : 0<N-t := sub_pos.mpr htN
    have htx : t = (N-t)*x := by
      dsimp [t]
      field_simp [hden.ne']
      <;> ring
    have hb : ∀ i≤D, basis N D i t = (N-t)^D * x^i := by
      intro i hi
      unfold basis
      calc
        _ = ((N-t)*x)^i*(N-t)^(D-i) := by rw [← htx]
        _ = ((N-t)^i*(N-t)^(D-i))*x^i := by rw [mul_pow]; ring
        _ = _ := by rw [← pow_add, Nat.add_sub_of_le hi]
    have hlt : l<t := by
      have h := (div_lt_iff₀ (sub_pos.mpr hlN)).1 hxl
      dsimp [t]
      apply (lt_div_iff₀ hden).2
      nlinarith
    have hh := he t hlt htN
    change Polynomial.eval x p = Polynomial.eval x q
    simp only [p, q, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
    have hh' :
        (N-t)^D*(∑ i ∈ Finset.range (D+1), c i*x^i) =
        (N-t)^D*(∑ i ∈ Finset.range (D+1), d i*x^i) := by
      rw [Finset.mul_sum,Finset.mul_sum]
      have hc : (∑ i ∈ Finset.range (D+1), c i*basis N D i t) =
          ∑ i ∈ Finset.range (D+1), (N-t)^D*(c i*x^i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hb i (by have := Finset.mem_range.mp hi; omega)]
        ring
      have hd : (∑ i ∈ Finset.range (D+1), d i*basis N D i t) =
          ∑ i ∈ Finset.range (D+1), (N-t)^D*(d i*x^i) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [hb i (by have := Finset.mem_range.mp hi; omega)]
        ring
      rw [← hc, ← hd]
      exact hh
    exact mul_left_cancel₀ (pow_ne_zero _ hs.ne') hh'
  intro i hi
  have e := congrArg (fun z : ℝ[X] => z.coeff i) hpq
  have hm : i∈Finset.range (D+1) := Finset.mem_range.mpr (by omega)
  simpa [p,q, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, hm] using e

#print axioms basis_coeff_unique

-- The three binomial moment identities used for an explicit cubic example.
def bern (n i : ℕ) (t : ℝ) : ℝ :=
  (n.choose i : ℝ)*basis 1 n i t

theorem bern_sum (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range (n+1), bern n i t) = 1 := by
  have h := congrArg (Polynomial.eval t) (bernsteinPolynomial.sum ℝ n)
  simpa [bern, basis, bernsteinPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, mul_assoc] using h

theorem bern_first (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range (n+1), (i:ℝ)*bern n i t) = (n:ℝ)*t := by
  have h := congrArg (Polynomial.eval t) (bernsteinPolynomial.sum_smul ℝ n)
  simpa [bern, basis, bernsteinPolynomial, Polynomial.eval_finset_sum,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_sub, nsmul_eq_mul,
    Polynomial.eval_natCast, mul_assoc] using h

theorem bern_second (n : ℕ) (t : ℝ) :
    (∑ i ∈ Finset.range (n+1), (i:ℝ)*((i:ℝ)-1)*bern n i t) =
      (n:ℝ)*((n:ℝ)-1)*t^2 := by
  have h := congrArg (Polynomial.eval t) (bernsteinPolynomial.sum_mul_smul ℝ n)
  have hn : ∀ j : ℕ, (j:ℝ)*((j-1:ℕ):ℝ)=(j:ℝ)*((j:ℝ)-1) := by
    intro j
    cases j with
    | zero => simp
    | succ j => push_cast; simp
  simp [bernsteinPolynomial, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_sub, nsmul_eq_mul, Polynomial.eval_natCast] at h
  simp_rw [hn] at h
  simpa [bern,basis,mul_assoc] using h

def quad (ε t : ℝ) : ℝ := (t-1/2)^2 + ε

def quadCoef (n : ℕ) (ε : ℝ) (i : ℕ) : ℝ :=
  ε + 1/4 - (i:ℝ)/n + ((i:ℝ)*((i:ℝ)-1))/((n:ℝ)*((n:ℝ)-1))

theorem quad_expansion (n : ℕ) (hn : 2≤n) (ε t : ℝ) :
    (∑ i ∈ Finset.range (n+1), quadCoef n ε i*bern n i t)=quad ε t := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hn1 : (n:ℝ)-1 ≠ 0 := by
    have h : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    linarith
  unfold quadCoef quad
  simp only [add_mul, sub_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have h1 : (∑ i ∈ Finset.range (n+1), (ε+1/4)*bern n i t) = ε+1/4 := by
    rw [← Finset.mul_sum,bern_sum,mul_one]
  have h2 : (∑ i ∈ Finset.range (n+1), (i:ℝ)/n*bern n i t) = t := by
    have he : (∑ i ∈ Finset.range (n+1), (i:ℝ)/n*bern n i t) =
        (∑ i ∈ Finset.range (n+1), (i:ℝ)*bern n i t)/n := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he,bern_first]
    field_simp
  have h3 : (∑ i ∈ Finset.range (n+1), (i:ℝ)*((i:ℝ)-1)/((n:ℝ)*((n:ℝ)-1))*bern n i t) = t^2 := by
    have he : (∑ i ∈ Finset.range (n+1), (i:ℝ)*((i:ℝ)-1)/((n:ℝ)*((n:ℝ)-1))*bern n i t) =
        (∑ i ∈ Finset.range (n+1), (i:ℝ)*((i:ℝ)-1)*bern n i t)/((n:ℝ)*((n:ℝ)-1)) := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      ring
    rw [he,bern_second]
    field_simp
  -- The outer add has distributed epsilon+1/4 too.
  have h1' : (∑ i ∈ Finset.range (n+1), ε*bern n i t) +
      (∑ i ∈ Finset.range (n+1), (1/4)*bern n i t) = ε+1/4 := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← add_mul]
    exact h1
  rw [h2,h3]
  linarith [h1']

theorem quad_coef_square (n : ℕ) (hn : 2≤n) (ε : ℝ) (i : ℕ) :
    quadCoef n ε i =
      ε+(((2*(i:ℝ)-(n:ℝ))^2-(n:ℝ))/(4*(n:ℝ)*((n:ℝ)-1))) := by
  have h : (2:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have hn0 : (n:ℝ) ≠ 0 := by linarith
  have hn1 : (n:ℝ)-1 ≠ 0 := by linarith
  unfold quadCoef
  field_simp
  ring

theorem quad_factor_iff (n : ℕ) (hn : 2≤n) (ε a : ℝ)
    (ha : 0<a) (ha1 : a<1) :
    PositiveFactor 1 a (n+1) (fun t => (a-t)*quad ε t) ↔
      ∀ i≤n, 0≤quadCoef n ε i := by
  constructor
  · rintro ⟨c,hc,he⟩
    have hEq : ∀ t, a<t → t<1 →
      (∑ i ∈ Finset.range (n+1), c i*basis 1 n i t) =
      ∑ i ∈ Finset.range (n+1), (quadCoef n ε i*(n.choose i:ℝ))*basis 1 n i t := by
      intro t ht ht1
      have h := he t (lt_trans ha ht) ht1
      simp only [Nat.add_sub_cancel] at h
      change (a-t)*quad ε t = _ at h
      have hq := quad_expansion n hn ε t
      have hsum : (∑ i ∈ Finset.range (n+1), (quadCoef n ε i*(n.choose i:ℝ))*basis 1 n i t) =
          quad ε t := by
        simpa [bern, mul_assoc] using hq
      rw [hsum]
      exact (mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_lt ht)) h).symm
    have hu := basis_coeff_unique 1 a ha.le ha1 n c
      (fun i => quadCoef n ε i*(n.choose i:ℝ)) hEq
    intro i hi
    have hp : 0<(n.choose i:ℝ) := by
      exact_mod_cast Nat.choose_pos hi
    have h := hc i (Finset.mem_range.mpr (by omega))
    rw [hu i hi] at h
    exact nonneg_of_mul_nonneg_left h hp
  · intro h
    refine ⟨fun i => quadCoef n ε i*(n.choose i:ℝ), ?_, ?_⟩
    · intro i hi
      exact mul_nonneg (h i (by have := Finset.mem_range.mp hi; omega)) (by positivity)
    · intro t _ _
      have hq := quad_expansion n hn ε t
      simp only [Nat.add_sub_cancel]
      have hsum : (∑ i ∈ Finset.range (n+1), (quadCoef n ε i*(n.choose i:ℝ))*basis 1 n i t) =
          quad ε t := by simpa [bern,mul_assoc] using hq
      rw [hsum]

#print axioms quad_expansion
#print axioms quad_factor_iff


theorem factor_monotone (N a : ℝ) (hN : 0<N) (D M : ℕ) (hDM : D≤M)
    (f : ℝ → ℝ) (hf : PositiveFactor N a D f) : PositiveFactor N a M f := by
  induction M, hDM using Nat.le_induction with
  | base => exact hf
  | succ M hle ih => exact factor_elevate N a hN M f ih

theorem quad_even_nonneg_iff (m : ℕ) (hm : 1≤m) (ε : ℝ) :
    (∀ i≤2*m, 0≤quadCoef (2*m) ε i) ↔
      1/(4*((2*m:ℕ):ℝ)-4) ≤ ε := by
  let n := 2*m
  have hn : 2≤n := by dsimp [n]; omega
  have hnR : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hn1 : 0 < (n:ℝ)-1 := by linarith
  have hden : 0<4*(n:ℝ)*((n:ℝ)-1) := by positivity
  have hnm : (n:ℝ)=2*(m:ℝ) := by simp [n]
  have hrel : (n:ℝ)/(4*(n:ℝ)*((n:ℝ)-1)) = 1/(4*(n:ℝ)-4) := by
    field_simp
    <;> ring
  change (∀ i≤n, 0≤quadCoef n ε i) ↔ 1/(4*(n:ℝ)-4) ≤ ε
  constructor
  · intro h
    have hh := h m (by dsimp [n]; omega)
    rw [quad_coef_square n hn ε m, hnm] at hh
    have he : (2*(m:ℝ)-2*(m:ℝ))^2=0 := by ring
    rw [he, zero_sub, neg_div, ← hnm, hrel] at hh
    linarith
  · intro h i hi
    rw [quad_coef_square n hn ε i, sub_div, hrel]
    have hp := div_nonneg (sq_nonneg (2*(i:ℝ)-(n:ℝ))) hden.le
    linarith

theorem quad_odd_nonneg_iff (m : ℕ) (hm : 1≤m) (ε : ℝ) :
    (∀ i≤2*m+1, 0≤quadCoef (2*m+1) ε i) ↔
      1/(4*((2*m+1:ℕ):ℝ)) ≤ ε := by
  let n := 2*m+1
  have hn : 2≤n := by dsimp [n]; omega
  have hnR : (2:ℝ)≤(n:ℝ) := by exact_mod_cast hn
  have hn0 : 0 < (n:ℝ) := by linarith
  have hn1 : 0 < (n:ℝ)-1 := by linarith
  have hden : 0<4*(n:ℝ)*((n:ℝ)-1) := by positivity
  have hnm : (n:ℝ)=2*(m:ℝ)+1 := by simp [n]
  have hrel : ((n:ℝ)-1)/(4*(n:ℝ)*((n:ℝ)-1)) = 1/(4*(n:ℝ)) := by
    field_simp [ne_of_gt hn1]
  have hrepr : ∀ i, quadCoef n ε i =
      ε + ((2*(i:ℝ)-(n:ℝ))^2-1)/(4*(n:ℝ)*((n:ℝ)-1)) - 1/(4*(n:ℝ)) := by
    intro i
    rw [quad_coef_square n hn ε i, ← hrel, sub_div, sub_div]
    ring
  change (∀ i≤n, 0≤quadCoef n ε i) ↔ 1/(4*(n:ℝ)) ≤ ε
  constructor
  · intro h
    have hh := h m (by dsimp [n]; omega)
    rw [hrepr] at hh
    have he : (2*(m:ℝ)-(n:ℝ))^2=1 := by rw [hnm]; ring
    rw [he,sub_self,zero_div,add_zero] at hh
    linarith
  · intro h i hi
    rw [hrepr]
    have hs : 1≤(2*(i:ℝ)-(n:ℝ))^2 := by
      by_cases hh : i≤m
      · have hr : (i:ℝ)≤(m:ℝ) := by exact_mod_cast hh
        have hz : 2*(i:ℝ)-(n:ℝ)≤ -1 := by rw [hnm]; linarith
        nlinarith [sq_nonneg (2*(i:ℝ)-(n:ℝ)+1)]
      · have hh' : m + 1 ≤ i := by omega
        have hr : (m:ℝ)+1≤(i:ℝ) := by exact_mod_cast hh'
        have hz : 1≤2*(i:ℝ)-(n:ℝ) := by rw [hnm]; linarith
        nlinarith [sq_nonneg (2*(i:ℝ)-(n:ℝ)-1)]
    have hp := div_nonneg (sub_nonneg.mpr hs) hden.le
    linarith

theorem cubic_even_degree (m : ℕ) (hm : 1≤m) (ε a : ℝ)
    (ha : 0<a) (ha1 : a<1) :
    MixedCB 1 a (2*m+1) (fun t => (a-t)*quad ε t) ↔
      1/(4*((2*m:ℕ):ℝ)-4) ≤ ε := by
  rw [mixed_exact 1 a ha ha1, quad_factor_iff (2*m) (by omega) ε a ha ha1]
  exact quad_even_nonneg_iff m hm ε

theorem cubic_odd_degree (m : ℕ) (hm : 1≤m) (ε a : ℝ)
    (ha : 0<a) (ha1 : a<1) :
    MixedCB 1 a (2*m+1+1) (fun t => (a-t)*quad ε t) ↔
      1/(4*((2*m+1:ℕ):ℝ)) ≤ ε := by
  rw [mixed_exact 1 a ha ha1, quad_factor_iff (2*m+1) (by omega) ε a ha ha1]
  exact quad_odd_nonneg_iff m hm ε

theorem cubic_no_degree_two (ε : ℝ) :
    ¬PositiveFactor 1 (1/3) 2 (fun t => (1/3-t)*quad ε t) := by
  rintro ⟨c,hc,he⟩
  have h1 := he (1/2) (by norm_num) (by norm_num)
  have h2 := he (5/8) (by norm_num) (by norm_num)
  have h3 := he (3/4) (by norm_num) (by norm_num)
  norm_num [basis,quad,Finset.sum_range_succ] at h1 h2 h3
  linarith

theorem cubic_unbounded_degree_gap (D : ℕ) :
    ∃ ε : ℝ, 0<ε ∧
      ¬MixedCB 1 (1/3) D (fun t => (1/3-t)*quad ε t) ∧
      ∃ M : ℕ, DBRealizable 1 (1/3) M (fun t => (1/3-t)*quad ε t) := by
  let m := D+1
  let ε : ℝ := 1/(8*((2*m:ℕ):ℝ)-8)
  have hm : 1≤m := by dsimp [m]; omega
  have hden : 0<8*((2*m:ℕ):ℝ)-8 := by
    have h : (1:ℝ)≤(m:ℝ) := by exact_mod_cast hm
    push_cast
    linarith
  have hε : 0<ε := one_div_pos.mpr hden
  refine ⟨ε,hε,?_,?_⟩
  · intro hc
    have hfactor := (mixed_exact 1 (1/3) (by norm_num) (by norm_num) D _).1 hc
    have hlarge := factor_monotone 1 (1/3) (by norm_num) D (2*m+1) (by dsimp [m]; omega) _ hfactor
    have hcb := (mixed_exact 1 (1/3) (by norm_num) (by norm_num) (2*m+1) _).2 hlarge
    have hlow := (cubic_even_degree m hm ε (1/3) (by norm_num) (by norm_num)).1 hcb
    dsimp [ε] at hlow
    have hsmall : 0<4*((2*m:ℕ):ℝ)-4 := by linarith
    have hhalf : 1/(8*((2*m:ℕ):ℝ)-8) < 1/(4*((2*m:ℕ):ℝ)-4) := by
      exact one_div_lt_one_div_of_lt hsmall (by linarith)
    exact (not_lt_of_ge hlow) hhalf
  · obtain ⟨k,hk⟩ := exists_nat_gt (1/ε+1)
    have hk1 : 1≤k := by
      have hp : 0<ε⁻¹ := inv_pos.mpr hε
      by_contra h
      have hh : k=0 := by omega
      simp [hh] at hk
      linarith
    have hden' : 0<4*((2*k:ℕ):ℝ)-4 := by
      have h : (1:ℝ)≤(k:ℝ) := by exact_mod_cast hk1
      push_cast
      linarith
    have hlarge : 1/(4*((2*k:ℕ):ℝ)-4) ≤ ε := by
      apply (div_le_iff₀ hden').2
      have hh := (div_lt_iff₀ hε).1 (show 1/ε < (k:ℝ)-1 by linarith)
      push_cast
      nlinarith
    have hcb := (cubic_even_degree k hk1 ε (1/3) (by norm_num) (by norm_num)).2 hlarge
    have hp := (mixed_exact 1 (1/3) (by norm_num) (by norm_num) _ _).1 hcb
    exact ⟨2*k+1,(fixed_degree_exact 1 (1/3) (by norm_num) (by norm_num) _ _).2.mpr hp⟩

#print axioms cubic_even_degree
#print axioms cubic_odd_degree
#print axioms cubic_no_degree_two
#print axioms cubic_unbounded_degree_gap

end

theorem basis_scale (N t r : ℝ) (d i : ℕ) (hi : i≤d) :
    basis (r*N) d i (r*t) = r^d * basis N d i t := by
  unfold basis
  rw [show r*N-r*t=r*(N-t) by ring, mul_pow, mul_pow]
  calc
    _ = (r^i*r^(d-i))*(t^i*(N-t)^(d-i)) := by ring
    _ = _ := by rw [←pow_add, Nat.add_sub_of_le hi]

theorem rateField_scale (N t r : ℝ) (d : ℕ) (k : ℕ → ℕ → ℝ) :
    rateField (r*N) d k (r*t) = r^d * rateField N d k t := by
  unfold rateField
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [basis_scale N t r d i (by have := Finset.mem_range.mp hi; omega)]
  ring

open Polynomial in
theorem global_homogeneous_component (D q : ℕ) (v : ℕ → ℝ) (z : ℝ)
    (h : ∀ r>0, (∑ d ∈ Finset.range (D+1), r^d*v d) = r^q*z) :
    (if q≤D then v q else 0) = z := by
  let p : ℝ[X] := ∑ d ∈ Finset.range (D+1), C (v d)*X^d
  let s : ℝ[X] := C z * X^q
  have hps : p=s := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.Ioi_infinite (0:ℝ)).mono
    intro r hr
    change p.eval r = s.eval r
    simp only [p,s,Polynomial.eval_finset_sum,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_X]
    calc
      _ = ∑ d ∈ Finset.range (D+1), r^d*v d := by
        apply Finset.sum_congr rfl
        intro i hi
        ring
      _ = r^q*z := h r hr
      _ = _ := by ring
  have hp := congrArg (fun x : ℝ[X] => x.coeff q) hps
  by_cases hq : q≤D
  · have hm : q∈Finset.range (D+1) := Finset.mem_range.mpr (by omega)
    simpa [p,s,Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow,hq,hm] using hp
  · have hm : q∉Finset.range (D+1) := by simpa using hq
    simpa [p,s,Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul_X_pow,hq,hm] using hp

-- Global equality to the homogeneous degree-q extension means equality at every
-- scaled copy of the fixed simplex, with the SAME rates.
def GlobalHomogeneousCB (N a : ℝ) (D q : ℕ) (f : ℝ → ℝ) : Prop :=
  ∃ k : ℕ → ℕ → ℕ → ℝ, (∀ d i j, 0≤k d i j) ∧
    (∀ d≤D, bal d (fun i j => k d i j*basis N d i a)) ∧
    (∀ t, 0<t → t<N → ∀ r>0,
      mixedField (r*N) D k (r*t)=r^q*f t)

theorem global_homogeneous_extract (N a : ℝ) (D q : ℕ) (f : ℝ → ℝ)
    (hnz : ∃ t, 0<t ∧ t<N ∧ f t≠0)
    (h : GlobalHomogeneousCB N a D q f) :
    q≤D ∧ CBRealizable N a q f := by
  obtain ⟨k,hk,hbal,he⟩ := h
  have hc : ∀ t, 0<t → t<N →
      (if q≤D then rateField N q (k q) t else 0)=f t := by
    intro t ht htN
    apply global_homogeneous_component D q (fun d => rateField N d (k d) t)
    intro r hr
    simpa only [mixedField,rateField_scale] using he t ht htN r hr
  have hq : q≤D := by
    by_contra hh
    obtain ⟨t,ht,htN,hn⟩ := hnz
    exact hn (by simpa [hh] using (hc t ht htN).symm)
  exact ⟨hq,k q,hk q,hbal q hq,fun t ht htN => by simpa [hq] using hc t ht htN⟩

theorem cubic_global_fixed_separation (ε : ℝ) (he : 0<ε) (he4 : ε<1/4) :
    (∀ D, ¬ GlobalHomogeneousCB 1 (1/3) D 3 (fun t => (1/3-t)*quad ε t)) ∧
    (∃ M, DBRealizable 1 (1/3) M (fun t => (1/3-t)*quad ε t)) := by
  constructor
  · intro D h
    have hnz : ∃ t:ℝ, 0<t ∧ t<1 ∧ (1/3-t)*quad ε t≠0 := by
      refine ⟨1/2,by norm_num,by norm_num,?_⟩
      simp [quad]
      constructor <;> linarith
    obtain ⟨hq,hcb⟩ := global_homogeneous_extract 1 (1/3) D 3 _ hnz h
    have hf := (fixed_degree_exact 1 (1/3) (by norm_num) (by norm_num) 3 _).1.mp hcb
    have hm := (mixed_exact 1 (1/3) (by norm_num) (by norm_num) 3 _).2 hf
    have h4 := (cubic_even_degree 1 (by norm_num) ε (1/3) (by norm_num) (by norm_num)).1 hm
    norm_num at h4
    linarith
  · obtain ⟨m,hm⟩ := exists_nat_gt (1/ε+1)
    have hm1 : 1≤m := by
      have hp : 0<ε⁻¹ := inv_pos.mpr he
      by_contra h
      have h0 : m=0 := by omega
      simp [h0] at hm
      linarith
    have hmR : 1 < (m:ℝ) := by have := one_div_pos.mpr he; linarith
    have hd : 0<4*((2*m:ℕ):ℝ)-4 := by push_cast; linarith
    have hlarge : 1/(4*((2*m:ℕ):ℝ)-4) ≤ ε := by
      apply (div_le_iff₀ hd).2
      have hh := (div_lt_iff₀ he).1 (show 1/ε < (m:ℝ)-1 by linarith)
      push_cast
      nlinarith
    have hcb := (cubic_even_degree m hm1 ε (1/3) (by norm_num) (by norm_num)).2 hlarge
    exact ⟨2*m+1,(fixed_degree_exact 1 (1/3) (by norm_num) (by norm_num) _ _).2.mpr
      ((mixed_exact 1 (1/3) (by norm_num) (by norm_num) _ _).1 hcb)⟩

#print axioms global_homogeneous_extract
#print axioms cubic_global_fixed_separation

end FixedPopulation.Cuts

namespace FixedPopulation.Cuts

theorem mixed_cb_db_exact (N a : ℝ) (ha : 0<a) (haN : a<N)
    (D : ℕ) (f : ℝ → ℝ) :
    MixedCB N a D f ↔ DBRealizable N a D f :=
  (mixed_exact N a ha haN D f).trans (fixed_degree_exact N a ha haN D f).2.symm

theorem cubic_no_degree_two_general (ε a : ℝ) (ha : 0<a) (ha1 : a<1) :
    ¬PositiveFactor 1 a 2 (fun t => (a-t)*quad ε t) := by
  rintro ⟨c,hc,he⟩
  have hEq : ∀ t, a<t → t<1 →
      (∑ i ∈ Finset.range (2+1), elevateCoef 1 2 c i*basis 1 2 i t) =
      ∑ i ∈ Finset.range (2+1), (quadCoef 2 ε i*(Nat.choose 2 i:ℝ))*basis 1 2 i t := by
    intro t ht ht1
    have h := he t (lt_trans ha ht) ht1
    change (a-t)*quad ε t = (a-t)*(∑ i ∈ Finset.range 2, c i*basis 1 1 i t) at h
    have hcancel := (mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_lt ht)) h).symm
    have h1 := elevate_field_sum 1 t (by norm_num) 2 c (by norm_num)
    have hq := quad_expansion 2 (by norm_num) ε t
    have hsum : (∑ i ∈ Finset.range (2+1), (quadCoef 2 ε i*(Nat.choose 2 i:ℝ))*basis 1 2 i t) = quad ε t := by
      simpa [bern,mul_assoc] using hq
    rw [hsum, ← h1]
    exact hcancel
  have hu := basis_coeff_unique 1 a ha.le ha1 2 (elevateCoef 1 2 c)
    (fun i => quadCoef 2 ε i*(Nat.choose 2 i:ℝ)) hEq
  have h0 := hu 0 (by norm_num)
  have h1 := hu 1 (by norm_num)
  have h2 := hu 2 (by norm_num)
  norm_num [elevateCoef,quadCoef,Nat.choose] at h0 h1 h2
  linarith

theorem cubic_no_small_cap (ε a : ℝ) (ha : 0<a) (ha1 : a<1)
    (D : ℕ) (hD : D≤2) :
    ¬MixedCB 1 a D (fun t => (a-t)*quad ε t) := by
  intro hc
  have hf := (mixed_exact 1 a ha ha1 D _).1 hc
  have he := factor_monotone 1 a (by norm_num) D 2 hD _ hf
  exact cubic_no_degree_two_general ε a ha ha1 he

theorem cubic_finite_db (ε a : ℝ) (he : 0<ε) (ha : 0<a) (ha1 : a<1) :
    ∃ M, DBRealizable 1 a M (fun t => (a-t)*quad ε t) := by
  obtain ⟨m,hm⟩ := exists_nat_gt (1/ε+1)
  have hm1 : 1≤m := by
    have hp : 0<ε⁻¹ := inv_pos.mpr he
    by_contra h
    have h0 : m=0 := by omega
    simp [h0] at hm
    linarith
  have hmR : 1 < (m:ℝ) := by have := one_div_pos.mpr he; linarith
  have hd : 0<4*((2*m:ℕ):ℝ)-4 := by push_cast; linarith
  have hlarge : 1/(4*((2*m:ℕ):ℝ)-4) ≤ ε := by
    apply (div_le_iff₀ hd).2
    have hh := (div_lt_iff₀ he).1 (show 1/ε < (m:ℝ)-1 by linarith)
    push_cast
    nlinarith
  have hcb := (cubic_even_degree m hm1 ε a ha ha1).2 hlarge
  exact ⟨2*m+1,(mixed_cb_db_exact 1 a ha ha1 _ _).1 hcb⟩

theorem cubic_global_fixed_separation_general (ε a : ℝ)
    (he : 0<ε) (he4 : ε<1/4) (ha : 0<a) (ha1 : a<1) :
    (∀ D, ¬ GlobalHomogeneousCB 1 a D 3 (fun t => (a-t)*quad ε t)) ∧
    (∃ M, DBRealizable 1 a M (fun t => (a-t)*quad ε t)) := by
  constructor
  · intro D h
    have hnz : ∃ t:ℝ, 0<t ∧ t<1 ∧ (a-t)*quad ε t≠0 := by
      refine ⟨a/2,by linarith,by linarith,?_⟩
      apply ne_of_gt
      apply mul_pos (by linarith)
      unfold quad
      positivity
    obtain ⟨hq,hcb⟩ := global_homogeneous_extract 1 a D 3 _ hnz h
    have hf := (fixed_degree_exact 1 a ha ha1 3 _).1.mp hcb
    have hm := (mixed_exact 1 a ha ha1 3 _).2 hf
    have h4 := (cubic_even_degree 1 (by norm_num) ε a ha ha1).1 hm
    norm_num at h4
    linarith
  · exact cubic_finite_db ε a he ha ha1

#print axioms mixed_cb_db_exact
#print axioms cubic_no_degree_two_general
#print axioms cubic_no_small_cap
#print axioms cubic_finite_db
#print axioms cubic_global_fixed_separation_general
end FixedPopulation.Cuts
