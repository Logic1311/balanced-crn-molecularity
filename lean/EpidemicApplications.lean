import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open scoped BigOperators Topology
open Filter
namespace FixedPopulation

variable {V : Type*} [DecidableEq V]

inductive Path (E : Finset (V × V)) : V → V → Prop
  | refl (x) : Path E x x
  | tail {x y z} : Path E x y → (y,z) ∈ E → Path E x z

def WeaklyReversible (E : Finset (V × V)) : Prop :=
  ∀ e ∈ E, Path E e.2 e.1

theorem path_closed {E : Finset (V × V)} {P : V → Prop}
    {x y : V} (p : Path E x y) (hx : P x)
    (step : ∀ a b, (a,b) ∈ E → P a → P b) : P y := by
  induction p with
  | refl => exact hx
  | tail _ he ih => exact step _ _ he ih

def active (E : Finset (V × V)) (h : V → ℕ) : Finset (V × V) :=
  E.filter (fun e => h e.1 ≠ h e.2)

theorem active_mem {E : Finset (V × V)} {h : V → ℕ} {e : V × V} :
    e ∈ active E h ↔ e ∈ E ∧ h e.1 ≠ h e.2 := Finset.mem_filter

theorem min_edge_rises (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (m : ℕ)
    (low : ∀ e ∈ active E h, m ≤ h e.1)
    (e : V × V) (he : e ∈ active E h) (hm : h e.1 = m) :
    h e.1 < h e.2 := by
  have ha := active_mem.mp he
  by_contra hn
  have hb : h e.2 < m := by omega
  have step : ∀ a b, (a,b) ∈ E → h a < m → h b < m := by
    intro a b hab hlt
    by_contra hnot
    have hnab : h a ≠ h b := by omega
    have hc : m ≤ h a := low (a,b) (active_mem.mpr ⟨hab, hnab⟩)
    omega
  have hc := path_closed (wr e ha.1) hb step
  omega

theorem max_edge_falls (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (M : ℕ)
    (high : ∀ e ∈ active E h, h e.1 ≤ M)
    (e : V × V) (he : e ∈ active E h) (hm : h e.1 = M) :
    h e.2 < h e.1 := by
  have ha := active_mem.mp he
  by_contra hn
  have hb : M < h e.2 := by omega
  have step : ∀ a b, (a,b) ∈ E → M < h a → M < h b := by
    intro a b hab hlt
    by_contra hnot
    have hnab : h a ≠ h b := by omega
    have hc : h a ≤ M := high (a,b) (active_mem.mpr ⟨hab, hnab⟩)
    omega
  have hc := path_closed (wr e ha.1) hb step
  omega

theorem exists_low (E : Finset (V × V)) (h : V → ℕ)
    (ne : (active E h).Nonempty) :
    ∃ e ∈ active E h, ∀ a ∈ active E h, h e.1 ≤ h a.1 := by
  classical
  exact Finset.exists_min_image _ (fun e : V × V => h e.1) ne

theorem exists_high (E : Finset (V × V)) (h : V → ℕ)
    (ne : (active E h).Nonempty) :
    ∃ e ∈ active E h, ∀ a ∈ active E h, h a.1 ≤ h e.1 := by
  classical
  exact Finset.exists_max_image _ (fun e : V × V => h e.1) ne

def change (h : V → ℕ) (e : V × V) : ℝ :=
  (h e.2 : ℝ) - (h e.1 : ℝ)

def drift (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ e ∈ E, change h e * w e t * t ^ h e.1

theorem drift_active (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ → ℝ) (t : ℝ) :
    drift E h w t = ∑ e ∈ active E h, change h e * w e t * t ^ h e.1 := by
  classical
  rw [drift, active, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro e he
  split_ifs with hh
  · rfl
  · have hh' : h e.1 = h e.2 := not_ne_iff.mp hh
    simp [change, hh']

theorem drift_empty (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ → ℝ) (hn : active E h = ∅) (t : ℝ) :
    drift E h w t = 0 := by
  rw [drift_active, hn]
  simp

def lowFactor (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ → ℝ) (m : ℕ) (t : ℝ) : ℝ :=
  ∑ e ∈ active E h, change h e * w e t * t ^ (h e.1 - m)

theorem low_factor (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ → ℝ) (m : ℕ) (t : ℝ)
    (low : ∀ e ∈ active E h, m ≤ h e.1) :
    drift E h w t = t ^ m * lowFactor E h w m t := by
  rw [drift_active, lowFactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hh : h e.1 = m + (h e.1 - m) := by have := low e he; omega
  conv_lhs => rw [hh, pow_add]
  ring

theorem low_factor_pos (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (w : V × V → ℝ → ℝ) (m : ℕ)
    (low : ∀ e ∈ active E h, m ≤ h e.1)
    (hw : ∀ e ∈ active E h, 0 < w e 0)
    (e0 : V × V) (he0 : e0 ∈ active E h) (hm : h e0.1 = m) :
    0 < lowFactor E h w m 0 := by
  unfold lowFactor
  apply Finset.sum_pos'
  · intro e he
    by_cases hh : h e.1 = m
    · have hlt := min_edge_rises E h wr m low e he hh
      have hp : 0 < change h e := by unfold change; exact sub_pos.mpr (by exact_mod_cast hlt)
      rw [hh, Nat.sub_self, pow_zero, mul_one]
      exact (mul_pos hp (hw e he)).le
    · have hp : h e.1 - m ≠ 0 := by have := low e he; omega
      simp [zero_pow hp]
  · refine ⟨e0, he0, ?_⟩
    have hlt := min_edge_rises E h wr m low e0 he0 hm
    have hp : 0 < change h e0 := by unfold change; exact sub_pos.mpr (by exact_mod_cast hlt)
    rw [hm, Nat.sub_self, pow_zero, mul_one]
    exact mul_pos hp (hw e0 he0)

theorem eventually_positive (g : ℝ → ℝ)
    (hc : ContinuousAt g 0) (hp : 0 < g 0) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε → 0 < g t := by
  have hh : ∀ᶠ t in 𝓝 (0 : ℝ), g t ∈ Set.Ioi (0 : ℝ) :=
    hc (Ioi_mem_nhds hp)
  obtain ⟨ε, he, hn⟩ := Metric.eventually_nhds_iff.mp hh
  refine ⟨ε, he, ?_⟩
  intro t ht hlt
  apply hn
  simpa [Real.dist_eq, abs_of_pos ht] using hlt

theorem sum_cont_at_zero {A : Type*} (s : Finset A) (f : A → ℝ → ℝ)
    (hc : ∀ a ∈ s, ContinuousAt (f a) 0) :
    ContinuousAt (fun t => ∑ a ∈ s, f a t) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (0:ℝ)) 0)
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    apply ContinuousAt.add
    · exact hc a (Finset.mem_insert_self a s)
    · exact ih (fun b hb => hc b (Finset.mem_insert_of_mem hb))


theorem boundary_repulsion (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (w : V × V → ℝ → ℝ)
    (hc : ∀ e ∈ active E h, ContinuousAt (w e) 0)
    (hw : ∀ e ∈ active E h, 0 < w e 0)
    (ne : (active E h).Nonempty) :
    ∃ ε > 0, ∀ t, 0 < t → t < ε → 0 < drift E h w t := by
  obtain ⟨e0, he0, low⟩ := exists_low E h ne
  let m := h e0.1
  have hcont : ContinuousAt (lowFactor E h w m) 0 := by
    unfold lowFactor
    apply sum_cont_at_zero
    intro e he
    exact ((continuousAt_const.mul (hc e he)).mul (continuousAt_id.pow _))
  have hp := low_factor_pos E h wr w m low hw e0 he0 rfl
  obtain ⟨ε, hε, hh⟩ := eventually_positive _ hcont hp
  refine ⟨ε, hε, ?_⟩
  intro t ht hlt
  rw [low_factor E h w m t low]
  exact mul_pos (pow_pos ht _) (hh t ht hlt)

def highFactor (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ) (M : ℕ) (u : ℝ) : ℝ :=
  ∑ e ∈ active E h, change h e * w e * u ^ (M - h e.1)

theorem high_factor_neg (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (w : V × V → ℝ) (M : ℕ)
    (high : ∀ e ∈ active E h, h e.1 ≤ M)
    (hw : ∀ e ∈ active E h, 0 < w e)
    (e0 : V × V) (he0 : e0 ∈ active E h) (hm : h e0.1 = M) :
    highFactor E h w M 0 < 0 := by
  unfold highFactor
  apply Finset.sum_neg'
  · intro e he
    by_cases hh : h e.1 = M
    · have hlt := max_edge_falls E h wr M high e he hh
      have hp : change h e < 0 := by unfold change; exact sub_neg.mpr (by exact_mod_cast hlt)
      rw [hh, Nat.sub_self, pow_zero, mul_one]
      exact (mul_neg_of_neg_of_pos hp (hw e he)).le
    · have hp : M - h e.1 ≠ 0 := by have := high e he; omega
      simp [zero_pow hp]
  · refine ⟨e0, he0, ?_⟩
    have hlt := max_edge_falls E h wr M high e0 he0 hm
    have hp : change h e0 < 0 := by unfold change; exact sub_neg.mpr (by exact_mod_cast hlt)
    rw [hm, Nat.sub_self, pow_zero, mul_one]
    exact mul_neg_of_neg_of_pos hp (hw e0 he0)

theorem high_factor (E : Finset (V × V)) (h : V → ℕ)
    (w : V × V → ℝ) (M : ℕ) (t : ℝ) (ht : 0 < t)
    (high : ∀ e ∈ active E h, h e.1 ≤ M) :
    drift E h (fun e _ => w e) t = t ^ M * highFactor E h w M t⁻¹ := by
  rw [drift_active, highFactor, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e he
  have hh : M = h e.1 + (M - h e.1) := by have := high e he; omega
  have hp : t ^ M * (t⁻¹) ^ (M - h e.1) = t ^ h e.1 := by
    rw [inv_pow]
    calc
      _ = (t ^ h e.1 * t ^ (M - h e.1)) * (t ^ (M - h e.1))⁻¹ := by
        rw [← pow_add, Nat.add_sub_of_le (high e he)]
      _ = _ := by rw [mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht.ne'), mul_one]
  calc
    _ = (change h e * w e) * (t ^ M * (t⁻¹) ^ (M - h e.1)) := by rw [hp]
    _ = _ := by ring

theorem infinity_attraction (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (w : V × V → ℝ)
    (hw : ∀ e ∈ active E h, 0 < w e)
    (ne : (active E h).Nonempty) :
    ∃ B > 0, ∀ t, B < t → drift E h (fun e _ => w e) t < 0 := by
  obtain ⟨e0, he0, high⟩ := exists_high E h ne
  let M := h e0.1
  have hcont : ContinuousAt (highFactor E h w M) 0 := by
    unfold highFactor
    apply sum_cont_at_zero
    intro e he
    exact continuousAt_const.mul (continuousAt_id.pow _)
  have hn := high_factor_neg E h wr w M high hw e0 he0 rfl
  obtain ⟨ε, hε, hh⟩ := eventually_positive (fun x => -highFactor E h w M x) hcont.neg (neg_pos.mpr hn)
  refine ⟨ε⁻¹, inv_pos.mpr hε, ?_⟩
  intro t ht
  have ht0 := lt_trans (inv_pos.mpr hε) ht
  have hi : t⁻¹ < ε := by
    rw [← inv_inv ε]
    exact (inv_lt_inv₀ ht0 (inv_pos.mpr hε)).2 ht
  have hneg := neg_pos.mp (hh t⁻¹ (inv_pos.mpr ht0) hi)
  rw [high_factor E h w M t ht0 high]
  exact mul_neg_of_pos_of_neg (pow_pos ht0 _) hneg

-- Any affine projected epidemic drift with positive slope is impossible globally.
theorem global_no_go (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (w : V × V → ℝ)
    (hw : ∀ e ∈ active E h, 0 < w e)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ¬ (∀ t > 0, drift E h (fun e _ => w e) t = a + b*t) := by
  intro heq
  by_cases he : (active E h).Nonempty
  · obtain ⟨B, hB, hneg⟩ := infinity_attraction E h wr w hw he
    have ht : 0 < B + 1 := by linarith
    have h1 := hneg (B + 1) (by linarith)
    rw [heq _ ht] at h1
    have h2 : 0 < b*(B+1) := mul_pos hb ht
    linarith
  · have hEmpty : active E h = ∅ := Finset.not_nonempty_iff_eq_empty.mp he
    have h1 := heq 1 (by norm_num)
    rw [drift_empty E h _ hEmpty] at h1
    linarith

-- Negative drift at every sufficiently small positive parameter is impossible.
theorem boundary_no_go (E : Finset (V × V)) (h : V → ℕ)
    (wr : WeaklyReversible E) (w : V × V → ℝ → ℝ)
    (hc : ∀ e ∈ active E h, ContinuousAt (w e) 0)
    (hw : ∀ e ∈ active E h, 0 < w e 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ¬ (∀ t, 0 < t → t < δ → drift E h w t < 0) := by
  intro hneg
  by_cases he : (active E h).Nonempty
  · obtain ⟨ε, hε, hpos⟩ := boundary_repulsion E h wr w hc hw he
    let t := min ε δ / 2
    have ht : 0 < t := by dsimp [t]; positivity
    have hte : t < ε := by dsimp [t]; have := min_le_left ε δ; linarith
    have htd : t < δ := by dsimp [t]; have := min_le_right ε δ; linarith
    exact (not_lt_of_ge (hpos t ht hte).le) (hneg t ht htd)
  · have hEmpty := Finset.not_nonempty_iff_eq_empty.mp he
    have h1 := hneg (δ/2) (by linarith) (by linarith)
    rw [drift_empty E h _ hEmpty] at h1
    exact (lt_irrefl 0) h1

-- The reversible SIS pair is an exact conservative realization on S+I=N.
theorem sis_pair_identity (β γ N S I : ℝ) (hN : N > 0) (hs : S+I=N) :
    (β-γ/N)*S*I-(γ/N)*I^2 = β*S*I-γ*I := by
  field_simp [hN.ne']
  nlinarith [congrArg (fun z : ℝ => γ*I*z) hs]

theorem sis_pair_rates (β γ N : ℝ) (hN : N > 0) (hγ : γ > 0)
    (h : γ < β*N) :
    0 < β-γ/N ∧ 0 < γ/N := by
  exact ⟨sub_pos.mpr ((div_lt_iff₀ hN).mpr h), div_pos hγ hN⟩

theorem sis_nonpositive_threshold (β γ N I : ℝ)
    (hβ : 0 < β) (hI : 0 < I) (h : β*N ≤ γ) :
    β*(N-I)*I-γ*I < 0 := by
  have hp : 0 < β*I := mul_pos hβ hI
  have hn : β*(N-I)-γ < 0 := by linarith
  calc
    _ = (β*(N-I)-γ)*I := by ring
    _ < 0 := mul_neg_of_neg_of_pos hn hI

-- Construction at an interior source of a reversible homogeneous chain.
theorem interior_rates (c du dd : ℝ) (hu : 0 < du) (hd : 0 < dd) :
    ∃ ku kd : ℝ, 0 < ku ∧ 0 < kd ∧ ku*du-kd*dd=c := by
  refine ⟨(1+max c 0)/du, (1+max (-c) 0)/dd, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · field_simp [hu.ne', hd.ne']
    by_cases hc : 0 ≤ c
    · rw [max_eq_left hc, max_eq_right (by linarith : -c ≤ 0)]
      ring
    · rw [max_eq_right (le_of_not_ge hc), max_eq_left (by linarith : 0 ≤ -c)]
      ring

-- A detailed-balanced pair realizes one positive Bernstein summand.
theorem db_term_identity (a N S I b : ℝ) (hN : 0 < N) (hs : S+I=N) :
    b * ((a/N)*S - (1-a/N)*I) = b*(a-I) := by
  field_simp [hN.ne']
  nlinarith [congrArg (fun z : ℝ => b*a*z) hs]

theorem db_term_positive (a N b : ℝ) (ha : 0 < a) (hN : a < N) (hb : 0 < b) :
    0 < b*(a/N) ∧ 0 < b*(1-a/N) := by
  have hn : 0 < N := lt_trans ha hN
  exact ⟨mul_pos hb (div_pos ha hn), mul_pos hb (sub_pos.mpr ((div_lt_one hn).mpr hN))⟩

theorem db_term_balance (a N b : ℝ) (hN : 0 < N) :
    b*(a/N)*(N-a) = b*(1-a/N)*a := by
  field_simp [hN.ne']

#print axioms min_edge_rises
#print axioms max_edge_falls
#print axioms boundary_repulsion
#print axioms infinity_attraction
#print axioms global_no_go
#print axioms boundary_no_go
#print axioms sis_pair_identity
#print axioms interior_rates
#print axioms db_term_identity

abbrev Complex (n : ℕ) := Fin n → ℕ
def height {n : ℕ} (J : Finset (Fin n)) (y : Complex n) : ℕ :=
  ∑ j ∈ J, y j
def monomial {n : ℕ} (x : Fin n → ℝ) (y : Complex n) : ℝ :=
  ∏ j, x j ^ y j
def field {n : ℕ} (E : Finset (Complex n × Complex n))
    (k : Complex n × Complex n → ℝ) (x : Fin n → ℝ) (j : Fin n) : ℝ :=
  ∑ e ∈ E, k e * monomial x e.1 * ((e.2 j : ℝ) - (e.1 j : ℝ))
def projection {n : ℕ} (E : Finset (Complex n × Complex n))
    (k : Complex n × Complex n → ℝ) (J : Finset (Fin n)) (x : Fin n → ℝ) : ℝ :=
  ∑ j ∈ J, field E k x j

theorem projection_eq {n : ℕ} (E : Finset (Complex n × Complex n))
    (k : Complex n × Complex n → ℝ) (J : Finset (Fin n)) (x : Fin n → ℝ) :
    projection E k J x = ∑ e ∈ E, change (height J) e * k e * monomial x e.1 := by
  unfold projection field
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  rw [← Finset.mul_sum]
  simp only [change, height, Nat.cast_sum, Finset.sum_sub_distrib]
  ring

def rayBase {n : ℕ} (J : Finset (Fin n)) (a : Fin n → ℝ)
    (b : Fin n → ℝ → ℝ) (j : Fin n) (t : ℝ) : ℝ :=
  if j ∈ J then a j else b j t

def ray {n : ℕ} (J : Finset (Fin n)) (a : Fin n → ℝ)
    (b : Fin n → ℝ → ℝ) (t : ℝ) (j : Fin n) : ℝ :=
  if j ∈ J then t * a j else b j t

theorem ray_monomial {n : ℕ} (J : Finset (Fin n)) (a : Fin n → ℝ)
    (b : Fin n → ℝ → ℝ) (t : ℝ) (y : Complex n) :
    monomial (ray J a b t) y =
      (∏ j, rayBase J a b j t ^ y j) * t ^ height J y := by
  have H : ∀ j : Fin n, ray J a b t j ^ y j =
      rayBase J a b j t ^ y j * (if j ∈ J then t ^ y j else 1) := by
    intro j
    by_cases hj : j ∈ J
    · simp [ray, rayBase, hj, mul_pow, mul_comm]
    · simp [ray, rayBase, hj]
  unfold monomial
  simp_rw [H]
  rw [Finset.prod_mul_distrib, ← Finset.prod_filter]
  have hh : (Finset.univ.filter (fun j : Fin n => j ∈ J)) = J := by ext j; simp
  rw [hh, Finset.prod_pow_eq_pow_sum]
  rfl

theorem projection_ray {n : ℕ} (E : Finset (Complex n × Complex n))
    (k : Complex n × Complex n → ℝ) (J : Finset (Fin n)) (a : Fin n → ℝ)
    (b : Fin n → ℝ → ℝ) (t : ℝ) :
    projection E k J (ray J a b t) =
      drift E (height J) (fun e u => k e * ∏ j, rayBase J a b j u ^ e.1 j) t := by
  rw [projection_eq]
  unfold drift
  apply Finset.sum_congr rfl
  intro e he
  rw [ray_monomial]
  ring

theorem prod_cont_at_zero {A : Type*} (s : Finset A) (f : A → ℝ → ℝ)
    (hc : ∀ a ∈ s, ContinuousAt (f a) 0) :
    ContinuousAt (fun t => ∏ a ∈ s, f a t) 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (continuousAt_const : ContinuousAt (fun _ : ℝ => (1:ℝ)) 0)
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    apply ContinuousAt.mul
    · exact hc a (Finset.mem_insert_self a s)
    · exact ih (fun b hb => hc b (Finset.mem_insert_of_mem hb))

theorem massAction_boundary_no_go {n : ℕ} (E : Finset (Complex n × Complex n))
    (k : Complex n × Complex n → ℝ) (J : Finset (Fin n))
    (a : Fin n → ℝ) (b : Fin n → ℝ → ℝ) (wr : WeaklyReversible E)
    (hk : ∀ e ∈ E, 0 < k e) (ha : ∀ j ∈ J, 0 < a j)
    (hb : ∀ j ∉ J, 0 < b j 0) (hc : ∀ j ∉ J, ContinuousAt (b j) 0)
    (δ : ℝ) (hδ : 0 < δ) :
    ¬ (∀ t, 0 < t → t < δ → projection E k J (ray J a b t) < 0) := by
  let w := fun (e : Complex n × Complex n) (u : ℝ) => k e * ∏ j, rayBase J a b j u ^ e.1 j
  have hcw : ∀ e ∈ active E (height J), ContinuousAt (w e) 0 := by
    intro e he
    apply continuousAt_const.mul
    apply prod_cont_at_zero
    intro j hj
    have hcb : ContinuousAt (fun t => rayBase J a b j t) 0 := by
      by_cases hJ : j ∈ J
      · simpa [rayBase, hJ] using (continuousAt_const : ContinuousAt (fun _ : ℝ => a j) 0)
      · simpa [rayBase, hJ] using hc j hJ
    exact hcb.pow _
  have hpw : ∀ e ∈ active E (height J), 0 < w e 0 := by
    intro e he
    apply mul_pos (hk e ((Finset.mem_filter.mp he).1))
    apply Finset.prod_pos
    intro j hj
    apply pow_pos
    by_cases hJ : j ∈ J
    · simpa [rayBase, hJ] using ha j hJ
    · simpa [rayBase, hJ] using hb j hJ
  intro H
  apply boundary_no_go E (height J) wr w hcw hpw δ hδ
  intro t ht htd
  rw [← projection_ray]
  exact H t ht htd

theorem massAction_global_no_go {n : ℕ} (E : Finset (Complex n × Complex n))
    (k : Complex n × Complex n → ℝ) (J : Finset (Fin n))
    (a b : Fin n → ℝ) (wr : WeaklyReversible E)
    (hk : ∀ e ∈ E, 0 < k e) (ha : ∀ j ∈ J, 0 < a j)
    (hb : ∀ j ∉ J, 0 < b j)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 < B) :
    ¬ (∀ t > 0, projection E k J (ray J a (fun j _ => b j) t) = A+B*t) := by
  let w := fun (e : Complex n × Complex n) =>
    k e * ∏ j, rayBase J a (fun j _ => b j) j 0 ^ e.1 j
  have hpw : ∀ e ∈ active E (height J), 0 < w e := by
    intro e he
    apply mul_pos (hk e ((Finset.mem_filter.mp he).1))
    apply Finset.prod_pos
    intro j hj
    apply pow_pos
    by_cases hJ : j ∈ J
    · simpa [rayBase, hJ] using ha j hJ
    · simpa [rayBase, hJ] using hb j hJ
  intro H
  apply global_no_go E (height J) wr w hpw A B hA hB
  intro t ht
  have hh := projection_ray E k J a (fun j _ => b j) t
  rw [H t ht] at hh
  simpa [w, rayBase] using hh.symm

#print axioms projection_ray
#print axioms massAction_boundary_no_go
#print axioms massAction_global_no_go


-- Explicit applications: arbitrary competitors, not just the displayed reaction graph.
theorem sis_global_obstruction (β γ : ℝ) (hβ : 0<β) (hγ : 0<γ)
    (E : Finset (Complex 2 × Complex 2)) (k : Complex 2 × Complex 2 → ℝ)
    (wr : WeaklyReversible E) (hk : ∀ e ∈ E, 0<k e) :
    ¬ (∀ x : Fin 2 → ℝ, (∀ j, 0<x j) →
      field E k x 1 = β*x 0*x 1-γ*x 1) := by
  let B := (γ+1)/β
  have hB : 0<B := by dsimp [B]; positivity
  let J : Finset (Fin 2) := {1}
  let a : Fin 2 → ℝ := fun _ => 1
  let b : Fin 2 → ℝ := fun _ => B
  have hA : ∀ j ∈ J, 0<a j := by simp [a]
  have hC : ∀ j ∉ J, 0<b j := by simp [b,hB]
  intro heq
  apply massAction_global_no_go E k J a b wr hk hA hC 0 1 (by norm_num) (by norm_num)
  intro t ht
  have hx : ∀ j : Fin 2, 0<ray J a (fun j _ => b j) t j := by
    intro j; fin_cases j <;> simp [J,a,b,ray,ht,hB]
  have hh := heq _ hx
  have hbβ : β*B=γ+1 := by dsimp [B]; field_simp <;> ring
  simpa [projection,J,a,b,ray,hbβ] using (show field E k (ray J a (fun j _ => b j) t) 1 = 0+1*t from by
    rw [hh]
    have h0 : ray J a (fun j _ => b j) t 0=B := by simp [ray,J,a,b]
    have h1 : ray J a (fun j _ => b j) t 1=t := by simp [ray,J,a,b]
    rw [h0,h1,hbβ]; ring)

theorem sis_below_threshold_obstruction (β γ N : ℝ) (hβ : 0<β) (hN : 0<N)
    (hle : β*N≤γ)
    (E : Finset (Complex 2 × Complex 2)) (k : Complex 2 × Complex 2 → ℝ)
    (wr : WeaklyReversible E) (hk : ∀ e ∈ E, 0<k e) :
    ¬ (∀ t, 0<t → t<N → field E k (![N-t,t] : Fin 2 → ℝ) 1 =
      β*(N-t)*t-γ*t) := by
  let J : Finset (Fin 2) := {1}
  let a : Fin 2 → ℝ := fun _ => 1
  let b : Fin 2 → ℝ → ℝ := fun _ t => N-t
  have hA : ∀ j ∈ J, 0<a j := by simp [a]
  have hB : ∀ j ∉ J, 0<b j 0 := by simp [b,hN]
  have hc : ∀ j ∉ J, ContinuousAt (b j) 0 := by
    intro j hj; dsimp [b]; fun_prop
  intro heq
  apply massAction_boundary_no_go E k J a b wr hk hA hB hc N hN
  intro t ht htN
  have hv : ray J a b t = (![N-t,t] : Fin 2 → ℝ) := by
    ext j; fin_cases j <;> simp [ray,J,a,b]
  rw [hv]
  simpa [projection,J,heq t ht htN] using sis_nonpositive_threshold β γ N t hβ ht hle

theorem sir_sirs_obstruction (β γ N : ℝ) (hβ : 0<β) (hγ : 0<γ) (hN : 0<N)
    (E : Finset (Complex 3 × Complex 3)) (k : Complex 3 × Complex 3 → ℝ)
    (wr : WeaklyReversible E) (hk : ∀ e ∈ E, 0<k e) :
    ¬ (∀ S I R : ℝ, 0<S → 0<I → 0<R → S+I+R=N →
      field E k (![S,I,R] : Fin 3 → ℝ) 1 = β*S*I-γ*I) := by
  let S := min (N/2) (γ/(2*β))
  have hS : 0<S := by dsimp [S]; positivity
  have hSN : S<N := by
    have h : S≤N/2 := min_le_left _ _
    linarith
  have hSβ : β*S<γ := by
    have h : S≤γ/(2*β) := min_le_right _ _
    have hh := (le_div_iff₀ (show 0<2*β by positivity)).1 h
    nlinarith
  let J : Finset (Fin 3) := {1}
  let a : Fin 3 → ℝ := fun _ => 1
  let b : Fin 3 → ℝ → ℝ := fun j t => if j=0 then S else N-S-t
  have hA : ∀ j ∈ J, 0<a j := by simp [a]
  have hB : ∀ j ∉ J, 0<b j 0 := by
    intro j hj; dsimp [b]; split_ifs <;> linarith
  have hc : ∀ j ∉ J, ContinuousAt (b j) 0 := by
    intro j hj; dsimp [b]; split_ifs <;> fun_prop
  intro heq
  apply massAction_boundary_no_go E k J a b wr hk hA hB hc (N-S) (sub_pos.mpr hSN)
  intro t ht htN
  have hR : 0<N-S-t := by linarith
  have hv : ray J a b t = (![S,t,N-S-t] : Fin 3 → ℝ) := by
    ext j; fin_cases j <;> simp [ray,J,a,b]
  rw [hv]
  have hh := heq S t (N-S-t) hS ht hR (by ring)
  have hn : β*S*t-γ*t<0 := by
    have hm := mul_neg_of_neg_of_pos (sub_neg.mpr hSβ) ht
    nlinarith
  simpa [projection,J,hh] using hn

def sisSource : Complex 2 := ![1,1]
def sisTarget : Complex 2 := ![0,2]
def sisEdges : Finset (Complex 2 × Complex 2) :=
  {(sisSource,sisTarget),(sisTarget,sisSource)}
noncomputable def sisK (β γ N : ℝ) (e : Complex 2 × Complex 2) : ℝ :=
  if e=(sisSource,sisTarget) then β-γ/N else γ/N

theorem sis_source_target_ne : sisSource≠sisTarget := by
  intro h
  have hh := congrFun h (0:Fin 2)
  norm_num [sisSource,sisTarget] at hh

theorem sisEdges_wr : WeaklyReversible sisEdges := by
  intro e he
  simp only [sisEdges,Finset.mem_insert,Finset.mem_singleton] at he
  rcases he with h|h
  · subst e; exact Path.tail (Path.refl _) (by simp [sisEdges])
  · subst e; exact Path.tail (Path.refl _) (by simp [sisEdges])

theorem sisK_pos (β γ N : ℝ) (hN : 0<N) (hγ : 0<γ) (h : γ<β*N) :
    ∀ e ∈ sisEdges, 0<sisK β γ N e := by
  intro e he
  have hp := sis_pair_rates β γ N hN hγ h
  by_cases hh : e=(sisSource,sisTarget)
  · simpa [sisK,hh] using hp.1
  · simpa [sisK,hh] using hp.2

theorem sisEdges_field (β γ N S I : ℝ) (hN : 0<N) (hS : S+I=N) :
    field sisEdges (sisK β γ N) (![S,I] : Fin 2 → ℝ) 1 = β*S*I-γ*I ∧
    field sisEdges (sisK β γ N) (![S,I] : Fin 2 → ℝ) 0 = -(β*S*I-γ*I) := by
  have h1 : (sisSource,sisTarget)≠(sisTarget,sisSource) := by
    intro h; exact sis_source_target_ne (congrArg Prod.fst h)
  have h2 := Ne.symm h1
  have hid := sis_pair_identity β γ N S I hN hS
  constructor <;>
    simp [field,sisEdges,sisK,h1,h2,monomial,Fin.prod_univ_two,sisSource,sisTarget] <;>
    linarith

theorem sis_threshold_exact (β γ N : ℝ) (hβ : 0<β) (hγ : 0<γ) (hN : 0<N) :
    (∃ E : Finset (Complex 2 × Complex 2), ∃ k : Complex 2 × Complex 2 → ℝ,
      WeaklyReversible E ∧ (∀ e ∈ E, 0<k e) ∧
      (∀ t, 0<t → t<N →
        field E k (![N-t,t] : Fin 2 → ℝ) 1 = β*(N-t)*t-γ*t ∧
        field E k (![N-t,t] : Fin 2 → ℝ) 0 = -(β*(N-t)*t-γ*t))) ↔ γ<β*N := by
  constructor
  · rintro ⟨E,k,wr,hk,heq⟩
    by_contra hn
    exact sis_below_threshold_obstruction β γ N hβ hN (le_of_not_gt hn) E k wr hk
      (fun t ht htN => (heq t ht htN).1)
  · intro h
    refine ⟨sisEdges,sisK β γ N,sisEdges_wr,sisK_pos β γ N hN hγ h,?_⟩
    intro t ht htN
    exact sisEdges_field β γ N (N-t) t hN (by ring)

#print axioms sis_global_obstruction
#print axioms sir_sirs_obstruction
#print axioms sis_threshold_exact

end FixedPopulation
