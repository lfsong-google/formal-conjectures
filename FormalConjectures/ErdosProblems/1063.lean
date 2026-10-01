/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import Mathlib
set_option maxHeartbeats 4000000

/-!
# Erdős Problem 1063

*References:*
 * erdosproblems.com/1063
 * Erdos, P. and Selfridge, J. L., Problem 6447. Amer. Math. Monthly 1983, 710.
 * Guy, Richard K., Unsolved problems in number theory. 2004, Problem B31.
 * Monier, Jean-Marie, Problems and Solutions: Solutions of Advanced Problems: 6447.
   Amer. Math. Monthly 92, 1985, 435-436.
-/

open Filter Real
open scoped Nat Topology

namespace Erdos1063

/--
Let $n_k$ be the least $n \ge 2k$ such that all but one of the integers $n - i$ with
$0 \le i < k$ divide $\binom{n}{k}$.
-/
noncomputable def n (k : ℕ) : ℕ :=
  sInf {m | 2 * k ≤ m ∧ ∃ i0 < k, ¬ (m - i0) ∣ m.choose k ∧
    ∀ i < k, i ≠ i0 → (m - i) ∣ m.choose k}

/-- The initial values satisfy $n_2 = 4$, $n_3 = 6$, $n_4 = 9$, and $n_5 = 12$. -/
theorem erdos_1063.variants.small_values :
    n 2 = 4 ∧ n 3 = 6 ∧ n 4 = 9 ∧ n 5 = 12 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨4, by decide⟩
      rintro b hb
      have : 2 * 2 ≤ b := hb.1
      omega
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨6, by decide⟩
      rintro b hb
      have : 2 * 3 ≤ b := hb.1
      omega
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨9, by decide⟩
      rintro b hb
      have hb8 : 8 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
  · apply le_antisymm
    · exact Nat.sInf_le (by decide)
    · apply le_csInf ⟨12, by decide⟩
      rintro b hb
      have hb10 : 10 ≤ b := by have := hb.1; omega
      by_contra! h
      interval_cases b
      · exact absurd hb (by decide)
      · exact absurd hb (by decide)

/--
Combined statement of Erdős Problem 1063 (`erdos_1063.better_upper`) and its four companion
theorems (`exists_exception`, `monier_upper_bound`, `cambie_upper_bound`, `exp_upper_bound`).
-/

theorem exists_exception {n_val k : ℕ} (hk : 2 ≤ k) (hn : 2 * k ≤ n_val) :
    ∃ i < k, ¬ (n_val - i) ∣ n_val.choose k :=
by
  have choose_mul_choose_split : ∀ {n k i0 : ℕ}, i0 < k → k ≤ n →
      n.choose k * k * (k - 1).choose i0 =
        (n - i0) * n.choose i0 * (n - i0 - 1).choose (k - 1 - i0) := by
    intro n k i0 hi0 hkn
    have h1 : k * (k - 1).choose i0 = k.choose i0 * (k - i0) := by
      have h1a := Nat.add_one_mul_choose_eq (k - 1) (k - 1 - i0)
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 - i0 + 1 = k - i0 := by omega
      rw [hk1, hk2] at h1a
      rw [Nat.choose_symm (by omega : i0 ≤ k - 1), Nat.choose_symm (by omega : i0 ≤ k)] at h1a
      exact h1a
    have h2 : (n - i0) * (n - i0 - 1).choose (k - 1 - i0) = (n - i0).choose (k - i0) * (k - i0) := by
      have h2a := Nat.add_one_mul_choose_eq (n - i0 - 1) (k - 1 - i0)
      have hn1 : n - i0 - 1 + 1 = n - i0 := by omega
      have hk2 : k - 1 - i0 + 1 = k - i0 := by omega
      rw [hn1, hk2] at h2a
      exact h2a
    have h3 : n.choose k * k.choose i0 = n.choose i0 * (n - i0).choose (k - i0) :=
      Nat.choose_mul (by omega : i0 ≤ k)
    calc n.choose k * k * (k - 1).choose i0
      _ = n.choose k * (k * (k - 1).choose i0) := by ring
      _ = n.choose k * (k.choose i0 * (k - i0)) := by rw [h1]
      _ = (n.choose k * k.choose i0) * (k - i0) := by ring
      _ = (n.choose i0 * (n - i0).choose (k - i0)) * (k - i0) := by rw [h3]
      _ = n.choose i0 * ((n - i0).choose (k - i0) * (k - i0)) := by ring
      _ = n.choose i0 * ((n - i0) * (n - i0 - 1).choose (k - 1 - i0)) := by rw [← h2]
      _ = (n - i0) * n.choose i0 * (n - i0 - 1).choose (k - 1 - i0) := by ring
  have padicValNat_add_choose_eq_zero : ∀ {p M r : ℕ} [Fact p.Prime], 0 < M →
      (∀ j : ℕ, 1 ≤ j → j ≤ r → padicValNat p (M + j) ≤ padicValNat p M) →
      padicValNat p ((M + r).choose r) = 0 := by
    intro p M r _ hM hmax
    induction r with
    | zero => simp
    | succ r ih =>
      change padicValNat p ((M + r + 1).choose (r + 1)) = 0
      have ih' : padicValNat p ((M + r).choose r) = 0 :=
        ih (fun j hj1 hjr => hmax j hj1 (by omega))
      have habs : (M + r + 1) * (M + r).choose r = (M + r + 1).choose (r + 1) * (r + 1) :=
        Nat.add_one_mul_choose_eq (M + r) r
      have hpos1 : (M + r).choose r ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hpos2 : (M + r + 1).choose (r + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hval := congrArg (padicValNat p) habs
      rw [padicValNat.mul (by omega) hpos1, padicValNat.mul hpos2 (by omega)] at hval
      have hle : padicValNat p (M + r + 1) ≤ padicValNat p (r + 1) := by
        have hm := hmax (r + 1) (by omega) (by omega)
        have hdvd1 : p ^ padicValNat p (M + r + 1) ∣ M + r + 1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (le_refl _)
        have hdvd2 : p ^ padicValNat p (M + r + 1) ∣ M :=
          (padicValNat_dvd_iff_le (by omega)).mpr hm
        have hdvd3 : p ^ padicValNat p (M + r + 1) ∣ (M + r + 1) - M :=
          Nat.dvd_sub hdvd1 hdvd2
        have hsub : M + r + 1 - M = r + 1 := by omega
        rw [hsub] at hdvd3
        exact (padicValNat_dvd_iff_le (by omega)).mp hdvd3
      omega
  have padicValNat_pred_choose_eq_zero : ∀ {p M s : ℕ} [Fact p.Prime], s < M →
      (∀ j : ℕ, 1 ≤ j → j ≤ s → padicValNat p (M - j) ≤ padicValNat p M) →
      padicValNat p ((M - 1).choose s) = 0 := by
    intro p M s _ hsM hmax
    induction s with
    | zero => simp
    | succ s ih =>
      have ih' : padicValNat p ((M - 1).choose s) = 0 :=
        ih (by omega) (fun j hj1 hjs => hmax j hj1 (by omega))
      have habs : (M - 1).choose (s + 1) * (s + 1) = (M - 1).choose s * (M - 1 - s) :=
        Nat.choose_succ_right_eq (M - 1) s
      have hsub1 : M - 1 - s = M - (s + 1) := by omega
      rw [hsub1] at habs
      have hpos1 : (M - 1).choose (s + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hpos2 : (M - 1).choose s ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hval := congrArg (padicValNat p) habs
      rw [padicValNat.mul hpos1 (by omega), padicValNat.mul hpos2 (by omega)] at hval
      have hle : padicValNat p (M - (s + 1)) ≤ padicValNat p (s + 1) := by
        have hm := hmax (s + 1) (by omega) (by omega)
        have hdvd1 : p ^ padicValNat p (M - (s + 1)) ∣ M - (s + 1) :=
          (padicValNat_dvd_iff_le (by omega)).mpr (le_refl _)
        have hdvd2 : p ^ padicValNat p (M - (s + 1)) ∣ M :=
          (padicValNat_dvd_iff_le (by omega)).mpr hm
        have hdvd3 : p ^ padicValNat p (M - (s + 1)) ∣ M - (M - (s + 1)) :=
          Nat.dvd_sub hdvd2 hdvd1
        have hsub2 : M - (M - (s + 1)) = s + 1 := by omega
        rw [hsub2] at hdvd3
        exact (padicValNat_dvd_iff_le (by omega)).mp hdvd3
      omega
  let p := k.minFac
  have hp_prime : p.Prime := Nat.minFac_prime (by omega)
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hp_dvd : p ∣ k := Nat.minFac_dvd k
  have hvp_k : 1 ≤ padicValNat p k := by
    have hdvd : p ^ 1 ∣ k := by simpa using hp_dvd
    exact (padicValNat_dvd_iff_le (by omega)).mp hdvd
  have hne : (Finset.range k).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
  obtain ⟨i0, hi0_mem, hi0_max⟩ :=
    Finset.exists_max_image (Finset.range k) (fun i => padicValNat p (n_val - i)) hne
  have hi0 : i0 < k := Finset.mem_range.mp hi0_mem
  refine ⟨i0, hi0, ?_⟩
  set M := n_val - i0
  have hM_pos : 0 < M := by omega
  have h_add_zero : padicValNat p (n_val.choose i0) = 0 := by
    have hMi0 : M + i0 = n_val := by omega
    rw [← hMi0]
    apply padicValNat_add_choose_eq_zero hM_pos
    intro j hj1 hjr
    have hMj : M + j = n_val - (i0 - j) := by omega
    rw [hMj]
    exact hi0_max (i0 - j) (Finset.mem_range.mpr (by omega))
  have h_pred_zero : padicValNat p ((n_val - i0 - 1).choose (k - 1 - i0)) = 0 := by
    change padicValNat p ((M - 1).choose (k - 1 - i0)) = 0
    apply padicValNat_pred_choose_eq_zero (by omega)
    intro j hj1 hjs
    have hMj : M - j = n_val - (i0 + j) := by omega
    rw [hMj]
    exact hi0_max (i0 + j) (Finset.mem_range.mpr (by omega))
  have hsplit := choose_mul_choose_split hi0 (by omega : k ≤ n_val)
  have hpos_nk : n_val.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpos_k1 : (k - 1).choose i0 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpos_ni0 : n_val.choose i0 ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hpos_rem : (n_val - i0 - 1).choose (k - 1 - i0) ≠ 0 := (Nat.choose_pos (by omega)).ne'
  have hval := congrArg (padicValNat p) hsplit
  rw [padicValNat.mul (Nat.mul_ne_zero hpos_nk (by omega)) hpos_k1,
      padicValNat.mul hpos_nk (by omega),
      padicValNat.mul (Nat.mul_ne_zero (by omega) hpos_ni0) hpos_rem,
      padicValNat.mul (by omega) hpos_ni0] at hval
  intro hdvd
  have hdvd_pow : p ^ padicValNat p (n_val - i0) ∣ n_val.choose k :=
    dvd_trans ((padicValNat_dvd_iff_le (by omega)).mpr (le_refl _)) hdvd
  have hle : padicValNat p (n_val - i0) ≤ padicValNat p (n_val.choose k) :=
    (padicValNat_dvd_iff_le hpos_nk).mp hdvd_pow
  omega

theorem cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id :=
by
  have hW_ne_zero : ∀ m : ℕ, (Finset.Icc 1 m).lcm id ≠ 0 := by
    intro m hm
    rw [Finset.lcm_eq_zero_iff] at hm
    rcases hm with ⟨x, hx, hx0⟩
    simp only [Finset.mem_Icc, id_eq] at hx hx0
    omega
  set W := (Finset.Icc 1 (k - 1)).lcm id
  set N := k * W
  have h2_mem : (2 : ℕ) ∈ Finset.Icc 1 (k - 1) := by
    rw [Finset.mem_Icc]
    omega
  have h2_dvd_W : 2 ∣ W := Finset.dvd_lcm h2_mem
  have hW_pos : 0 < W := Nat.pos_of_ne_zero (hW_ne_zero (k - 1))
  have h2_le_W : 2 ≤ W := Nat.le_of_dvd hW_pos h2_dvd_W
  have h2k_le_N : 2 * k ≤ N := by
    calc 2 * k = k * 2 := Nat.mul_comm 2 k
      _ ≤ k * W := Nat.mul_le_mul_left k h2_le_W
  have hk_le_N : k ≤ N := by omega
  have hN_choose : N.choose k = W * (N - 1).choose (k - 1) := by
    have h1 := Nat.add_one_mul_choose_eq (N - 1) (k - 1)
    have hN1 : N - 1 + 1 = N := by omega
    have hk1 : k - 1 + 1 = k := by omega
    rw [hN1, hk1] at h1
    have h2 : N.choose k * k = (W * (N - 1).choose (k - 1)) * k := by
      rw [← h1]
      change (k * W) * (N - 1).choose (k - 1) = (W * (N - 1).choose (k - 1)) * k
      ring
    exact Nat.eq_of_mul_eq_mul_right (by omega : 0 < k) h2
  have h_dvd_pos : ∀ i < k, i ≠ 0 → (N - i) ∣ N.choose k := by
    intro i hi_lt hi_ne
    have hi_ge : 1 ≤ i := by omega
    set m := k - 1
    have hi_le_m : i ≤ m := by omega
    have hm_pos : 1 ≤ m := by omega
    have h_choose_pos : 0 < m.choose i := Nat.choose_pos hi_le_m
    set A := i * m.choose i
    have hA_pos : 0 < A := Nat.mul_pos (by omega) h_choose_pos
    have hA_ne_zero : A ≠ 0 := by omega
    have hW_ne_zero' : W ≠ 0 := hW_ne_zero m
    have hA_dvd_W : A ∣ W := by
      rw [← Nat.factorization_le_iff_dvd hA_ne_zero hW_ne_zero']
      intro p
      by_cases hp : p.Prime
      · haveI : Fact p.Prime := ⟨hp⟩
        rw [Nat.factorization_def A hp, Nat.factorization_def W hp]
        rw [← padicValNat_dvd_iff_le hW_ne_zero']
        set v := padicValNat p i
        set e := padicValNat p (m.choose i)
        set h := Nat.log p m
        have h_val_A : padicValNat p A = v + e :=
          padicValNat.mul (by omega) (by omega)
        have hp_gt_one : 1 < p := hp.one_lt
        have hv_dvd : p ^ v ∣ i := pow_padicValNat_dvd
        have hpv_le_i : p ^ v ≤ i := Nat.le_of_dvd (by omega) hv_dvd
        have hv_le_h : v ≤ h := Nat.le_log_of_pow_le hp_gt_one (by omega)
        have he_eq : e = {a ∈ Finset.Ico 1 (h + 1) | p ^ a ≤ i % p ^ a + (m - i) % p ^ a}.card :=
          padicValNat_choose hi_le_m (Nat.lt_succ_self h)
        have h_sub_Ico : {a ∈ Finset.Ico 1 (h + 1) | p ^ a ≤ i % p ^ a + (m - i) % p ^ a} ⊆
            Finset.Ico (v + 1) (h + 1) := by
          intro a ha
          simp only [Finset.mem_filter, Finset.mem_Ico] at ha ⊢
          refine ⟨?_, ha.1.2⟩
          by_contra! ha_le
          have hpa_dvd_pv : p ^ a ∣ p ^ v := Nat.pow_dvd_pow p (by omega)
          have hpa_dvd_i : p ^ a ∣ i := dvd_trans hpa_dvd_pv hv_dvd
          have hi_mod : i % p ^ a = 0 := Nat.mod_eq_zero_of_dvd hpa_dvd_i
          have hpa_pos : 0 < p ^ a := pow_pos hp.pos a
          have hmi_mod : (m - i) % p ^ a < p ^ a := Nat.mod_lt (m - i) hpa_pos
          omega
        have he_le : e ≤ h - v := by
          have h_card := Finset.card_le_card h_sub_Ico
          rw [Nat.card_Ico, ← he_eq] at h_card
          omega
        have hve_le_h : v + e ≤ h := by omega
        have hp_pow_le_m : p ^ (v + e) ≤ m := by
          calc p ^ (v + e) ≤ p ^ h := Nat.pow_le_pow_right hp.pos hve_le_h
            _ ≤ m := Nat.pow_log_le_self p (by omega)
        have hp_pow_pos : 1 ≤ p ^ (v + e) := Nat.one_le_pow (v + e) p hp.pos
        rw [h_val_A]
        exact Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hp_pow_pos, hp_pow_le_m⟩)
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
    rcases hA_dvd_W with ⟨Q, hQ⟩
    have hi_choose : A = (k - 1).choose (i - 1) * (k - i) := by
      have h1 := Nat.choose_succ_right_eq (k - 1) (i - 1)
      have hi1 : i - 1 + 1 = i := by omega
      have hki : k - 1 - (i - 1) = k - i := by omega
      rw [hi1, hki] at h1
      change i * (k - 1).choose i = (k - 1).choose (i - 1) * (k - i)
      linarith
    have h_sub : (N - 1).choose (k - 1) * (k - 1).choose (i - 1) =
        (N - 1).choose (i - 1) * (N - i).choose (k - i) := by
      have h1 := @Nat.choose_mul (N - 1) (k - 1) (i - 1) (by omega)
      have hNi : N - 1 - (i - 1) = N - i := by omega
      have hki : k - 1 - (i - 1) = k - i := by omega
      rw [hNi, hki] at h1
      exact h1
    have h_abs2 : (N - i).choose (k - i) * (k - i) =
        (N - i) * (N - 1 - i).choose (k - 1 - i) := by
      have h1 := Nat.add_one_mul_choose_eq (N - 1 - i) (k - 1 - i)
      have hNi1 : N - 1 - i + 1 = N - i := by omega
      have hki1 : k - 1 - i + 1 = k - i := by omega
      rw [hNi1, hki1] at h1
      exact h1.symm
    have h_four_term : N.choose k * A =
        ((N - i) * (Q * (N - 1).choose (i - 1) * (N - 1 - i).choose (k - 1 - i))) * A := by
      calc N.choose k * A
        _ = (W * (N - 1).choose (k - 1)) * ((k - 1).choose (i - 1) * (k - i)) := by
          rw [hN_choose, hi_choose]
        _ = W * ((N - 1).choose (k - 1) * (k - 1).choose (i - 1)) * (k - i) := by ring
        _ = W * ((N - 1).choose (i - 1) * (N - i).choose (k - i)) * (k - i) := by rw [h_sub]
        _ = W * (N - 1).choose (i - 1) * ((N - i).choose (k - i) * (k - i)) := by ring
        _ = W * (N - 1).choose (i - 1) * ((N - i) * (N - 1 - i).choose (k - 1 - i)) := by
          rw [h_abs2]
        _ = (A * Q) * (N - 1).choose (i - 1) * ((N - i) * (N - 1 - i).choose (k - 1 - i)) := by
          rw [hQ]
        _ = ((N - i) * (Q * (N - 1).choose (i - 1) * (N - 1 - i).choose (k - 1 - i))) * A := by
          ring
    have h_eq := Nat.eq_of_mul_eq_mul_right hA_pos h_four_term
    exact ⟨Q * (N - 1).choose (i - 1) * (N - 1 - i).choose (k - 1 - i), h_eq⟩
  have h_not_dvd_zero : ¬ (N - 0) ∣ N.choose k := by
    rw [Nat.sub_zero]
    set p := k.minFac
    have hp : p.Prime := Nat.minFac_prime (by omega)
    haveI : Fact p.Prime := ⟨hp⟩
    have hp_dvd_k : p ∣ k := Nat.minFac_dvd k
    have h_not_dvd_choose : ∀ m ≤ k - 1, ¬ p ∣ (N - 1).choose m := by
      intro m
      induction m with
      | zero =>
        intro _
        simp [hp.not_dvd_one]
      | succ m ih =>
        intro hm_le h_dvd
        have ih_m : ¬ p ∣ (N - 1).choose m := ih (by omega)
        set v := padicValNat p (m + 1)
        have hv_dvd : p ^ v ∣ m + 1 := pow_padicValNat_dvd
        have hv_not_dvd : ¬ p ^ (v + 1) ∣ m + 1 :=
          pow_succ_padicValNat_not_dvd (by omega)
        have hpv_le : p ^ v ≤ k - 1 :=
          le_trans (Nat.le_of_dvd (by omega) hv_dvd) hm_le
        have hpv_pos : 1 ≤ p ^ v := Nat.one_le_pow v p hp.pos
        have hpv_dvd_W : p ^ v ∣ W :=
          Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hpv_pos, hpv_le⟩)
        have hpv1_dvd_N : p ^ (v + 1) ∣ N := by
          rw [pow_succ']
          exact mul_dvd_mul hp_dvd_k hpv_dvd_W
        have hpv1_dvd_prod : p ^ (v + 1) ∣ (N - 1).choose m * (N - (m + 1)) := by
          have h_abs := Nat.choose_succ_right_eq (N - 1) m
          have h_sub_m : N - 1 - m = N - (m + 1) := by omega
          rw [h_sub_m] at h_abs
          rw [← h_abs, pow_succ']
          exact mul_dvd_mul h_dvd hv_dvd
        have h_cop : (p ^ (v + 1)).Coprime ((N - 1).choose m) :=
          (hp.coprime_iff_not_dvd.mpr ih_m).pow_left (v + 1)
        have hpv1_dvd_diff : p ^ (v + 1) ∣ N - (m + 1) :=
          h_cop.dvd_of_dvd_mul_left hpv1_dvd_prod
        have hpv1_dvd_m1 : p ^ (v + 1) ∣ m + 1 := by
          have h_eq_m1 : N - (N - (m + 1)) = m + 1 := by omega
          rw [← h_eq_m1]
          exact Nat.dvd_sub hpv1_dvd_N hpv1_dvd_diff
        exact hv_not_dvd hpv1_dvd_m1
    intro hN_dvd
    have hWN_dvd : W * k ∣ W * (N - 1).choose (k - 1) := by
      rw [mul_comm W k, ← hN_choose]
      exact hN_dvd
    have hk_dvd : k ∣ (N - 1).choose (k - 1) :=
      (mul_dvd_mul_iff_left (by omega : W ≠ 0)).mp hWN_dvd
    have hp_dvd : p ∣ (N - 1).choose (k - 1) := dvd_trans hp_dvd_k hk_dvd
    exact h_not_dvd_choose (k - 1) (le_refl _) hp_dvd
  apply Nat.sInf_le
  refine ⟨h2k_le_N, 0, by omega, h_not_dvd_zero, ?_⟩
  intro i hi_lt hi_ne
  exact h_dvd_pos i hi_lt hi_ne

theorem n_le_folded_pigeonhole_product : ∀ {k r : ℕ}, 500 ≤ k → Nat.sqrt k < r → 20 * r ≤ k →
    let P_all := (Finset.Ioc r k).filter Nat.Prime
    let P_inact := P_all.filter (fun p => r < k % p)
    let P_fold := P_all.filter (fun p => 51 * k ≤ 100 * p ∧ 100 * p ≤ 60 * k)
    let c (p : ℕ) : ℕ :=
      if p ∈ P_fold then ((p - 1) / 2 + r) / (r + 1) + 1
      else (p + min (r + 1) (k % p - r) - 1) / min (r + 1) (k % p - r)
    let G := (k * (k - 1).choose r) ^ 2 *
      (∏ p ∈ (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime, p ^ (Nat.log 2 k + 1)) *
      (∏ p ∈ (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime, p ^ 2)
    n k ≤ G * (∏ p ∈ P_inact, c p) + r :=
by
  intro k r hk500 hsqrt h20r P_all P_inact P_fold c G
  have hr_pos : 1 ≤ r := by omega
  have hr_lt_k : r < k := by omega

  
  have choose_mul_choose_split : ∀ {m k i0 : ℕ}, i0 < k → k ≤ m →
      m.choose k * k * (k - 1).choose i0 =
        (m - i0) * m.choose i0 * (m - i0 - 1).choose (k - 1 - i0) := by
    intro m k i0 hi0 hkm
    have h1 : k * (k - 1).choose i0 = k.choose i0 * (k - i0) := by
      have h1a := Nat.add_one_mul_choose_eq (k - 1) (k - 1 - i0)
      have hk1 : k - 1 + 1 = k := by omega
      have hk2 : k - 1 - i0 + 1 = k - i0 := by omega
      rw [hk1, hk2] at h1a
      rw [Nat.choose_symm (by omega : i0 ≤ k - 1), Nat.choose_symm (by omega : i0 ≤ k)] at h1a
      exact h1a
    have h2 : (m - i0) * (m - i0 - 1).choose (k - 1 - i0) = (m - i0).choose (k - i0) * (k - i0) := by
      have h2a := Nat.add_one_mul_choose_eq (m - i0 - 1) (k - 1 - i0)
      have hm1 : m - i0 - 1 + 1 = m - i0 := by omega
      have hk2 : k - 1 - i0 + 1 = k - i0 := by omega
      rw [hm1, hk2] at h2a
      exact h2a
    have h3 : m.choose k * k.choose i0 = m.choose i0 * (m - i0).choose (k - i0) :=
      Nat.choose_mul (by omega : i0 ≤ k)
    calc m.choose k * k * (k - 1).choose i0
      _ = m.choose k * (k * (k - 1).choose i0) := by ring
      _ = m.choose k * (k.choose i0 * (k - i0)) := by rw [h1]
      _ = (m.choose k * k.choose i0) * (k - i0) := by ring
      _ = (m.choose i0 * (m - i0).choose (k - i0)) * (k - i0) := by rw [h3]
      _ = m.choose i0 * ((m - i0).choose (k - i0) * (k - i0)) := by ring
      _ = m.choose i0 * ((m - i0) * (m - i0 - 1).choose (k - 1 - i0)) := by rw [← h2]
      _ = (m - i0) * m.choose i0 * (m - i0 - 1).choose (k - 1 - i0) := by ring

  have padicValNat_add_choose_eq_zero : ∀ {p M u : ℕ} [Fact p.Prime], 0 < M →
      (∀ j : ℕ, 1 ≤ j → j ≤ u → padicValNat p (M + j) ≤ padicValNat p M) →
      padicValNat p ((M + u).choose u) = 0 := by
    intro p M u _ hM hmax
    induction u with
    | zero => simp
    | succ u ih =>
      change padicValNat p ((M + u + 1).choose (u + 1)) = 0
      have ih' : padicValNat p ((M + u).choose u) = 0 :=
        ih (fun j hj1 hju => hmax j hj1 (by omega))
      have habs : (M + u + 1) * (M + u).choose u = (M + u + 1).choose (u + 1) * (u + 1) :=
        Nat.add_one_mul_choose_eq (M + u) u
      have hpos1 : (M + u).choose u ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hpos2 : (M + u + 1).choose (u + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hval := congrArg (padicValNat p) habs
      rw [padicValNat.mul (by omega) hpos1, padicValNat.mul hpos2 (by omega)] at hval
      have hle : padicValNat p (M + u + 1) ≤ padicValNat p (u + 1) := by
        have hm := hmax (u + 1) (by omega) (by omega)
        have hdvd1 : p ^ padicValNat p (M + u + 1) ∣ M + u + 1 :=
          (padicValNat_dvd_iff_le (by omega)).mpr (le_refl _)
        have hdvd2 : p ^ padicValNat p (M + u + 1) ∣ M :=
          (padicValNat_dvd_iff_le (by omega)).mpr hm
        have hdvd3 : p ^ padicValNat p (M + u + 1) ∣ (M + u + 1) - M :=
          Nat.dvd_sub hdvd1 hdvd2
        have hsub : M + u + 1 - M = u + 1 := by omega
        rw [hsub] at hdvd3
        exact (padicValNat_dvd_iff_le (by omega)).mp hdvd3
      omega

  have padicValNat_pred_choose_eq_zero : ∀ {p M s : ℕ} [Fact p.Prime], s < M →
      (∀ j : ℕ, 1 ≤ j → j ≤ s → padicValNat p (M - j) ≤ padicValNat p M) →
      padicValNat p ((M - 1).choose s) = 0 := by
    intro p M s _ hsM hmax
    induction s with
    | zero => simp
    | succ s ih =>
      have ih' : padicValNat p ((M - 1).choose s) = 0 :=
        ih (by omega) (fun j hj1 hjs => hmax j hj1 (by omega))
      have habs : (M - 1).choose (s + 1) * (s + 1) = (M - 1).choose s * (M - 1 - s) :=
        Nat.choose_succ_right_eq (M - 1) s
      have hsub1 : M - 1 - s = M - (s + 1) := by omega
      rw [hsub1] at habs
      have hpos1 : (M - 1).choose (s + 1) ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hpos2 : (M - 1).choose s ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hval := congrArg (padicValNat p) habs
      rw [padicValNat.mul hpos1 (by omega), padicValNat.mul hpos2 (by omega)] at hval
      have hle : padicValNat p (M - (s + 1)) ≤ padicValNat p (s + 1) := by
        have hm := hmax (s + 1) (by omega) (by omega)
        have hdvd1 : p ^ padicValNat p (M - (s + 1)) ∣ M - (s + 1) :=
          (padicValNat_dvd_iff_le (by omega)).mpr (le_refl _)
        have hdvd2 : p ^ padicValNat p (M - (s + 1)) ∣ M :=
          (padicValNat_dvd_iff_le (by omega)).mpr hm
        have hdvd3 : p ^ padicValNat p (M - (s + 1)) ∣ M - (M - (s + 1)) :=
          Nat.dvd_sub hdvd2 hdvd1
        have hsub2 : M - (M - (s + 1)) = s + 1 := by omega
        rw [hsub2] at hdvd3
        exact (padicValNat_dvd_iff_le (by omega)).mp hdvd3
      omega

  have s3_max_identity : ∀ {p m i0 : ℕ}, p.Prime → k ≤ m → i0 < k →
      (∀ i < k, padicValNat p (m - i) ≤ padicValNat p (m - i0)) →
      padicValNat p (m.choose k) + padicValNat p k + padicValNat p ((k - 1).choose i0) =
        padicValNat p (m - i0) := by
    intro p m i0 hp hkm hi0 hmax
    haveI : Fact p.Prime := ⟨hp⟩
    set M := m - i0
    have hM_pos : 0 < M := by omega
    have h_add_zero : padicValNat p (m.choose i0) = 0 := by
      have hMi0 : M + i0 = m := by omega
      rw [← hMi0]
      apply padicValNat_add_choose_eq_zero hM_pos
      intro j hj1 hju
      have hMj : M + j = m - (i0 - j) := by omega
      rw [hMj]
      exact hmax (i0 - j) (by omega)
    have h_pred_zero : padicValNat p ((m - i0 - 1).choose (k - 1 - i0)) = 0 := by
      change padicValNat p ((M - 1).choose (k - 1 - i0)) = 0
      apply padicValNat_pred_choose_eq_zero (by omega)
      intro j hj1 hjs
      have hMj : M - j = m - (i0 + j) := by omega
      rw [hMj]
      exact hmax (i0 + j) (by omega)
    have hsplit := choose_mul_choose_split hi0 hkm
    have hpos_mk : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hpos_k1 : (k - 1).choose i0 ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hpos_mi0 : m.choose i0 ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hpos_rem : (m - i0 - 1).choose (k - 1 - i0) ≠ 0 := (Nat.choose_pos (by omega)).ne'
    have hval := congrArg (padicValNat p) hsplit
    rw [padicValNat.mul (Nat.mul_ne_zero hpos_mk (by omega)) hpos_k1,
        padicValNat.mul hpos_mk (by omega),
        padicValNat.mul (Nat.mul_ne_zero (by omega) hpos_mi0) hpos_rem,
        padicValNat.mul (by omega) hpos_mi0,
        h_add_zero, h_pred_zero, add_zero, add_zero] at hval
    exact hval

  
  have s4_ultrametric : ∀ {p m i : ℕ}, p.Prime → k ≤ m → i < k → i ≠ r →
      Nat.log p (k - 1 - r) < padicValNat p (m - r) →
      padicValNat p (m - i) ≤ Nat.log p (k - 1 - r) := by
    intro p m i hp hkm hik hir hlt
    haveI : Fact p.Prime := ⟨hp⟩
    set H := Nat.log p (k - 1 - r)
    by_contra! hgt
    have hdvd_i : p ^ (H + 1) ∣ m - i := (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
    have hdvd_r : p ^ (H + 1) ∣ m - r := (padicValNat_dvd_iff_le (by omega)).mpr (by omega)
    have hpow_le : p ^ (H + 1) ≤ k - 1 - r := by
      rcases lt_or_gt_of_ne hir with hir_lt | hir_gt
      · have hdvd_sub : p ^ (H + 1) ∣ (m - i) - (m - r) := Nat.dvd_sub hdvd_i hdvd_r
        have hle : p ^ (H + 1) ≤ (m - i) - (m - r) := Nat.le_of_dvd (by omega) hdvd_sub
        omega
      · have hdvd_sub : p ^ (H + 1) ∣ (m - r) - (m - i) := Nat.dvd_sub hdvd_r hdvd_i
        have hle : p ^ (H + 1) ≤ (m - r) - (m - i) := Nat.le_of_dvd (by omega) hdvd_sub
        omega
    have hpow_gt : k - 1 - r < p ^ (H + 1) := Nat.lt_pow_succ_log_self hp.one_lt (k - 1 - r)
    omega

  
  have lt_sq_of_sqrt_lt : ∀ {p : ℕ}, Nat.sqrt k < p → k < p ^ 2 := by
    intro p hp_sqrt
    have h1 : k < (Nat.sqrt k + 1) * (Nat.sqrt k + 1) := Nat.lt_succ_sqrt k
    have h2 : (Nat.sqrt k + 1) * (Nat.sqrt k + 1) ≤ p * p :=
      Nat.mul_le_mul (by omega) (by omega)
    rw [sq]
    omega

  
  have s5_inactive_or_gt : ∀ {p m i0 : ℕ}, k ≤ m → p.Prime → i0 < k →
      1 ≤ padicValNat p (m - i0) →
      (k < p ∨ (p ∈ P_inact ∧ m % p < k % p)) →
      padicValNat p k = 0 ∧ padicValNat p ((k - 1).choose i0) = 0 := by
    intro p m i0 hkm hp hi0 hval hcases
    haveI : Fact p.Prime := ⟨hp⟩
    rcases hcases with hkp | ⟨hp_inact, hmp⟩
    · have hnot_dvd_k : ¬ p ∣ k := Nat.not_dvd_of_pos_of_lt (by omega) hkp
      have hvk : padicValNat p k = 0 := padicValNat.eq_zero_of_not_dvd hnot_dvd_k
      have hlog : Nat.log p (k - 1) < 1 :=
        Nat.log_lt_of_lt_pow (by omega) (by simpa using (by omega : k - 1 < p))
      refine ⟨hvk, ?_⟩
      rw [padicValNat_choose (by omega : i0 ≤ k - 1) hlog]
      simp
    · have hp_mem : p ∈ P_inact := hp_inact
      simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp_mem
      rcases hp_mem with ⟨⟨⟨hrp, hpk⟩, _⟩, hr_mod⟩
      have hnot_dvd_k : ¬ p ∣ k := by
        intro hdvd
        have := Nat.mod_eq_zero_of_dvd hdvd
        omega
      have hvk : padicValNat p k = 0 := padicValNat.eq_zero_of_not_dvd hnot_dvd_k
      refine ⟨hvk, ?_⟩
      have hdvd_mi0 : p ^ 1 ∣ m - i0 := (padicValNat_dvd_iff_le (by omega)).mpr hval
      rw [pow_one] at hdvd_mi0
      rcases hdvd_mi0 with ⟨t, ht⟩
      have hm_eq : m = i0 + p * t := by omega
      have hm_mod : m % p = i0 % p := by rw [hm_eq, Nat.add_mul_mod_self_left]
      have hk_mod_lt : k % p < p := Nat.mod_lt k hp.pos
      have hk1_mod : (k - 1) % p = k % p - 1 :=
        calc (k - 1) % p
          _ = ((k % p - 1) + p * (k / p)) % p := by
            congr 1
            have hk_div := (Nat.div_add_mod k p).symm
            omega
          _ = (k % p - 1) % p := Nat.add_mul_mod_self_left _ _ _
          _ = k % p - 1 := Nat.mod_eq_of_lt (by omega)
      have h_lt_sq : k - 1 < p ^ 2 := by
        have := lt_sq_of_sqrt_lt (by omega : Nat.sqrt k < p)
        omega
      have hlog : Nat.log p (k - 1) < 2 := Nat.log_lt_of_lt_pow (by omega) h_lt_sq
      rw [padicValNat_choose (by omega : i0 ≤ k - 1) hlog]
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro a ha
      have ha1 : a = 1 := by simp only [Finset.mem_Ico] at ha; omega
      subst ha1
      simp only [pow_one, not_le]
      set A := i0 % p
      set B := (k - 1 - i0) % p
      have hA_lt : A < p := Nat.mod_lt i0 hp.pos
      have hB_lt : B < p := Nat.mod_lt (k - 1 - i0) hp.pos
      have hAB_mod : (A + B) % p = (k - 1) % p := by
        rw [← Nat.add_mod, (by omega : i0 + (k - 1 - i0) = k - 1)]
      by_contra! hle_p
      have hAB_eq : (A + B) % p = A + B - p :=
        calc (A + B) % p
          _ = ((A + B - p) + p * 1) % p := by congr 1; omega
          _ = (A + B - p) % p := Nat.add_mul_mod_self_left _ _ _
          _ = A + B - p := Nat.mod_eq_of_lt (by omega)
      omega

  
  have s2_active_prime : ∀ {p a : ℕ}, 1 ≤ a → p.Prime → p ≤ k → p ∉ P_inact →
      2 * k ≤ a * G + r ∧
        Nat.log p (k - 1 - r) + max (padicValNat p k + padicValNat p ((k - 1).choose r)) 1 ≤
          padicValNat p (a * G) := by
    intro p a ha hp hpk hp_not_inact
    haveI : Fact p.Prime := ⟨hp⟩
    set prod1 := ∏ q ∈ (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime, q ^ (Nat.log 2 k + 1)
    set prod2 := ∏ q ∈ (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime, q ^ 2
    have hchoose_pos : 0 < (k - 1).choose r := Nat.choose_pos (by omega)
    have hprod1_pos : 0 < prod1 := by
      apply Finset.prod_pos
      intro q hq
      simp only [Finset.mem_filter] at hq
      exact pow_pos hq.2.pos _
    have hprod2_pos : 0 < prod2 := by
      apply Finset.prod_pos
      intro q hq
      simp only [Finset.mem_filter] at hq
      exact pow_pos hq.2.pos _
    have hG_ge : k ^ 2 ≤ G := by
      have hk_le : k ≤ k * (k - 1).choose r := Nat.le_mul_of_pos_right k hchoose_pos
      have hsq : k ^ 2 ≤ (k * (k - 1).choose r) ^ 2 := Nat.pow_le_pow_left hk_le 2
      have h1 : (k * (k - 1).choose r) ^ 2 ≤ (k * (k - 1).choose r) ^ 2 * prod1 :=
        Nat.le_mul_of_pos_right _ hprod1_pos
      have h2 : (k * (k - 1).choose r) ^ 2 * prod1 ≤ G :=
        Nat.le_mul_of_pos_right _ hprod2_pos
      omega
    have haG_ge : G ≤ a * G := Nat.le_mul_of_pos_left G (by omega)
    have h2k_le : 2 * k ≤ a * G + r := by nlinarith
    refine ⟨h2k_le, ?_⟩
    set H := Nat.log p (k - 1 - r)
    set β := padicValNat p k + padicValNat p ((k - 1).choose r)
    have hβ_eq : β = padicValNat p (k * (k - 1).choose r) :=
      (padicValNat.mul (by omega) hchoose_pos.ne').symm
    have hdvd_base : p ^ β ∣ k * (k - 1).choose r := by
      rw [hβ_eq]; exact pow_padicValNat_dvd
    have hdvd_sq : p ^ (2 * β) ∣ (k * (k - 1).choose r) ^ 2 := by
      rw [mul_comm 2 β, pow_mul]
      exact pow_dvd_pow_of_dvd hdvd_base 2
    have hdvd_G : p ^ (H + max β 1) ∣ G := by
      rcases le_or_gt p (Nat.sqrt k) with hp_sqrt | hp_sqrt
      · have hp_mem1 : p ∈ (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime :=
          Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.pos, hp_sqrt⟩, hp⟩
        have hdvd_p1 : p ^ (Nat.log 2 k + 1) ∣ prod1 :=
          Finset.dvd_prod_of_mem (fun q => q ^ (Nat.log 2 k + 1)) hp_mem1
        have hdvd_mul : p ^ (2 * β + (Nat.log 2 k + 1)) ∣ (k * (k - 1).choose r) ^ 2 * prod1 := by
          rw [pow_add]
          exact mul_dvd_mul hdvd_sq hdvd_p1
        have hH_le : H ≤ Nat.log 2 k := by
          have hp2 : 2 ≤ p := hp.two_le
          have hpow1 : 2 ^ H ≤ p ^ H := Nat.pow_le_pow_left hp2 H
          have hpow2 : p ^ H ≤ k - 1 - r := Nat.pow_log_le_self p (by omega)
          exact Nat.le_log_of_pow_le (by norm_num) (by omega)
        have hexp_le : H + max β 1 ≤ 2 * β + (Nat.log 2 k + 1) := by omega
        exact dvd_trans (pow_dvd_pow p hexp_le) (dvd_trans hdvd_mul (dvd_mul_right _ prod2))
      · rcases le_or_gt p r with hp_r | hp_r
        · have hp_mem2 : p ∈ (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime :=
            Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hp_sqrt, hp_r⟩, hp⟩
          have hdvd_p2 : p ^ 2 ∣ prod2 :=
            Finset.dvd_prod_of_mem (fun q => q ^ 2) hp_mem2
          have hdvd_G' : p ^ (2 * β + 2) ∣ G := by
            rw [pow_add]
            exact mul_dvd_mul (dvd_trans hdvd_sq (dvd_mul_right _ prod1)) hdvd_p2
          have hH_lt : H < 2 := by
            apply Nat.log_lt_of_lt_pow (by omega)
            have := lt_sq_of_sqrt_lt hp_sqrt
            omega
          have hexp_le : H + max β 1 ≤ 2 * β + 2 := by omega
          exact dvd_trans (pow_dvd_pow p hexp_le) hdvd_G'
        · have hmod_le_r : k % p ≤ r := by
            by_contra! hmod_gt
            apply hp_not_inact
            simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc]
            exact ⟨⟨⟨hp_r, hpk⟩, hp⟩, hmod_gt⟩
          have hH_lt : H < 2 := by
            apply Nat.log_lt_of_lt_pow (by omega)
            have := lt_sq_of_sqrt_lt hp_sqrt
            omega
          have hβ_pos : 1 ≤ β := by
            by_cases hdvd_k : p ∣ k
            · have hdvd1 : p ^ 1 ∣ k := by simpa using hdvd_k
              have hvk : 1 ≤ padicValNat p k := (padicValNat_dvd_iff_le (by omega)).mp hdvd1
              omega
            · have hmod_pos : 1 ≤ k % p := by
                have : k % p ≠ 0 := fun h0 => hdvd_k (Nat.dvd_of_mod_eq_zero h0)
                omega
              have hk_mod_lt : k % p < p := Nat.mod_lt k hp.pos
              have hk1_mod : (k - 1) % p = k % p - 1 :=
                calc (k - 1) % p
                  _ = ((k % p - 1) + p * (k / p)) % p := by
                    congr 1
                    have hk_div := (Nat.div_add_mod k p).symm
                    omega
                  _ = (k % p - 1) % p := Nat.add_mul_mod_self_left _ _ _
                  _ = k % p - 1 := Nat.mod_eq_of_lt (by omega)
              set b := Nat.log p (k - 1) + 2
              have hvc : 1 ≤ padicValNat p ((k - 1).choose r) := by
                rw [padicValNat_choose (by omega : r ≤ k - 1) (by omega : Nat.log p (k - 1) < b)]
                apply Finset.card_pos.mpr
                refine ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩⟩
                simp only [pow_one]
                have hr_mod : r % p = r := Nat.mod_eq_of_lt hp_r
                set B := (k - 1 - r) % p
                have hB_lt : B < p := Nat.mod_lt (k - 1 - r) hp.pos
                have hAB_mod : (r % p + B) % p = (k - 1) % p := by
                  rw [← Nat.add_mod, (by omega : r + (k - 1 - r) = k - 1)]
                by_contra! hlt_p
                have hAB_eq : (r % p + B) % p = r % p + B := Nat.mod_eq_of_lt hlt_p
                omega
              omega
          have hexp_le : H + max β 1 ≤ 2 * β := by omega
          exact dvd_trans (pow_dvd_pow p hexp_le)
            (dvd_trans hdvd_sq (dvd_trans (dvd_mul_right _ prod1) (dvd_mul_right _ prod2)))
    exact (padicValNat_dvd_iff_le (by omega)).mp (dvd_trans hdvd_G (dvd_mul_left G a))

  
  let fold (p z : ℕ) : ℕ := if z % p < (p - 1) / 2 then z % p else z % p - (p - 1) / 2
  let cell (p z : ℕ) : ℕ :=
    if p ∈ P_fold then fold p z / r
    else (z % p) / min (r + 1) (k % p - r)
  have hcell_lt : ∀ p ∈ P_inact, ∀ z : ℕ, cell p z < c p := by
    intro p hp_inact z
    have hp_mem : p ∈ P_inact := hp_inact
    simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp_mem
    rcases hp_mem with ⟨⟨⟨hrp, hpk⟩, hp⟩, hr_mod⟩
    have hzp : z % p < p := Nat.mod_lt z hp.pos
    by_cases hp_fold : p ∈ P_fold
    · simp only [cell, c, if_pos hp_fold]
      have hp_fold' : p ∈ P_fold := hp_fold
      simp only [P_fold, P_all, Finset.mem_filter] at hp_fold'
      have h51 : 51 * k ≤ 100 * p := hp_fold'.2.1
      have hp_not2 : ¬ 2 ∣ p := by
        intro hdvd
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd) with h2 | h2 <;> omega
      have hp_mod2 : p % 2 = 1 := by
        have : p % 2 ≠ 0 := fun h0 => hp_not2 (Nat.dvd_of_mod_eq_zero h0)
        omega
      set s := (p - 1) / 2
      have hfold_le : fold p z ≤ s := by
        dsimp only [fold, s]
        split_ifs <;> omega
      set q := (s + r) / (r + 1)
      have hq_div : (r + 1) * q + (s + r) % (r + 1) = s + r :=
        Nat.div_add_mod (s + r) (r + 1)
      have hq_mod : (s + r) % (r + 1) < r + 1 := Nat.mod_lt (s + r) (by omega)
      have hs_le : s ≤ r * q + q := by
        have hring : (r + 1) * q = r * q + q := by ring
        rw [hring] at hq_div
        omega
      have hk_lt_r2 : k < r * r := by
        have := lt_sq_of_sqrt_lt hsqrt
        rwa [sq] at this
      have hfold_lt_mul : fold p z < r * (q + 1) := by
        rcases lt_or_ge q r with hqr | hqr
        · have : r * (q + 1) = r * q + r := by ring
          omega
        · have hr2_le : r * r ≤ r * q := Nat.mul_le_mul_left r hqr
          have : r * (q + 1) = r * q + r := by ring
          omega
      exact Nat.div_lt_of_lt_mul hfold_lt_mul
    · simp only [cell, c, if_neg hp_fold]
      set w := min (r + 1) (k % p - r)
      have hw_pos : 1 ≤ w := by omega
      have hdiv_mod := Nat.div_add_mod (p + w - 1) w
      have hmod_lt : (p + w - 1) % w < w := Nat.mod_lt (p + w - 1) (by omega)
      have hlt_mul : z % p < w * ((p + w - 1) / w) := by omega
      exact Nat.div_lt_of_lt_mul hlt_mul

  have hcell_collision : ∀ p ∈ P_inact, ∀ z1 z2 : ℕ, cell p z1 = cell p z2 →
      ∃ d < k % p, (z1 % p + d) % p = (z2 % p + r) % p := by
    intro p hp_inact z1 z2 hcell
    have hp_mem : p ∈ P_inact := hp_inact
    simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp_mem
    rcases hp_mem with ⟨⟨⟨hrp, hpk⟩, hp⟩, hr_mod⟩
    set y := z1 % p
    set x := z2 % p
    have hy_lt : y < p := Nat.mod_lt z1 hp.pos
    have hx_lt : x < p := Nat.mod_lt z2 hp.pos
    by_cases hp_fold : p ∈ P_fold
    · simp only [cell, if_pos hp_fold] at hcell
      have hp_fold' : p ∈ P_fold := hp_fold
      simp only [P_fold, P_all, Finset.mem_filter] at hp_fold'
      rcases hp_fold'.2 with ⟨h51, h60⟩
      have hp_not2 : ¬ 2 ∣ p := by
        intro hdvd
        rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 hdvd) with h2 | h2 <;> omega
      have hp_mod2 : p % 2 = 1 := by
        have : p % 2 ≠ 0 := fun h0 => hp_not2 (Nat.dvd_of_mod_eq_zero h0)
        omega
      have hk_mod : k % p = k - p :=
        calc k % p
          _ = ((k - p) + p * 1) % p := by congr 1; omega
          _ = (k - p) % p := Nat.add_mul_mod_self_left _ _ _
          _ = k - p := Nat.mod_eq_of_lt (by omega)
      set u1 := fold p z1
      set u2 := fold p z2
      change u1 / r = u2 / r at hcell
      have hu1_div := Nat.div_add_mod u1 r
      rw [hcell] at hu1_div
      have hu1_mod : u1 % r < r := Nat.mod_lt u1 (by omega)
      have hu2_div := Nat.div_add_mod u2 r
      have hu2_mod : u2 % r < r := Nat.mod_lt u2 (by omega)
      have hu_diff : u1 ≤ u2 + r - 1 ∧ u2 ≤ u1 + r - 1 := by omega
      have hu1_def : u1 = if y < (p - 1) / 2 then y else y - (p - 1) / 2 := rfl
      have hu2_def : u2 = if x < (p - 1) / 2 then x else x - (p - 1) / 2 := rfl
      by_cases hyx : y ≤ x + r
      · refine ⟨x + r - y, ?_, ?_⟩
        · split_ifs at hu1_def hu2_def <;> omega
        · rw [Nat.add_sub_of_le hyx]
      · refine ⟨x + p + r - y, ?_, ?_⟩
        · split_ifs at hu1_def hu2_def <;> omega
        · have h_eq : y + (x + p + r - y) = (x + r) + p * 1 := by omega
          rw [h_eq, Nat.add_mul_mod_self_left]
    · simp only [cell, if_neg hp_fold] at hcell
      set w := min (r + 1) (k % p - r)
      change y / w = x / w at hcell
      have hw_pos : 1 ≤ w := by omega
      have hw_r : w ≤ r + 1 := Nat.min_le_left _ _
      have hw_k : w ≤ k % p - r := Nat.min_le_right _ _
      have hy_div := Nat.div_add_mod y w
      rw [hcell] at hy_div
      have hy_mod : y % w < w := Nat.mod_lt y (by omega)
      have hx_div := Nat.div_add_mod x w
      have hx_mod : x % w < w := Nat.mod_lt x (by omega)
      have h_diff : y ≤ x + w - 1 ∧ x ≤ y + w - 1 := by omega
      refine ⟨x + r - y, by omega, ?_⟩
      rw [Nat.add_sub_of_le (by omega)]

  set Q := ∏ p ∈ P_inact, c p
  have s1_exists_a : ∃ a : ℕ, 1 ≤ a ∧ a ≤ Q ∧ ∀ p ∈ P_inact, (a * G + r) % p < k % p := by
    let F : Fin (Q + 1) → (∀ p : P_inact, Fin (c p.1)) :=
      fun j p => ⟨cell p.1 (j.1 * G), hcell_lt p.1 p.2 (j.1 * G)⟩
    have hcard_cod : Fintype.card (∀ p : P_inact, Fin (c p.1)) = Q := by
      rw [Fintype.card_pi]
      simp only [Fintype.card_fin]
      exact Finset.prod_attach P_inact c
    have hcard_lt : Fintype.card (∀ p : P_inact, Fin (c p.1)) < Fintype.card (Fin (Q + 1)) := by
      rw [hcard_cod, Fintype.card_fin]
      omega
    obtain ⟨j1, j2, hj_ne, hj_eq⟩ := Fintype.exists_ne_map_eq_of_card_lt F hcard_lt
    have h_from_lt : ∀ u v : Fin (Q + 1), u.1 < v.1 → F u = F v →
        ∃ a : ℕ, 1 ≤ a ∧ a ≤ Q ∧ ∀ p ∈ P_inact, (a * G + r) % p < k % p := by
      intro u v huv hFuv
      refine ⟨v.1 - u.1, by omega, by omega, ?_⟩
      intro p hp_inact
      have hp_mem : p ∈ P_inact := hp_inact
      simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp_mem
      have hp_prime : p.Prime := hp_mem.1.2
      have hcell_eq : cell p (u.1 * G) = cell p (v.1 * G) := by
        have h := congrFun hFuv ⟨p, hp_inact⟩
        exact congrArg Fin.val h
      obtain ⟨d, hd_lt, hd_mod⟩ := hcell_collision p hp_inact (u.1 * G) (v.1 * G) hcell_eq
      rw [Nat.mod_add_mod, Nat.mod_add_mod] at hd_mod
      have hv_eq : v.1 * G + r = u.1 * G + ((v.1 - u.1) * G + r) := by
        have hsub : u.1 + (v.1 - u.1) = v.1 := Nat.add_sub_of_le (by omega)
        calc v.1 * G + r
          _ = (u.1 + (v.1 - u.1)) * G + r := by rw [hsub]
          _ = u.1 * G + ((v.1 - u.1) * G + r) := by ring
      rw [hv_eq] at hd_mod
      change u.1 * G + d ≡ u.1 * G + ((v.1 - u.1) * G + r) [MOD p] at hd_mod
      have hcancel : d ≡ (v.1 - u.1) * G + r [MOD p] :=
        Nat.ModEq.add_left_cancel' (u.1 * G) hd_mod
      have hd_lt_p : d < p := lt_trans hd_lt (Nat.mod_lt k hp_prime.pos)
      have hd_eq : (v.1 - u.1) * G + r ≡ d [MOD p] := hcancel.symm
      change ((v.1 - u.1) * G + r) % p = d % p at hd_eq
      rw [Nat.mod_eq_of_lt hd_lt_p] at hd_eq
      omega
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hj_ne) with hlt | hgt
    · exact h_from_lt j1 j2 hlt hj_eq
    · exact h_from_lt j2 j1 hgt hj_eq.symm

  
  obtain ⟨a, ha1, haQ, ha_mod⟩ := s1_exists_a
  set m := a * G + r
  let p0 := k.minFac
  have hp0_prime : p0.Prime := Nat.minFac_prime (by omega)
  have hp0_dvd : p0 ∣ k := Nat.minFac_dvd k
  have hp0_le_k : p0 ≤ k := Nat.le_of_dvd (by omega) hp0_dvd
  have hp0_not_inact : p0 ∉ P_inact := by
    intro hmem
    simp only [P_inact, Finset.mem_filter] at hmem
    have := Nat.mod_eq_zero_of_dvd hp0_dvd
    omega
  obtain ⟨h2k_m, hp0_val_le⟩ := s2_active_prime ha1 hp0_prime hp0_le_k hp0_not_inact
  have hm_sub_r : m - r = a * G := by omega
  have hn_le_m : n k ≤ m := by
    apply Nat.sInf_le
    refine ⟨h2k_m, r, hr_lt_k, ?_, ?_⟩
    · 
      haveI : Fact p0.Prime := ⟨hp0_prime⟩
      have hp0_max : ∀ i < k, padicValNat p0 (m - i) ≤ padicValNat p0 (m - r) := by
        intro i hik
        by_cases hir : i = r
        · subst hir; exact le_refl _
        · have hlt : Nat.log p0 (k - 1 - r) < padicValNat p0 (m - r) := by
            rw [hm_sub_r]; omega
          have hle := s4_ultrametric hp0_prime (by omega) hik hir hlt
          omega
      have h_id := s3_max_identity hp0_prime (by omega) hr_lt_k hp0_max
      have hvp0_k : 1 ≤ padicValNat p0 k := by
        have hdvd1 : p0 ^ 1 ∣ k := by simpa using hp0_dvd
        exact (padicValNat_dvd_iff_le (by omega)).mp hdvd1
      intro hdvd
      have hpos_mk : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
      have hdvd_pow : p0 ^ padicValNat p0 (m - r) ∣ m.choose k :=
        dvd_trans pow_padicValNat_dvd hdvd
      have hle_val : padicValNat p0 (m - r) ≤ padicValNat p0 (m.choose k) :=
        (padicValNat_dvd_iff_le hpos_mk).mp hdvd_pow
      omega
    · 
      intro i hik hir
      have hmi_ne : m - i ≠ 0 := by omega
      have hmk_ne : m.choose k ≠ 0 := (Nat.choose_pos (by omega)).ne'
      rw [← Nat.factorization_le_iff_dvd hmi_ne hmk_ne]
      intro p
      by_cases hp : p.Prime
      · rw [Nat.factorization_def (m - i) hp, Nat.factorization_def (m.choose k) hp]
        by_cases h_active : p ≤ k ∧ p ∉ P_inact
        · obtain ⟨_, hp_val_le⟩ := s2_active_prime ha1 hp h_active.1 h_active.2
          have hlt : Nat.log p (k - 1 - r) < padicValNat p (m - r) := by
            rw [hm_sub_r]; omega
          have h_i_le : padicValNat p (m - i) ≤ Nat.log p (k - 1 - r) :=
            s4_ultrametric hp (by omega) hik hir hlt
          have hp_max : ∀ j < k, padicValNat p (m - j) ≤ padicValNat p (m - r) := by
            intro j hjk
            by_cases hjr : j = r
            · subst hjr; exact le_refl _
            · have := s4_ultrametric hp (by omega) hjk hjr hlt
              omega
          have h_id := s3_max_identity hp (by omega) hr_lt_k hp_max
          rw [hm_sub_r] at h_id
          omega
        · have hne_range : (Finset.range k).Nonempty := Finset.nonempty_range_iff.mpr (by omega)
          obtain ⟨i0, hi0_mem, hi0_max⟩ :=
            Finset.exists_max_image (Finset.range k) (fun j => padicValNat p (m - j)) hne_range
          have hi0 : i0 < k := Finset.mem_range.mp hi0_mem
          have hp_max : ∀ j < k, padicValNat p (m - j) ≤ padicValNat p (m - i0) :=
            fun j hjk => hi0_max j (Finset.mem_range.mpr hjk)
          have h_i_le : padicValNat p (m - i) ≤ padicValNat p (m - i0) := hp_max i hik
          rcases Nat.eq_zero_or_pos (padicValNat p (m - i0)) with h0 | hpos
          · omega
          · have h_id := s3_max_identity hp (by omega) hi0 hp_max
            have hcases : k < p ∨ (p ∈ P_inact ∧ m % p < k % p) := by
              rcases lt_or_ge k p with hkp | hpk
              · exact Or.inl hkp
              · have hp_inact : p ∈ P_inact := by
                  by_contra hp_not
                  exact h_active ⟨hpk, hp_not⟩
                exact Or.inr ⟨hp_inact, ha_mod p hp_inact⟩
            obtain ⟨hvk0, hvc0⟩ := s5_inactive_or_gt (by omega) hp hi0 hpos hcases
            omega
      · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have hm_le : m ≤ G * Q + r := by
    have : a * G ≤ G * Q := by
      rw [mul_comm G Q]
      exact Nat.mul_le_mul_right G haQ
    omega
  exact le_trans hn_le_m hm_le

theorem witness_product_log_le_chebyshev : ∀ {k r : ℕ}, 500 ≤ k → Nat.sqrt k < r → 20 * r ≤ k →
    let P_all := (Finset.Ioc r k).filter Nat.Prime
    let P_inact := P_all.filter (fun p => r < k % p)
    let P_fold := P_all.filter (fun p => 51 * k ≤ 100 * p ∧ 100 * p ≤ 60 * k)
    let c (p : ℕ) : ℕ :=
      if p ∈ P_fold then ((p - 1) / 2 + r) / (r + 1) + 1
      else (p + min (r + 1) (k % p - r) - 1) / min (r + 1) (k % p - r)
    let G := (k * (k - 1).choose r) ^ 2 *
      (∏ p ∈ (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime, p ^ (Nat.log 2 k + 1)) *
      (∏ p ∈ (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime, p ^ 2)
    Real.log (((G * (∏ p ∈ P_inact, c p) + r : ℕ) : ℝ)) ≤
      2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) +
      Chebyshev.theta (k : ℝ) - (k.primeCounting : ℝ) * Real.log (r : ℝ) -
      Real.log 2 * (P_fold.card : ℝ) +
      50 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) +
      20 * (k : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) +
      4 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 :=
by
  intro k r hk500 h_sqrt_r h_20r
  dsimp only
  set P_all := (Finset.Ioc r k).filter Nat.Prime
  set P_inact := P_all.filter (fun p => r < k % p)
  set P_fold := P_all.filter (fun p => 51 * k ≤ 100 * p ∧ 100 * p ≤ 60 * k)
  set B := P_inact.filter (fun p => k % p ≤ 2 * r)
  set c : ℕ → ℕ := fun p =>
    if p ∈ P_fold then ((p - 1) / 2 + r) / (r + 1) + 1
    else (p + min (r + 1) (k % p - r) - 1) / min (r + 1) (k % p - r)
  set G := (k * (k - 1).choose r) ^ 2 *
    (∏ p ∈ (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime, p ^ (Nat.log 2 k + 1)) *
    (∏ p ∈ (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime, p ^ 2)
  set Q := ∏ p ∈ P_inact, c p
  
  have hs1 : 1 ≤ G ∧ r ≤ G ∧
      Real.log (2 * (G : ℝ)) ≤
        2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) +
        13 * (r : ℝ) +
        4 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by
    set C := (k - 1).choose r
    set P1 := (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime
    set P2 := (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime
    set Pi1 := ∏ p ∈ P1, p ^ (Nat.log 2 k + 1)
    set Pi2 := ∏ p ∈ P2, p ^ 2
    change 1 ≤ (k * C) ^ 2 * Pi1 * Pi2 ∧ r ≤ (k * C) ^ 2 * Pi1 * Pi2 ∧
      Real.log (2 * (((k * C) ^ 2 * Pi1 * Pi2 : ℕ) : ℝ)) ≤
        2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) +
        13 * (r : ℝ) +
        4 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2
    have hr1 : 1 ≤ r := by omega
    have hrk1 : r ≤ k - 1 := by omega
    have hC_pos : 1 ≤ C := Nat.choose_pos hrk1
    have hPi1_pos : 1 ≤ Pi1 := by
      apply Finset.one_le_prod'
      intro p hp
      simp only [P1, Finset.mem_filter] at hp
      exact Nat.one_le_pow _ _ hp.2.pos
    have hPi2_pos : 1 ≤ Pi2 := by
      apply Finset.one_le_prod'
      intro p hp
      simp only [P2, Finset.mem_filter] at hp
      exact Nat.one_le_pow _ _ hp.2.pos
    have hr_le_kC2 : r ≤ (k * C) ^ 2 := by
      have hkC : r ≤ k * C := le_trans (by omega : r ≤ k) (Nat.le_mul_of_pos_right k hC_pos)
      have h1 : 1 ≤ k * C := le_trans hr1 hkC
      calc r ≤ k * C := hkC
        _ = (k * C) * 1 := (Nat.mul_one _).symm
        _ ≤ (k * C) * (k * C) := Nat.mul_le_mul_left _ h1
        _ = (k * C) ^ 2 := (sq _).symm
    have hrG : r ≤ (k * C) ^ 2 * Pi1 * Pi2 := by
      calc r ≤ (k * C) ^ 2 := hr_le_kC2
        _ ≤ (k * C) ^ 2 * Pi1 := Nat.le_mul_of_pos_right _ hPi1_pos
        _ ≤ (k * C) ^ 2 * Pi1 * Pi2 := Nat.le_mul_of_pos_right _ hPi2_pos
    have h1G : 1 ≤ (k * C) ^ 2 * Pi1 * Pi2 := le_trans hr1 hrG
    refine ⟨h1G, hrG, ?_⟩
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hC_pos_R : (0 : ℝ) < (C : ℝ) := by exact_mod_cast hC_pos
    have hPi1_pos_R : (0 : ℝ) < (Pi1 : ℝ) := by exact_mod_cast hPi1_pos
    have hPi2_pos_R : (0 : ℝ) < (Pi2 : ℝ) := by exact_mod_cast hPi2_pos
    have hlog_2G : Real.log (2 * (((k * C) ^ 2 * Pi1 * Pi2 : ℕ) : ℝ)) =
        Real.log 2 + 2 * Real.log (k : ℝ) + 2 * Real.log (C : ℝ) +
        Real.log (Pi1 : ℝ) + Real.log (Pi2 : ℝ) := by
      have h2G_cast : 2 * (((k * C) ^ 2 * Pi1 * Pi2 : ℕ) : ℝ) =
          2 * ((k : ℝ) * (C : ℝ)) ^ 2 * (Pi1 : ℝ) * (Pi2 : ℝ) := by
        push_cast
        ring
      rw [h2G_cast]
      rw [Real.log_mul (by positivity) (ne_of_gt hPi2_pos_R)]
      rw [Real.log_mul (by positivity) (ne_of_gt hPi1_pos_R)]
      rw [Real.log_mul (by positivity) (by positivity)]
      rw [Real.log_pow, Real.log_mul (ne_of_gt hk_pos) (ne_of_gt hC_pos_R)]
      ring
    have h_log_C : 2 * Real.log (C : ℝ) ≤ 2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) + 2 * (r : ℝ) := by
      have h_desc : r.factorial * C ≤ k ^ r := by
        calc r.factorial * C = (k - 1).descFactorial r := (Nat.descFactorial_eq_factorial_mul_choose (k - 1) r).symm
          _ ≤ (k - 1) ^ r := Nat.descFactorial_le_pow (k - 1) r
          _ ≤ k ^ r := Nat.pow_le_pow_left (by omega) r
      have h_desc_R : (r.factorial : ℝ) * (C : ℝ) ≤ (k : ℝ) ^ r := by exact_mod_cast h_desc
      have h_fact_pos : (0 : ℝ) < (r.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos r
      have hC_le_div : (C : ℝ) ≤ (k : ℝ) ^ r / (r.factorial : ℝ) := by
        rw [le_div_iff₀ h_fact_pos]
        linarith
      have h_rr_fact_le_exp : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp (r : ℝ) := by
        have h_sum := Real.sum_le_exp_of_nonneg (le_of_lt hr_pos) (r + 1)
        have h_mem : r ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
        have h_nonneg : ∀ i ∈ Finset.range (r + 1), 0 ≤ (r : ℝ) ^ i / (i.factorial : ℝ) := fun i _ => by positivity
        exact le_trans (Finset.single_le_sum h_nonneg h_mem) h_sum
      have h_split : (k : ℝ) ^ r / (r.factorial : ℝ) = ((k : ℝ) / (r : ℝ)) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
        rw [div_pow, div_mul_div_cancel₀ (by positivity)]
      have hC_le_exp : (C : ℝ) ≤ ((k : ℝ) / (r : ℝ)) ^ r * Real.exp (r : ℝ) := by
        calc (C : ℝ) ≤ (k : ℝ) ^ r / (r.factorial : ℝ) := hC_le_div
          _ = ((k : ℝ) / (r : ℝ)) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := h_split
          _ ≤ ((k : ℝ) / (r : ℝ)) ^ r * Real.exp (r : ℝ) :=
            mul_le_mul_of_nonneg_left h_rr_fact_le_exp (by positivity)
      have h_log_C_single : Real.log (C : ℝ) ≤ (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) + (r : ℝ) := by
        calc Real.log (C : ℝ)
          _ ≤ Real.log (((k : ℝ) / (r : ℝ)) ^ r * Real.exp (r : ℝ)) := Real.log_le_log hC_pos_R hC_le_exp
          _ = Real.log (((k : ℝ) / (r : ℝ)) ^ r) + Real.log (Real.exp (r : ℝ)) :=
            Real.log_mul (by positivity) (by positivity)
          _ = (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) + (r : ℝ) := by rw [Real.log_pow, Real.log_exp]
      linarith
    have h_log_Pi2 : Real.log (Pi2 : ℝ) ≤ 11 * (r : ℝ) := by
      have hPi2_cast : (Pi2 : ℝ) = ∏ p ∈ P2, ((p : ℝ) ^ 2) := by
        dsimp [Pi2]
        push_cast
        rfl
      have h_log_eq : Real.log (Pi2 : ℝ) = 2 * ∑ p ∈ P2, Real.log (p : ℝ) := by
        rw [hPi2_cast, Real.log_prod]
        · simp_rw [Real.log_pow]
          rw [← Finset.mul_sum]
          ring
        · intro p hp
          simp only [P2, Finset.mem_filter] at hp
          have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
          positivity
      have hsub : P2 ⊆ (Finset.Icc 0 r).filter Nat.Prime := by
        intro p hp
        simp only [P2, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
      have hnonneg : ∀ p ∈ (Finset.Icc 0 r).filter Nat.Prime, p ∉ P2 → 0 ≤ Real.log (p : ℝ) := by
        intro p hp _
        simp only [Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
      have h_sum_le_theta : ∑ p ∈ P2, Real.log (p : ℝ) ≤ Chebyshev.theta (r : ℝ) := by
        rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      have h_theta_le : Chebyshev.theta (r : ℝ) ≤ (Real.log 4 + 4) * (r : ℝ) :=
        le_trans (Chebyshev.theta_le_psi (r : ℝ)) (Chebyshev.psi_le_const_mul_self (le_of_lt hr_pos))
      have hlog4 : Real.log 4 + 4 ≤ 5.5 := by
        have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
        rw [h4, Real.log_pow]
        push_cast
        linarith [Real.log_two_lt_d9]
      nlinarith
    have h_log_Pi1 : Real.log 2 + 2 * Real.log (k : ℝ) + Real.log (Pi1 : ℝ) ≤
        4 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by
      have hPi1_cast : (Pi1 : ℝ) = ∏ p ∈ P1, ((p : ℝ) ^ (Nat.log 2 k + 1)) := by
        dsimp [Pi1]
        push_cast
        rfl
      have h_log_eq : Real.log (Pi1 : ℝ) = ((Nat.log 2 k + 1 : ℕ) : ℝ) * ∑ p ∈ P1, Real.log (p : ℝ) := by
        rw [hPi1_cast, Real.log_prod]
        · simp_rw [Real.log_pow]
          rw [← Finset.mul_sum]
        · intro p hp
          simp only [P1, Finset.mem_filter] at hp
          have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
          positivity
      have h_sum_P1 : ∑ p ∈ P1, Real.log (p : ℝ) ≤ Real.sqrt (k : ℝ) * Real.log (k : ℝ) := by
        have h_ptwise : ∀ p ∈ P1, Real.log (p : ℝ) ≤ Real.log (k : ℝ) := by
          intro p hp
          simp only [P1, Finset.mem_filter, Finset.mem_Icc] at hp
          have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
          have hpk : p ≤ k := le_trans hp.1.2 (Nat.sqrt_le_self k)
          exact Real.log_le_log hp_pos (by exact_mod_cast hpk)
        have h_card : (P1.card : ℝ) ≤ Real.sqrt (k : ℝ) := by
          have hsub : P1 ⊆ Finset.Icc 1 (Nat.sqrt k) := Finset.filter_subset _ _
          have h1 : P1.card ≤ Nat.sqrt k := by
            have := Finset.card_le_card hsub
            simpa using this
          have h_sqrt_le : (Nat.sqrt k : ℝ) ≤ Real.sqrt (k : ℝ) := by
            rw [← Real.sqrt_sq (Nat.cast_nonneg (Nat.sqrt k))]
            apply Real.sqrt_le_sqrt
            exact_mod_cast (by simpa [sq] using Nat.sqrt_le k : (Nat.sqrt k) ^ 2 ≤ k)
          exact le_trans (Nat.cast_le.mpr h1) h_sqrt_le
        have hlogk_nonneg : 0 ≤ Real.log (k : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ k))
        calc ∑ p ∈ P1, Real.log (p : ℝ)
          _ ≤ ∑ _p ∈ P1, Real.log (k : ℝ) := Finset.sum_le_sum h_ptwise
          _ = (P1.card : ℝ) * Real.log (k : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ Real.sqrt (k : ℝ) * Real.log (k : ℝ) := mul_le_mul_of_nonneg_right h_card hlogk_nonneg
      have h_pow_log : (2 : ℝ) ^ (Nat.log 2 k) ≤ (k : ℝ) := by
        exact_mod_cast Nat.pow_log_le_self 2 (by omega : k ≠ 0)
      have h_log2_mul : (Nat.log 2 k : ℝ) * Real.log 2 ≤ Real.log (k : ℝ) := by
        have := Real.log_le_log (by positivity) h_pow_log
        rwa [Real.log_pow] at this
      have h_256_le_k : (2 : ℝ) ^ 8 ≤ (k : ℝ) := by
        have : (2 : ℝ) ^ 8 = (256 : ℝ) := by norm_num
        rw [this]
        exact_mod_cast (by omega : 256 ≤ k)
      have h_8log2_le : 8 * Real.log 2 ≤ Real.log (k : ℝ) := by
        have := Real.log_le_log (by positivity) h_256_le_k
        rwa [Real.log_pow, show ((8 : ℕ) : ℝ) = 8 by norm_num] at this
      have h_log2_gt : (0.693 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
      have h_log2_lt : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
      have h_natlog_nonneg : (0 : ℝ) ≤ (Nat.log 2 k : ℝ) := Nat.cast_nonneg _
      have h_natlog_0693 : 0.693 * (Nat.log 2 k : ℝ) ≤ (Nat.log 2 k : ℝ) * Real.log 2 := by nlinarith
      have h_natlog_le : ((Nat.log 2 k + 1 : ℕ) : ℝ) ≤ 2 * Real.log (k : ℝ) := by
        push_cast
        linarith
      have h_sqrtk_ge : (22 : ℝ) ≤ Real.sqrt (k : ℝ) := by
        rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ 22)]
        apply Real.sqrt_le_sqrt
        have : (22 : ℝ) ^ 2 = (484 : ℝ) := by norm_num
        rw [this]
        exact_mod_cast (by omega : 484 ≤ k)
      have h_sum_P1_nonneg : 0 ≤ ∑ p ∈ P1, Real.log (p : ℝ) := by
        apply Finset.sum_nonneg
        intro p hp
        simp only [P1, Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
      have h_Pi1_bound : Real.log (Pi1 : ℝ) ≤ 2 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by
        rw [h_log_eq]
        calc ((Nat.log 2 k + 1 : ℕ) : ℝ) * ∑ p ∈ P1, Real.log (p : ℝ)
          _ ≤ (2 * Real.log (k : ℝ)) * (Real.sqrt (k : ℝ) * Real.log (k : ℝ)) :=
            mul_le_mul h_natlog_le h_sum_P1 h_sum_P1_nonneg (by linarith)
          _ = 2 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by ring
      have h_head_bound : Real.log 2 + 2 * Real.log (k : ℝ) ≤ 2 * Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 := by
        have h_logk_ge5 : (5 : ℝ) ≤ Real.log (k : ℝ) := by linarith
        have h_sq_ge : 5 * Real.log (k : ℝ) ≤ (Real.log (k : ℝ)) ^ 2 := by nlinarith
        have h_sq_nonneg : 0 ≤ (Real.log (k : ℝ)) ^ 2 := sq_nonneg _
        have h_prod_ge : 22 * (Real.log (k : ℝ)) ^ 2 ≤ Real.sqrt (k : ℝ) * (Real.log (k : ℝ)) ^ 2 :=
          mul_le_mul_of_nonneg_right h_sqrtk_ge h_sq_nonneg
        linarith
      linarith
    linarith
  
  have hs2 : 1 ≤ Q ∧
      Real.log (Q : ℝ) ≤
        (∑ p ∈ P_inact, (Real.log (p : ℝ) - Real.log (r : ℝ))) -
        Real.log 2 * (P_fold.card : ℝ) +
        10 * (r : ℝ) +
        (∑ p ∈ B, Real.log (2 * (r : ℝ) / ((k % p - r : ℕ) : ℝ))) +
        (∑ p ∈ P_all, Real.log (1 + (r : ℝ) / (p : ℝ))) := by
    clear hs1 G
    have hr1 : 1 ≤ r := by omega
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr1
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have h_fold_mod : ∀ p ∈ P_fold, k % p = k - p ∧ 2 * r < k % p := by
      intro p hp
      simp only [P_fold, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp
      rcases hp with ⟨⟨⟨hrp, hpk⟩, _⟩, h51, h60⟩
      have hkp : k = (k - p) + p := (Nat.sub_add_cancel hpk).symm
      have hmod : k % p = k - p := by
        conv_lhs => rw [hkp, Nat.add_mod_right]
        exact Nat.mod_eq_of_lt (by omega)
      exact ⟨hmod, by omega⟩
    have h_fold_sub : P_fold ⊆ P_inact := by
      intro p hp
      have hmod := (h_fold_mod p hp).2
      simp only [P_fold, P_inact, Finset.mem_filter] at hp ⊢
      exact ⟨hp.1, by omega⟩
    have hc_pos : ∀ p ∈ P_inact, 1 ≤ c p := by
      intro p hp
      simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp
      rcases hp with ⟨⟨⟨hrp, hpk⟩, _⟩, hmod⟩
      dsimp [c]
      split_ifs with hfold
      · exact Nat.le_add_left 1 _
      · exact Nat.div_pos (by omega) (by omega)
    have h_prod_pos : 1 ≤ Q := Finset.one_le_prod' hc_pos
    refine ⟨h_prod_pos, ?_⟩
    have h_ptwise : ∀ p ∈ P_inact,
        Real.log (c p : ℝ) ≤
          (Real.log (p : ℝ) - Real.log (r : ℝ)) -
          (if p ∈ P_fold then Real.log 2 else 0) +
          (if p ∈ P_fold then 10 * (r : ℝ) / (k : ℝ) else 0) +
          (if k % p ≤ 2 * r then Real.log (2 * (r : ℝ) / ((k % p - r : ℕ) : ℝ)) else 0) +
          Real.log (1 + (r : ℝ) / (p : ℝ)) := by
      intro p hp
      have hp_mem := hp
      simp only [P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp_mem
      rcases hp_mem with ⟨⟨⟨hrp, hpk⟩, hp_prime⟩, hmod⟩
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hcp_pos : (0 : ℝ) < (c p : ℝ) := by exact_mod_cast (hc_pos p hp)
      have h_log1_nonneg : 0 ≤ Real.log (1 + (r : ℝ) / (p : ℝ)) :=
        Real.log_nonneg (le_add_of_nonneg_right (by positivity))
      by_cases hfold : p ∈ P_fold
      · have hmod_gt : ¬ (k % p ≤ 2 * r) := by
          have := (h_fold_mod p hfold).2
          omega
        rw [if_pos hfold, if_pos hfold, if_neg hmod_gt]
        have hcp_eq : c p = ((p - 1) / 2 + r) / (r + 1) + 1 := if_pos hfold
        set q := ((p - 1) / 2 + r) / (r + 1)
        have hdiv1 : q * (r + 1) ≤ (p - 1) / 2 + r := Nat.div_mul_le_self _ _
        have hdiv2 : ((p - 1) / 2) * 2 ≤ p - 1 := Nat.div_mul_le_self _ _
        have h51 : 51 * k ≤ 100 * p := by
          simp only [P_fold, Finset.mem_filter] at hfold
          exact hfold.2.1
        have h_cp_2r : c p * (2 * r) ≤ p + 5 * r := by
          have hqr : q * r ≤ q * (r + 1) := Nat.mul_le_mul_left q (by omega)
          have hexp : c p * (2 * r) = 2 * (q * r) + 2 * r := by
            rw [hcp_eq]
            ring
          omega
        have h_5rk : 5 * r * k ≤ 10 * r * p := by
          have hk2p : k ≤ 2 * p := by omega
          calc 5 * r * k ≤ 5 * r * (2 * p) := Nat.mul_le_mul_left (5 * r) hk2p
            _ = 10 * r * p := by ring
        have h_nat_ineq : c p * (2 * r) * k ≤ p * (k + 10 * r) := by
          calc c p * (2 * r) * k ≤ (p + 5 * r) * k := Nat.mul_le_mul_right k h_cp_2r
            _ = p * k + 5 * r * k := by ring
            _ ≤ p * k + 10 * r * p := Nat.add_le_add_left h_5rk (p * k)
            _ = p * (k + 10 * r) := by ring
        have h_R_ineq : (c p : ℝ) * (2 * (r : ℝ)) * (k : ℝ) ≤ (p : ℝ) * ((k : ℝ) + 10 * (r : ℝ)) := by
          exact_mod_cast h_nat_ineq
        have h_cp_le : (c p : ℝ) ≤ ((p : ℝ) / (2 * (r : ℝ))) * (1 + 10 * (r : ℝ) / (k : ℝ)) := by
          have h_rhs : ((p : ℝ) / (2 * (r : ℝ))) * (1 + 10 * (r : ℝ) / (k : ℝ)) =
              ((p : ℝ) * ((k : ℝ) + 10 * (r : ℝ))) / ((2 * (r : ℝ)) * (k : ℝ)) := by
            field_simp
          rw [h_rhs, le_div_iff₀ (by positivity)]
          linarith
        have h_log_cp : Real.log (c p : ℝ) ≤
            Real.log (p : ℝ) - Real.log (r : ℝ) - Real.log 2 + 10 * (r : ℝ) / (k : ℝ) := by
          have h1 := Real.log_le_log hcp_pos h_cp_le
          rw [Real.log_mul (by positivity) (by positivity),
              Real.log_div (by positivity) (by positivity),
              Real.log_mul (by positivity) (by positivity)] at h1
          have h2 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + 10 * (r : ℝ) / (k : ℝ))
          linarith
        linarith
      · rw [if_neg hfold, if_neg hfold]
        by_cases h2r : k % p ≤ 2 * r
        · rw [if_pos h2r]
          set d := k % p - r
          have hd1 : 1 ≤ d := by omega
          have hdr : d ≤ r := by omega
          have hd_pos : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hd1
          have hmin : min (r + 1) d = d := Nat.min_eq_right (by omega)
          have hcp_eq : c p = (p + d - 1) / d := by
            dsimp [c]
            rw [if_neg hfold, hmin]
          have hdiv : c p * d ≤ 2 * p := by
            calc c p * d = ((p + d - 1) / d) * d := by rw [hcp_eq]
              _ ≤ p + d - 1 := Nat.div_mul_le_self _ _
              _ ≤ 2 * p := by omega
          have hdiv_R : (c p : ℝ) * (d : ℝ) ≤ 2 * (p : ℝ) := by exact_mod_cast hdiv
          have h_cp_le : (c p : ℝ) ≤ ((p : ℝ) / (r : ℝ)) * (2 * (r : ℝ) / (d : ℝ)) := by
            have h_eq : ((p : ℝ) / (r : ℝ)) * (2 * (r : ℝ) / (d : ℝ)) = 2 * (p : ℝ) / (d : ℝ) := by
              field_simp
            rw [h_eq, le_div_iff₀ hd_pos]
            exact hdiv_R
          have h_log_cp : Real.log (c p : ℝ) ≤
              Real.log (p : ℝ) - Real.log (r : ℝ) + Real.log (2 * (r : ℝ) / (d : ℝ)) := by
            have h1 := Real.log_le_log hcp_pos h_cp_le
            rw [Real.log_mul (by positivity) (by positivity),
                Real.log_div (by positivity) (by positivity)] at h1
            linarith
          linarith
        · rw [if_neg h2r]
          set d := k % p - r
          have hdr1 : r + 1 ≤ d := by omega
          have hmin : min (r + 1) d = r + 1 := Nat.min_eq_left hdr1
          have hcp_eq : c p = (p + r) / (r + 1) := by
            dsimp [c]
            rw [if_neg hfold, hmin]
            have hpr : p + (r + 1) - 1 = p + r := by omega
            rw [hpr]
          have hdiv : c p * r ≤ p + r := by
            have h1 : c p * (r + 1) ≤ p + r := by
              rw [hcp_eq]
              exact Nat.div_mul_le_self _ _
            nlinarith
          have hdiv_R : (c p : ℝ) * (r : ℝ) ≤ (p : ℝ) + (r : ℝ) := by exact_mod_cast hdiv
          have h_cp_le : (c p : ℝ) ≤ ((p : ℝ) / (r : ℝ)) * (1 + (r : ℝ) / (p : ℝ)) := by
            have h_eq : ((p : ℝ) / (r : ℝ)) * (1 + (r : ℝ) / (p : ℝ)) = ((p : ℝ) + (r : ℝ)) / (r : ℝ) := by
              field_simp
            rw [h_eq, le_div_iff₀ hr_pos]
            exact hdiv_R
          have h_log_cp : Real.log (c p : ℝ) ≤
              Real.log (p : ℝ) - Real.log (r : ℝ) + Real.log (1 + (r : ℝ) / (p : ℝ)) := by
            have h1 := Real.log_le_log hcp_pos h_cp_le
            rw [Real.log_mul (by positivity) (by positivity),
                Real.log_div (by positivity) (by positivity)] at h1
            linarith
          linarith
    have h_log_prod : Real.log (Q : ℝ) = ∑ p ∈ P_inact, Real.log (c p : ℝ) := by
      dsimp [Q]
      push_cast
      rw [Real.log_prod]
      intro p hp
      have : (0 : ℝ) < (c p : ℝ) := by exact_mod_cast (hc_pos p hp)
      exact ne_of_gt this
    have h_sum_le := Finset.sum_le_sum h_ptwise
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_sub_distrib] at h_sum_le
    have h_filter_fold : P_inact.filter (fun p => p ∈ P_fold) = P_fold := by
      ext p
      simp only [Finset.mem_filter]
      exact ⟨fun h => h.2, fun h => ⟨h_fold_sub h, h⟩⟩
    have h_sum_fold1 : ∑ p ∈ P_inact, (if p ∈ P_fold then Real.log 2 else 0) = Real.log 2 * (P_fold.card : ℝ) := by
      rw [← Finset.sum_filter, h_filter_fold, Finset.sum_const, nsmul_eq_mul]
      ring
    have h_sum_fold2 : ∑ p ∈ P_inact, (if p ∈ P_fold then 10 * (r : ℝ) / (k : ℝ) else 0) ≤ 10 * (r : ℝ) := by
      rw [← Finset.sum_filter, h_filter_fold, Finset.sum_const, nsmul_eq_mul]
      have h_card_le_k : P_fold.card ≤ k := by
        have hsub : P_fold ⊆ Finset.Ioc r k :=
          Finset.Subset.trans (Finset.filter_subset _ _) (Finset.filter_subset _ _)
        have hcard := Finset.card_le_card hsub
        rw [Nat.card_Ioc] at hcard
        omega
      have h_card_R : (P_fold.card : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr h_card_le_k
      calc (P_fold.card : ℝ) * (10 * (r : ℝ) / (k : ℝ))
        _ ≤ (k : ℝ) * (10 * (r : ℝ) / (k : ℝ)) := mul_le_mul_of_nonneg_right h_card_R (by positivity)
        _ = 10 * (r : ℝ) := mul_div_cancel₀ _ (ne_of_gt hk_pos)
    have h_sum_B : ∑ p ∈ P_inact, (if k % p ≤ 2 * r then Real.log (2 * (r : ℝ) / ((k % p - r : ℕ) : ℝ)) else 0) =
        ∑ p ∈ B, Real.log (2 * (r : ℝ) / ((k % p - r : ℕ) : ℝ)) := by
      rw [← Finset.sum_filter]
    have h_sum_all : ∑ p ∈ P_inact, Real.log (1 + (r : ℝ) / (p : ℝ)) ≤
        ∑ p ∈ P_all, Real.log (1 + (r : ℝ) / (p : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      simp only [P_all, Finset.mem_filter] at hp
      have : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.2.pos
      exact Real.log_nonneg (le_add_of_nonneg_right (by positivity))
    linarith
  
  have hs3 : ∑ p ∈ B, Real.log (2 * (r : ℝ) / ((k % p - r : ℕ) : ℝ)) ≤ 2 * (r : ℝ) := by
    clear hs1 hs2 Q c P_fold G
    set f : ℕ → ℕ := fun p => k % p - r
    set g : ℕ → ℝ := fun x => 2 * (r : ℝ) / (x : ℝ)
    have hr1 : 1 ≤ r := by omega
    have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr1
    have hB_mem : ∀ p ∈ B, Nat.Prime p ∧ r < p ∧ p ≤ k ∧ r < k % p ∧ k % p ≤ 2 * r := by
      intro p hp
      simp only [B, P_inact, P_all, Finset.mem_filter, Finset.mem_Ioc] at hp
      exact ⟨hp.1.1.2, hp.1.1.1.1, hp.1.1.1.2, hp.1.2, hp.2⟩
    have hf_mem : ∀ p ∈ B, f p ∈ Finset.Ico 1 (r + 1) := by
      intro p hp
      obtain ⟨_, _, _, h1, h2⟩ := hB_mem p hp
      simp only [f, Finset.mem_Ico]
      omega
    have hf_sub : B.image f ⊆ Finset.Ico 1 (r + 1) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
      exact hf_mem p hp
    have hf_inj : Set.InjOn f B := by
      intro p1 hp1 p2 hp2 hfeq
      obtain ⟨hp1_prime, hr_p1, hp1_k, hmod1_gt, hmod1_le⟩ := hB_mem p1 hp1
      obtain ⟨hp2_prime, hr_p2, hp2_k, hmod2_gt, hmod2_le⟩ := hB_mem p2 hp2
      have hmod_eq : k % p1 = k % p2 := by
        dsimp [f] at hfeq
        omega
      by_contra hne
      have hcop : Nat.Coprime p1 p2 := (Nat.coprime_primes hp1_prime hp2_prime).mpr hne
      have hdvd1 : p1 ∣ k - k % p1 := Nat.dvd_sub_mod k
      have hdvd2 : p2 ∣ k - k % p1 := by
        rw [hmod_eq]
        exact Nat.dvd_sub_mod k
      have hmul_dvd : p1 * p2 ∣ k - k % p1 := Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hdvd1 hdvd2
      have hsub_pos : 0 < k - k % p1 := by omega
      have hmul_le : p1 * p2 ≤ k - k % p1 := Nat.le_of_dvd hsub_pos hmul_dvd
      have hsqrt_lt : k < (Nat.sqrt k + 1) * (Nat.sqrt k + 1) := Nat.lt_succ_sqrt k
      have hp1_ge : Nat.sqrt k + 1 ≤ p1 := by omega
      have hp2_ge : Nat.sqrt k + 1 ≤ p2 := by omega
      have hmul_ge : (Nat.sqrt k + 1) * (Nat.sqrt k + 1) ≤ p1 * p2 := Nat.mul_le_mul hp1_ge hp2_ge
      omega
    have hg_one_le : ∀ x ∈ Finset.Ico 1 (r + 1), 1 ≤ g x := by
      intro x hx
      simp only [Finset.mem_Ico] at hx
      dsimp [g]
      have hx_pos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (by omega : 0 < x)
      rw [one_le_div hx_pos]
      have hxr : (x : ℝ) ≤ (r : ℝ) := by exact_mod_cast (by omega : x ≤ r)
      linarith
    have hg_pos_Ico : ∀ x ∈ Finset.Ico 1 (r + 1), 0 < g x := by
      intro x hx
      have := hg_one_le x hx
      linarith
    have h_sum_le_Ico : ∑ p ∈ B, Real.log (g (f p)) ≤ ∑ x ∈ Finset.Ico 1 (r + 1), Real.log (g x) := by
      rw [← Finset.sum_image (f := fun x => Real.log (g x)) hf_inj]
      exact Finset.sum_le_sum_of_subset_of_nonneg hf_sub (fun x hx _ => Real.log_nonneg (hg_one_le x hx))
    have h_sum_Ico_eq_log_prod : ∑ x ∈ Finset.Ico 1 (r + 1), Real.log (g x) = Real.log (∏ x ∈ Finset.Ico 1 (r + 1), g x) := by
      rw [Real.log_prod]
      intro x hx
      exact ne_of_gt (hg_pos_Ico x hx)
    have h_prod_Ico_pos : 0 < ∏ x ∈ Finset.Ico 1 (r + 1), g x := Finset.prod_pos hg_pos_Ico
    have h_prod_Ico_eq : ∏ x ∈ Finset.Ico 1 (r + 1), g x = (2 : ℝ) ^ r * ((r : ℝ) ^ r / (r.factorial : ℝ)) := by
      dsimp [g]
      rw [Finset.prod_div_distrib, Finset.prod_const]
      have hcard : (Finset.Ico 1 (r + 1)).card = r := by simp
      have hfact : (∏ x ∈ Finset.Ico 1 (r + 1), (x : ℝ)) = (r.factorial : ℝ) := by
        rw [← Nat.cast_prod, Finset.prod_Ico_id_eq_factorial]
      rw [hcard, hfact, mul_pow, mul_div_assoc]
    have h_rr_fact_le_exp : (r : ℝ) ^ r / (r.factorial : ℝ) ≤ Real.exp (r : ℝ) := by
      have h_sum := Real.sum_le_exp_of_nonneg (le_of_lt hr_pos) (r + 1)
      have h_mem : r ∈ Finset.range (r + 1) := Finset.mem_range.mpr (by omega)
      have h_nonneg : ∀ i ∈ Finset.range (r + 1), 0 ≤ (r : ℝ) ^ i / (i.factorial : ℝ) := by
        intro i _
        positivity
      exact le_trans (Finset.single_le_sum h_nonneg h_mem) h_sum
    have h_prod_le_exp : ∏ x ∈ Finset.Ico 1 (r + 1), g x ≤ (2 : ℝ) ^ r * Real.exp (r : ℝ) := by
      rw [h_prod_Ico_eq]
      exact mul_le_mul_of_nonneg_left h_rr_fact_le_exp (by positivity)
    have h_log_le : Real.log (∏ x ∈ Finset.Ico 1 (r + 1), g x) ≤ (r : ℝ) * Real.log 2 + (r : ℝ) := by
      calc Real.log (∏ x ∈ Finset.Ico 1 (r + 1), g x)
        _ ≤ Real.log ((2 : ℝ) ^ r * Real.exp (r : ℝ)) := Real.log_le_log h_prod_Ico_pos h_prod_le_exp
        _ = Real.log ((2 : ℝ) ^ r) + Real.log (Real.exp (r : ℝ)) :=
            Real.log_mul (by positivity) (by positivity)
        _ = (r : ℝ) * Real.log 2 + (r : ℝ) := by rw [Real.log_pow, Real.log_exp]
    have h_log2 : Real.log 2 < 1 := by linarith [Real.log_two_lt_d9]
    calc ∑ p ∈ B, Real.log (2 * (r : ℝ) / ((k % p - r : ℕ) : ℝ))
      _ = ∑ p ∈ B, Real.log (g (f p)) := rfl
      _ ≤ ∑ x ∈ Finset.Ico 1 (r + 1), Real.log (g x) := h_sum_le_Ico
      _ = Real.log (∏ x ∈ Finset.Ico 1 (r + 1), g x) := h_sum_Ico_eq_log_prod
      _ ≤ (r : ℝ) * Real.log 2 + (r : ℝ) := h_log_le
      _ ≤ (r : ℝ) * 1 + (r : ℝ) := by nlinarith
      _ = 2 * (r : ℝ) := by ring
  
  have hs4 : ∑ p ∈ P_all, Real.log (1 + (r : ℝ) / (p : ℝ)) ≤
      6 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) +
      20 * (k : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) := by
    clear hs1 hs2 hs3 Q c P_fold B P_inact G
    set X := (r : ℝ) * Real.log (k : ℝ)
    set Y := Nat.floor X
    have hr2 : 2 ≤ r := by
      have : 1 ≤ Nat.sqrt k := Nat.sqrt_pos.mpr (by omega)
      omega
    have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (by omega : 0 < r)
    have hk_pos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast (by omega : 0 < k)
    have hlogr_pos : 0 < Real.log (r : ℝ) := Real.log_pos (by exact_mod_cast hr2)
    have hlogk_pos : 0 < Real.log (k : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < k))
    have hX_nonneg : 0 ≤ X := by positivity
    have hlog2_le_one : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hlog4_le : Real.log 4 + 4 ≤ 6 := by
      have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
      rw [h4, Real.log_pow]
      push_cast
      linarith [Real.log_two_lt_d9]
    have h_ptwise : ∀ p ∈ P_all,
        Real.log (1 + (r : ℝ) / (p : ℝ)) ≤
          (if p ≤ Y then Real.log (p : ℝ) / Real.log (r : ℝ) else 0) +
          Real.log (p : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) := by
      intro p hp
      simp only [P_all, Finset.mem_filter, Finset.mem_Ioc] at hp
      rcases hp with ⟨⟨hrp, hpk⟩, hp_prime⟩
      have hp_pos : (0 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 0 < p)
      have hrp_R : (r : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : r ≤ p)
      have hlog_rp : Real.log (r : ℝ) ≤ Real.log (p : ℝ) := Real.log_le_log hr_pos hrp_R
      have h_ratio_ge_one : 1 ≤ Real.log (p : ℝ) / Real.log (r : ℝ) := (one_le_div hlogr_pos).mpr hlog_rp
      have h_second_nonneg : 0 ≤ Real.log (p : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) := by
        have : 0 ≤ Real.log (p : ℝ) := le_trans (le_of_lt hlogr_pos) hlog_rp
        positivity
      split_ifs with hpY
      · have hdiv_le_one : (r : ℝ) / (p : ℝ) ≤ 1 := (div_le_one hp_pos).mpr hrp_R
        have h_arg_pos : 0 < 1 + (r : ℝ) / (p : ℝ) := by positivity
        have h_log_le_log2 : Real.log (1 + (r : ℝ) / (p : ℝ)) ≤ Real.log 2 := by
          apply Real.log_le_log h_arg_pos
          linarith
        linarith
      · have hYp : Y + 1 ≤ p := by omega
        have hXp : X < (p : ℝ) := by
          calc X < (Y : ℝ) + 1 := Nat.lt_floor_add_one X
            _ = ((Y + 1 : ℕ) : ℝ) := by push_cast; ring
            _ ≤ (p : ℝ) := Nat.cast_le.mpr hYp
        have h_r_div_p : (r : ℝ) / (p : ℝ) ≤ 1 / Real.log (k : ℝ) := by
          rw [div_le_div_iff₀ hp_pos hlogk_pos]
          linarith
        have h_arg_pos : 0 < 1 + (r : ℝ) / (p : ℝ) := by positivity
        have h_log_le_rp : Real.log (1 + (r : ℝ) / (p : ℝ)) ≤ (r : ℝ) / (p : ℝ) := by
          have := Real.log_le_sub_one_of_pos h_arg_pos
          linarith
        have h_inv_le : 1 / Real.log (k : ℝ) ≤ Real.log (p : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) := by
          rw [div_mul_eq_div_div]
          exact div_le_div_of_nonneg_right h_ratio_ge_one (le_of_lt hlogk_pos)
        linarith
    have h_sum_le := Finset.sum_le_sum h_ptwise
    rw [Finset.sum_add_distrib] at h_sum_le
    have h_sum1 : ∑ p ∈ P_all, (if p ≤ Y then Real.log (p : ℝ) / Real.log (r : ℝ) else 0) ≤
        6 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) := by
      rw [← Finset.sum_filter, ← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (le_of_lt hlogr_pos)
      have hsub : P_all.filter (fun p => p ≤ Y) ⊆ (Finset.Icc 0 Y).filter Nat.Prime := by
        intro p hp
        simp only [P_all, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨by omega, hp.2⟩, hp.1.2⟩
      have hnonneg : ∀ p ∈ (Finset.Icc 0 Y).filter Nat.Prime, p ∉ P_all.filter (fun p => p ≤ Y) → 0 ≤ Real.log (p : ℝ) := by
        intro p hp _
        simp only [Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
      have h_le_theta : ∑ p ∈ P_all.filter (fun p => p ≤ Y), Real.log (p : ℝ) ≤ Chebyshev.theta X := by
        rw [Chebyshev.theta_eq_sum_Icc]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      have h_theta_le : Chebyshev.theta X ≤ (Real.log 4 + 4) * X :=
        le_trans (Chebyshev.theta_le_psi X) (Chebyshev.psi_le_const_mul_self hX_nonneg)
      dsimp [X] at h_theta_le ⊢
      nlinarith
    have h_sum2 : ∑ p ∈ P_all, Real.log (p : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) ≤
        20 * (k : ℝ) / (Real.log (r : ℝ) * Real.log (k : ℝ)) := by
      rw [← Finset.sum_div]
      apply div_le_div_of_nonneg_right _ (by positivity)
      have hsub : P_all ⊆ (Finset.Icc 0 k).filter Nat.Prime := by
        intro p hp
        simp only [P_all, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
      have hnonneg : ∀ p ∈ (Finset.Icc 0 k).filter Nat.Prime, p ∉ P_all → 0 ≤ Real.log (p : ℝ) := by
        intro p hp _
        simp only [Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
      have h_le_theta : ∑ p ∈ P_all, Real.log (p : ℝ) ≤ Chebyshev.theta (k : ℝ) := by
        rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg
      have h_theta_le : Chebyshev.theta (k : ℝ) ≤ (Real.log 4 + 4) * (k : ℝ) :=
        le_trans (Chebyshev.theta_le_psi (k : ℝ)) (Chebyshev.psi_le_const_mul_self (le_of_lt hk_pos))
      nlinarith
    linarith
  
  have hs5 : ∑ p ∈ P_inact, (Real.log (p : ℝ) - Real.log (r : ℝ)) ≤
      Chebyshev.theta (k : ℝ) - (k.primeCounting : ℝ) * Real.log (r : ℝ) +
      13 * (r : ℝ) := by
    clear hs1 hs2 hs3 hs4 Q c P_fold B G
    set P_le_k := (Finset.Icc 0 k).filter Nat.Prime
    set P_le_r := (Finset.Icc 0 r).filter Nat.Prime
    have hr1 : 1 ≤ r := by omega
    have hr_pos : (0 : ℝ) < (r : ℝ) := Nat.cast_pos.mpr hr1
    have hlogr_nonneg : 0 ≤ Real.log (r : ℝ) := Real.log_nonneg (by exact_mod_cast hr1)
    have h_inact_le_all : ∑ p ∈ P_inact, (Real.log (p : ℝ) - Real.log (r : ℝ)) ≤
        ∑ p ∈ P_all, (Real.log (p : ℝ) - Real.log (r : ℝ)) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro p hp _
      simp only [P_all, Finset.mem_filter, Finset.mem_Ioc] at hp
      have : (r : ℝ) ≤ (p : ℝ) := by exact_mod_cast (by omega : r ≤ p)
      linarith [Real.log_le_log hr_pos this]
    have h_all_eq : ∑ p ∈ P_all, (Real.log (p : ℝ) - Real.log (r : ℝ)) =
        ∑ p ∈ P_all, Real.log (p : ℝ) - (P_all.card : ℝ) * Real.log (r : ℝ) := by
      rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
    have h_sum_all_le_theta : ∑ p ∈ P_all, Real.log (p : ℝ) ≤ Chebyshev.theta (k : ℝ) := by
      rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        simp only [P_all, Finset.mem_filter, Finset.mem_Ioc, Finset.mem_Icc] at hp ⊢
        exact ⟨⟨by omega, hp.1.2⟩, hp.2⟩
      · intro p hp _
        simp only [Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
    have h_union : P_le_k = P_le_r ∪ P_all := by
      ext p
      simp only [P_le_k, P_le_r, P_all, Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
      constructor
      · rintro ⟨⟨_, hpk⟩, hp⟩
        by_cases hpr : p ≤ r
        · left; exact ⟨⟨by omega, hpr⟩, hp⟩
        · right; exact ⟨⟨by omega, hpk⟩, hp⟩
      · rintro (⟨⟨_, hpr⟩, hp⟩ | ⟨⟨hrp, hpk⟩, hp⟩)
        · exact ⟨⟨by omega, by omega⟩, hp⟩
        · exact ⟨⟨by omega, hpk⟩, hp⟩
    have h_disj : Disjoint P_le_r P_all := by
      rw [Finset.disjoint_left]
      intro p hp1 hp2
      simp only [P_le_r, P_all, Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc] at hp1 hp2
      omega
    have h_card_union : P_le_k.card = P_le_r.card + P_all.card := by
      rw [h_union, Finset.card_union_of_disjoint h_disj]
    have h_primeCounting : k.primeCounting = P_le_k.card := by
      rw [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
      congr 2
      ext x
      simp only [Finset.mem_range, Finset.mem_Icc]
      omega
    have h_card_R : (k.primeCounting : ℝ) = (P_le_r.card : ℝ) + (P_all.card : ℝ) := by
      exact_mod_cast (h_primeCounting.trans h_card_union)
    have h_card_mul : (k.primeCounting : ℝ) * Real.log (r : ℝ) =
        (P_le_r.card : ℝ) * Real.log (r : ℝ) + (P_all.card : ℝ) * Real.log (r : ℝ) := by
      rw [h_card_R, add_mul]
    have h_Pr_bound : (P_le_r.card : ℝ) * Real.log (r : ℝ) ≤ 13 * (r : ℝ) := by
      set sr := Nat.sqrt r
      set P_small := P_le_r.filter (fun p => p ≤ sr)
      set P_large := P_le_r.filter (fun p => ¬ p ≤ sr)
      have h_card_split : P_le_r.card = P_small.card + P_large.card :=
        (Finset.filter_card_add_filter_neg_card_eq_card (fun p => p ≤ sr)).symm
      have h_small_card : (P_small.card : ℝ) ≤ Real.sqrt (r : ℝ) := by
        have hsub : P_small ⊆ Finset.Icc 1 sr := by
          intro p hp
          simp only [P_small, P_le_r, Finset.mem_filter, Finset.mem_Icc] at hp ⊢
          exact ⟨hp.1.2.one_le, hp.2⟩
        have h1 : P_small.card ≤ sr := by
          have := Finset.card_le_card hsub
          simpa using this
        have h_sqrt_le : (sr : ℝ) ≤ Real.sqrt (r : ℝ) := by
          rw [← Real.sqrt_sq (Nat.cast_nonneg sr)]
          apply Real.sqrt_le_sqrt
          exact_mod_cast (by simpa [sq, sr] using Nat.sqrt_le r : sr ^ 2 ≤ r)
        exact le_trans (Nat.cast_le.mpr h1) h_sqrt_le
      have h_sqrtr_pos : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hr_pos
      have h_logr_eq : Real.log (r : ℝ) = 2 * Real.log (Real.sqrt (r : ℝ)) := by
        have : (r : ℝ) = Real.sqrt (r : ℝ) ^ 2 := (Real.sq_sqrt (le_of_lt hr_pos)).symm
        conv_lhs => rw [this, Real.log_pow]
        ring
      have h_small_bound : (P_small.card : ℝ) * Real.log (r : ℝ) ≤ 2 * (r : ℝ) := by
        have h_log_sqrt : Real.log (Real.sqrt (r : ℝ)) ≤ Real.sqrt (r : ℝ) := by
          have := Real.log_le_sub_one_of_pos h_sqrtr_pos
          linarith
        have h_logr_le : Real.log (r : ℝ) ≤ 2 * Real.sqrt (r : ℝ) := by linarith
        calc (P_small.card : ℝ) * Real.log (r : ℝ)
          _ ≤ Real.sqrt (r : ℝ) * Real.log (r : ℝ) := mul_le_mul_of_nonneg_right h_small_card hlogr_nonneg
          _ ≤ Real.sqrt (r : ℝ) * (2 * Real.sqrt (r : ℝ)) := mul_le_mul_of_nonneg_left h_logr_le (le_of_lt h_sqrtr_pos)
          _ = 2 * (Real.sqrt (r : ℝ) ^ 2) := by ring
          _ = 2 * (r : ℝ) := by rw [Real.sq_sqrt (le_of_lt hr_pos)]
      have h_large_bound : (P_large.card : ℝ) * Real.log (r : ℝ) ≤ 11 * (r : ℝ) := by
        have h_eq_sum : (P_large.card : ℝ) * Real.log (r : ℝ) = ∑ p ∈ P_large, Real.log (r : ℝ) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        have h_ptwise : ∀ p ∈ P_large, Real.log (r : ℝ) ≤ 2 * Real.log (p : ℝ) := by
          intro p hp
          simp only [P_large, P_le_r, Finset.mem_filter, Finset.mem_Icc] at hp
          have hsr_p : sr + 1 ≤ p := by omega
          have h_sqrtr_le_p : Real.sqrt (r : ℝ) ≤ (p : ℝ) := by
            have hlt : r < (sr + 1) ^ 2 := by
              simpa [sq] using Nat.lt_succ_sqrt r
            have hlt_R : (r : ℝ) < ((sr + 1 : ℕ) : ℝ) ^ 2 := by exact_mod_cast hlt
            have hle_sr : Real.sqrt (r : ℝ) ≤ ((sr + 1 : ℕ) : ℝ) := by
              rw [← Real.sqrt_sq (by positivity : (0 : ℝ) ≤ ((sr + 1 : ℕ) : ℝ))]
              exact Real.sqrt_le_sqrt (le_of_lt hlt_R)
            exact le_trans hle_sr (Nat.cast_le.mpr hsr_p)
          have : Real.log (Real.sqrt (r : ℝ)) ≤ Real.log (p : ℝ) :=
            Real.log_le_log h_sqrtr_pos h_sqrtr_le_p
          linarith
        have h_sum_large_le : ∑ p ∈ P_large, Real.log (r : ℝ) ≤ 2 * ∑ p ∈ P_le_r, Real.log (p : ℝ) := by
          calc ∑ p ∈ P_large, Real.log (r : ℝ)
            _ ≤ ∑ p ∈ P_large, 2 * Real.log (p : ℝ) := Finset.sum_le_sum h_ptwise
            _ = 2 * ∑ p ∈ P_large, Real.log (p : ℝ) := (Finset.mul_sum _ _ _).symm
            _ ≤ 2 * ∑ p ∈ P_le_r, Real.log (p : ℝ) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
              intro p hp _
              simp only [P_le_r, Finset.mem_filter] at hp
              exact Real.log_nonneg (by exact_mod_cast hp.2.one_le)
        have h_theta_r : ∑ p ∈ P_le_r, Real.log (p : ℝ) = Chebyshev.theta (r : ℝ) := by
          rw [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
        have h_theta_le : Chebyshev.theta (r : ℝ) ≤ (Real.log 4 + 4) * (r : ℝ) :=
          le_trans (Chebyshev.theta_le_psi (r : ℝ)) (Chebyshev.psi_le_const_mul_self (le_of_lt hr_pos))
        have hlog4 : Real.log 4 + 4 ≤ 5.5 := by
          have h4 : (4 : ℝ) = (2 : ℝ) ^ 2 := by norm_num
          rw [h4, Real.log_pow]
          push_cast
          linarith [Real.log_two_lt_d9]
        nlinarith
      have h_card_split_R : (P_le_r.card : ℝ) = (P_small.card : ℝ) + (P_large.card : ℝ) := by
        exact_mod_cast h_card_split
      nlinarith
    linarith
  
  rcases hs1 with ⟨h1G, hrG, hlog2G⟩
  rcases hs2 with ⟨h1Q, hlogQ⟩
  have hr2 : 2 ≤ r := by
    have : 1 ≤ Nat.sqrt k := Nat.sqrt_pos.mpr (by omega)
    omega
  have hrk : r ≤ k := by omega
  have hGQ_le : G * Q + r ≤ 2 * G * Q := by
    have hrGQ : r ≤ G * Q := by
      calc r ≤ G := hrG
        _ = G * 1 := (Nat.mul_one G).symm
        _ ≤ G * Q := Nat.mul_le_mul_left G h1Q
    have h2GQ : 2 * G * Q = G * Q + G * Q := by ring
    omega
  have hGQr_pos : (0 : ℝ) < ((G * Q + r : ℕ) : ℝ) := by
    exact Nat.cast_pos.mpr (by omega)
  have h2G_pos : (0 : ℝ) < 2 * (G : ℝ) := by
    have : (0 : ℝ) < (G : ℝ) := Nat.cast_pos.mpr (by omega)
    linarith
  have hQ_pos : (0 : ℝ) < (Q : ℝ) := Nat.cast_pos.mpr (by omega)
  have hlog_add_r : Real.log (((G * Q + r : ℕ) : ℝ)) ≤ Real.log (2 * (G : ℝ)) + Real.log (Q : ℝ) := by
    calc Real.log (((G * Q + r : ℕ) : ℝ))
      _ ≤ Real.log (((2 * G * Q : ℕ) : ℝ)) := Real.log_le_log hGQr_pos (Nat.cast_le.mpr hGQ_le)
      _ = Real.log ((2 * (G : ℝ)) * (Q : ℝ)) := by push_cast; ring_nf
      _ = Real.log (2 * (G : ℝ)) + Real.log (Q : ℝ) := Real.log_mul (ne_of_gt h2G_pos) (ne_of_gt hQ_pos)
  have hlogr_pos : 0 < Real.log (r : ℝ) := by
    apply Real.log_pos
    exact_mod_cast hr2
  have hlog_rk : Real.log (r : ℝ) ≤ Real.log (k : ℝ) := by
    apply Real.log_le_log
    · exact_mod_cast (by omega : 0 < r)
    · exact_mod_cast hrk
  have h_one_le_ratio : 1 ≤ Real.log (k : ℝ) / Real.log (r : ℝ) := by
    rw [one_le_div hlogr_pos]
    exact hlog_rk
  have hr_nonneg : 0 ≤ (r : ℝ) := Nat.cast_nonneg r
  have h_r_44 : 38 * (r : ℝ) + 6 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) ≤
      50 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) := by
    have h1 : (r : ℝ) ≤ (r : ℝ) * (Real.log (k : ℝ) / Real.log (r : ℝ)) :=
      le_mul_of_one_le_right hr_nonneg h_one_le_ratio
    have h6 : 6 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) =
        6 * ((r : ℝ) * (Real.log (k : ℝ) / Real.log (r : ℝ))) := by ring
    have h50 : 50 * (r : ℝ) * Real.log (k : ℝ) / Real.log (r : ℝ) =
        50 * ((r : ℝ) * (Real.log (k : ℝ) / Real.log (r : ℝ))) := by ring
    linarith
  linarith

theorem psi_laplace_eq_neg_zeta_log_deriv {z : ℂ} (hz : 0 < z.re) :
    ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1 : ℝ) : ℂ) *
      Complex.exp (-z * (t : ℂ)) =
      -deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z :=
by
  have hz_ne : z ≠ 0 := by
    intro h
    rw [h, Complex.zero_re] at hz
    exact lt_irrefl 0 hz
  have h1z_re : 1 < (1 + z).re := by
    simp only [Complex.add_re, Complex.one_re, lt_add_iff_pos_right]
    exact hz
  have h1z_ne : 1 + z ≠ 0 := by
    intro h
    have hre := congr_arg Complex.re h
    simp only [Complex.add_re, Complex.one_re, Complex.zero_re] at hre
    linarith
  have h_sum_eq : ∀ m : ℕ,
      ∑ k ∈ Finset.Icc 1 m, ArithmeticFunction.vonMangoldt k =
      ∑ k ∈ Finset.Icc 0 m, ArithmeticFunction.vonMangoldt k := by
    intro m
    have hIcc : Finset.Icc 0 m = insert 0 (Finset.Icc 1 m) := by
      ext k
      simp only [Finset.mem_Icc, Finset.mem_insert]
      omega
    rw [hIcc, Finset.sum_insert (by simp), ArithmeticFunction.map_zero, zero_add]
  have h_sum_real : ∀ u : ℝ,
      ∑ k ∈ Finset.Icc 1 ⌊u⌋₊, ArithmeticFunction.vonMangoldt k = Chebyshev.psi u := by
    intro u
    rw [h_sum_eq, ← Chebyshev.psi_eq_sum_Icc]
  have h_sum_nat : ∀ n : ℕ,
      ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k = Chebyshev.psi (n : ℝ) := by
    intro n
    have hfl : ⌊(n : ℝ)⌋₊ = n := Nat.floor_natCast n
    rw [← h_sum_real (n : ℝ), hfl]
  have h_bigO : (fun n : ℕ => ∑ k ∈ Finset.Icc 1 n, ArithmeticFunction.vonMangoldt k) =O[atTop]
      fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
    apply Asymptotics.IsBigO.of_bound (Real.log 4 + 4)
    filter_upwards with n
    rw [h_sum_nat n, Real.rpow_one, Real.norm_of_nonneg (Chebyshev.psi_nonneg _),
        Real.norm_of_nonneg (Nat.cast_nonneg n)]
    exact Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n)
  have h_mell : ∫ u in Set.Ioi (1 : ℝ), (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-((1 + z) + 1)) =
      -deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) := by
    have h_ls := LSeries_eq_mul_integral_of_nonneg ArithmeticFunction.vonMangoldt
      (by norm_num : (0 : ℝ) ≤ 1) h1z_re h_bigO (fun n => ArithmeticFunction.vonMangoldt_nonneg)
    have h_vm := ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div h1z_re
    rw [h_vm] at h_ls
    have h_int_eq : (∫ u in Set.Ioi (1 : ℝ),
        (∑ k ∈ Finset.Icc 1 ⌊u⌋₊, (ArithmeticFunction.vonMangoldt k : ℂ)) * (u : ℂ) ^ (-((1 + z) + 1))) =
        ∫ u in Set.Ioi (1 : ℝ), (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-((1 + z) + 1)) := by
      congr 1
      ext u
      rw [← Complex.ofReal_sum, h_sum_real]
    rw [h_int_eq] at h_ls
    rw [mul_comm (1 + z) (riemannZeta (1 + z)), ← div_div, eq_div_iff h1z_ne, mul_comm]
    exact h_ls.symm
  have h_cov : ∫ t in Set.Ioi (0 : ℝ), ((Real.exp (-t) * Chebyshev.psi (Real.exp t) : ℝ) : ℂ) *
      Complex.exp (-z * (t : ℂ)) =
      ∫ u in Set.Ioi (1 : ℝ), (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-((1 + z) + 1)) := by
    have h_img : Real.exp '' Set.Ioi (0 : ℝ) = Set.Ioi (1 : ℝ) := by
      ext u
      simp only [Set.mem_image, Set.mem_Ioi]
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact Real.one_lt_exp_iff.mpr ht
      · intro hu
        exact ⟨Real.log u, Real.log_pos hu, Real.exp_log (by linarith)⟩
    have h_subst := MeasureTheory.integral_image_eq_integral_abs_deriv_smul
      (measurableSet_Ioi : MeasurableSet (Set.Ioi (0 : ℝ)))
      (fun t _ => (Real.hasDerivAt_exp t).hasDerivWithinAt)
      Real.exp_strictMono.injective.injOn
      (fun u : ℝ => (Chebyshev.psi u : ℂ) * (u : ℂ) ^ (-((1 + z) + 1)))
    rw [h_img] at h_subst
    rw [h_subst]
    congr 1
    ext t
    rw [abs_of_pos (Real.exp_pos t), Complex.real_smul]
    have hexp_ne : (Real.exp t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero t)
    rw [Complex.cpow_def_of_ne_zero hexp_ne]
    have hlog : Complex.log (Real.exp t : ℂ) = (t : ℂ) := by
      rw [← Complex.ofReal_log (le_of_lt (Real.exp_pos t)), Real.log_exp]
    rw [hlog, Complex.ofReal_mul, Complex.ofReal_exp, Complex.ofReal_exp, Complex.ofReal_neg]
    have hexp_combine : Complex.exp (t : ℂ) * ((Chebyshev.psi (Real.exp t) : ℂ) *
        Complex.exp ((t : ℂ) * (-((1 + z) + 1)))) =
        (Chebyshev.psi (Real.exp t) : ℂ) *
        (Complex.exp (t : ℂ) * Complex.exp ((t : ℂ) * (-((1 + z) + 1)))) := by ring
    have hexp_lhs : Complex.exp (-(t : ℂ)) * (Chebyshev.psi (Real.exp t) : ℂ) *
        Complex.exp (-z * (t : ℂ)) =
        (Chebyshev.psi (Real.exp t) : ℂ) *
        (Complex.exp (-(t : ℂ)) * Complex.exp (-z * (t : ℂ))) := by ring
    rw [hexp_combine, hexp_lhs, ← Complex.exp_add, ← Complex.exp_add]
    congr 2
    ring
  have h_int_exp : MeasureTheory.IntegrableOn (fun t : ℝ => Complex.exp (-z * (t : ℂ))) (Set.Ioi (0 : ℝ)) MeasureTheory.volume := by
    refine (exp_neg_integrableOn_Ioi 0 hz).mono' ?_ ?_
    · exact (Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).aestronglyMeasurable
    · refine Eventually.of_forall (fun t => le_of_eq ?_)
      rw [Complex.norm_exp]
      congr 1
      simp [Complex.mul_re]
  have h_int_psi : MeasureTheory.IntegrableOn
      (fun t : ℝ => ((Real.exp (-t) * Chebyshev.psi (Real.exp t) : ℝ) : ℂ) * Complex.exp (-z * (t : ℂ)))
      (Set.Ioi (0 : ℝ)) MeasureTheory.volume := by
    refine h_int_exp.bdd_mul (c := Real.log 4 + 4) ?_ ?_
    · exact (Complex.continuous_ofReal.measurable.comp
        ((Real.continuous_exp.comp continuous_neg).measurable.mul
          (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable))).aestronglyMeasurable
    · refine Eventually.of_forall (fun t => ?_)
      rw [Complex.norm_real, Real.norm_of_nonneg
        (mul_nonneg (le_of_lt (Real.exp_pos (-t))) (Chebyshev.psi_nonneg _))]
      calc Real.exp (-t) * Chebyshev.psi (Real.exp t)
        _ ≤ Real.exp (-t) * ((Real.log 4 + 4) * Real.exp t) :=
          mul_le_mul_of_nonneg_left (Chebyshev.psi_le_const_mul_self (le_of_lt (Real.exp_pos t)))
            (le_of_lt (Real.exp_pos (-t)))
        _ = (Real.log 4 + 4) * (Real.exp (-t) * Real.exp t) := by ring
        _ = Real.log 4 + 4 := by rw [← Real.exp_add, neg_add_cancel, Real.exp_zero, mul_one]
  have h_lap_one : ∫ t in Set.Ioi (0 : ℝ), Complex.exp (-z * (t : ℂ)) = 1 / z := by
    let F : ℝ → ℂ := fun t => -Complex.exp (-z * (t : ℂ)) / z
    have h_cont : ContinuousWithinAt F (Set.Ici (0 : ℝ)) 0 :=
      ((Complex.continuous_exp.comp (continuous_const.mul Complex.continuous_ofReal)).neg.div_const z).continuousWithinAt
    have h_deriv : ∀ t ∈ Set.Ioi (0 : ℝ), HasDerivAt F (Complex.exp (-z * (t : ℂ))) t := by
      intro t _
      have hd1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 t := Complex.ofRealCLM.hasDerivAt
      have hd2 : HasDerivAt (fun x : ℝ => -z * (x : ℂ)) (-z * 1) t := hd1.const_mul (-z)
      have hd3 : HasDerivAt (fun x : ℝ => Complex.exp (-z * (x : ℂ)))
          (Complex.exp (-z * (t : ℂ)) * (-z * 1)) t := hd2.cexp
      have hd4 : HasDerivAt F (-(Complex.exp (-z * (t : ℂ)) * (-z * 1)) / z) t :=
        hd3.neg.div_const z
      convert hd4 using 1
      field_simp [hz_ne]
    have h_tendsto : Tendsto F atTop (nhds 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      have h_norm : (fun t : ℝ => ‖F t‖) = (fun t : ℝ => Real.exp (-z.re * t) / ‖z‖) := by
        ext t
        simp only [F, norm_div, norm_neg, Complex.norm_exp]
        congr 2
        simp [Complex.mul_re]
      rw [h_norm]
      have h_atBot : Tendsto (fun t : ℝ => -z.re * t) atTop atBot :=
        Tendsto.const_mul_atTop_of_neg (neg_lt_zero.mpr hz) tendsto_id
      have h_exp0 : Tendsto (fun t : ℝ => Real.exp (-z.re * t)) atTop (nhds 0) :=
        Real.tendsto_exp_atBot.comp h_atBot
      simpa using h_exp0.div_const ‖z‖
    have h_ftc := MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto h_cont h_deriv h_int_exp h_tendsto
    rw [h_ftc]
    simp only [F, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
    ring
  have h_sub_eq : (fun t : ℝ => ((Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1 : ℝ) : ℂ) *
      Complex.exp (-z * (t : ℂ))) =
      (fun t : ℝ => ((Real.exp (-t) * Chebyshev.psi (Real.exp t) : ℝ) : ℂ) *
        Complex.exp (-z * (t : ℂ)) - Complex.exp (-z * (t : ℂ))) := by
    ext t
    push_cast
    ring
  rw [h_sub_eq, MeasureTheory.integral_sub h_int_psi h_int_exp, h_cov, h_mell, h_lap_one]

theorem zeta_log_deriv_sub_pole_extension : ∃ (g : ℂ → ℂ) (r0 M0 : ℝ), 0 < r0 ∧ r0 ≤ 1 / 2 ∧ 0 < M0 ∧
      (∀ z : ℂ, z ≠ 0 → 1 + z ≠ 0 → riemannZeta (1 + z) ≠ 0 →
        DifferentiableAt ℂ g z ∧
        g z = -deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z) ∧
      (∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ g z) ∧
      (∀ z : ℂ, ‖z‖ ≤ r0 → DifferentiableAt ℂ g z ∧ ‖g z‖ ≤ M0) :=
by
  let h : ℂ → ℂ := fun s => if s = 1 then 1 else (s - 1) * riemannZeta s
  let g : ℂ → ℂ := fun z => -deriv h (1 + z) / ((1 + z) * h (1 + z)) - 1 / (1 + z)
  have hh_diff : Differentiable ℂ h := by
    rw [← differentiableOn_univ]
    have h_univ : (Set.univ : Set ℂ) ∈ nhds (1 : ℂ) := Filter.univ_mem
    rw [← Complex.differentiableOn_compl_singleton_and_continuousAt_iff h_univ]
    refine ⟨?_, ?_⟩
    · intro s hs
      have hs1 : s ≠ 1 := by simpa using hs
      have h_eq : h =ᶠ[nhds s] fun w => (w - 1) * riemannZeta w := by
        filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
        dsimp only [h]
        rw [if_neg hw]
      have h_diff_s : DifferentiableAt ℂ (fun w => (w - 1) * riemannZeta w) s :=
        (differentiableAt_id.sub (differentiableAt_const 1)).mul (differentiableAt_riemannZeta hs1)
      exact (h_eq.differentiableAt_iff.mpr h_diff_s).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self]
      change Filter.Tendsto h (nhdsWithin 1 {1}ᶜ) (nhds (h 1))
      have h1 : h 1 = 1 := by dsimp only [h]; rw [if_pos rfl]
      rw [h1]
      refine riemannZeta_residue_one.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with s hs
      have hs1 : s ≠ 1 := by simpa using hs
      dsimp only [h]
      rw [if_neg hs1]
  have hdh_diff : Differentiable ℂ (deriv h) :=
    differentiableOn_univ.mp ((differentiableOn_univ.mpr hh_diff).deriv isOpen_univ)
  have hdh_eq : ∀ s : ℂ, s ≠ 1 → deriv h s = riemannZeta s + (s - 1) * deriv riemannZeta s := by
    intro s hs
    have h_eq : h =ᶠ[nhds s] fun w => (w - 1) * riemannZeta w := by
      filter_upwards [isOpen_ne.mem_nhds hs] with w hw
      dsimp only [h]
      rw [if_neg hw]
    rw [h_eq.deriv_eq]
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => w - 1) s :=
      differentiableAt_id.sub (differentiableAt_const 1)
    have hd2 : DifferentiableAt ℂ riemannZeta s := differentiableAt_riemannZeta hs
    have hmul : deriv (fun w => (w - 1) * riemannZeta w) s =
        deriv (fun w => w - 1) s * riemannZeta s + (s - 1) * deriv riemannZeta s :=
      deriv_mul hd1 hd2
    rw [hmul, deriv_sub_const, deriv_id'', one_mul]
  have hg_diff_of_ne : ∀ z : ℂ, 1 + z ≠ 0 → h (1 + z) ≠ 0 → DifferentiableAt ℂ g z := by
    intro z h1z hh1z
    have hphi : DifferentiableAt ℂ (fun w : ℂ => 1 + w) z :=
      (differentiableAt_const 1).add differentiableAt_id
    have hdh_z : DifferentiableAt ℂ (fun w : ℂ => deriv h (1 + w)) z :=
      (hdh_diff.differentiableAt).comp z hphi
    have hh_z : DifferentiableAt ℂ (fun w : ℂ => h (1 + w)) z :=
      (hh_diff.differentiableAt).comp z hphi
    exact ((hdh_z.neg.div (hphi.mul hh_z) (mul_ne_zero h1z hh1z)).sub
      ((differentiableAt_const 1).div hphi h1z))
  have hg_away : ∀ z : ℂ, z ≠ 0 → 1 + z ≠ 0 → riemannZeta (1 + z) ≠ 0 →
      DifferentiableAt ℂ g z ∧
      g z = -deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z := by
    intro z hz h1z hzeta
    have h1z_ne_one : 1 + z ≠ 1 := by
      intro h_eq
      apply hz
      linear_combination h_eq
    have h1z_sub : (1 + z) - 1 = z := by ring
    have hh1z_eq : h (1 + z) = z * riemannZeta (1 + z) := by
      dsimp only [h]
      rw [if_neg h1z_ne_one, h1z_sub]
    have hh1z_ne : h (1 + z) ≠ 0 := by
      rw [hh1z_eq]
      exact mul_ne_zero hz hzeta
    refine ⟨hg_diff_of_ne z h1z hh1z_ne, ?_⟩
    dsimp only [g]
    rw [hdh_eq (1 + z) h1z_ne_one, h1z_sub, hh1z_eq]
    field_simp
    ring
  have hg_right : ∀ z : ℂ, 0 ≤ z.re → DifferentiableAt ℂ g z := by
    intro z hz_re
    have h1z_re : 1 ≤ (1 + z).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have h1z_ne : 1 + z ≠ 0 := by
      intro h_eq
      rw [h_eq, Complex.zero_re] at h1z_re
      linarith
    apply hg_diff_of_ne z h1z_ne
    rcases eq_or_ne z 0 with rfl | hz_ne
    · dsimp only [h]
      rw [add_zero, if_pos rfl]
      exact one_ne_zero
    · have h1z_ne_one : 1 + z ≠ 1 := by
        intro h_eq
        apply hz_ne
        linear_combination h_eq
      dsimp only [h]
      rw [if_neg h1z_ne_one]
      have hsub : (1 + z) - 1 = z := by ring
      rw [hsub]
      exact mul_ne_zero hz_ne (riemannZeta_ne_zero_of_one_le_re h1z_re)
  have hg_nhds : ∀ᶠ z : ℂ in nhds 0, DifferentiableAt ℂ g z := by
    have hphi_cont : ContinuousAt (fun z : ℂ => 1 + z) 0 :=
      (continuous_const.add continuous_id).continuousAt
    have hphi_0 : (1 : ℂ) + 0 ≠ 0 := by norm_num
    have h1z_ev : ∀ᶠ z : ℂ in nhds 0, 1 + z ≠ 0 := hphi_cont.eventually_ne hphi_0
    have hh_cont : ContinuousAt (fun z : ℂ => h (1 + z)) 0 :=
      (hh_diff.continuous.comp (continuous_const.add continuous_id)).continuousAt
    have hh_0 : h (1 + 0) ≠ 0 := by
      dsimp only [h]
      rw [add_zero, if_pos rfl]
      exact one_ne_zero
    have hh_ev : ∀ᶠ z : ℂ in nhds 0, h (1 + z) ≠ 0 := hh_cont.eventually_ne hh_0
    filter_upwards [h1z_ev, hh_ev] with z h1z hh1z
    exact hg_diff_of_ne z h1z hh1z
  rw [Metric.eventually_nhds_iff] at hg_nhds
  obtain ⟨ε, hε_pos, hε_diff⟩ := hg_nhds
  let r0 : ℝ := min (ε / 2) (1 / 2)
  have hr0_pos : 0 < r0 := lt_min (half_pos hε_pos) (by norm_num)
  have hr0_le : r0 ≤ 1 / 2 := min_le_right _ _
  have hr0_lt_ε : r0 < ε := by
    have : r0 ≤ ε / 2 := min_le_left _ _
    linarith
  have hg_ball_diff : ∀ z : ℂ, ‖z‖ ≤ r0 → DifferentiableAt ℂ g z := by
    intro z hz
    apply hε_diff
    rw [dist_zero_right]
    exact lt_of_le_of_lt hz hr0_lt_ε
  have hg_diff_on : DifferentiableOn ℂ g (Metric.closedBall 0 r0) := by
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right] at hz
    exact (hg_ball_diff z hz).differentiableWithinAt
  obtain ⟨M1, hM1⟩ :=
    (isCompact_closedBall (0 : ℂ) r0).exists_bound_of_continuousOn hg_diff_on.continuousOn
  let M0 : ℝ := max M1 1
  have hM0_pos : 0 < M0 := lt_of_lt_of_le zero_lt_one (le_max_right M1 1)
  refine ⟨g, r0, M0, hr0_pos, hr0_le, hM0_pos, hg_away, hg_right, ?_⟩
  intro z hz
  refine ⟨hg_ball_diff z hz, ?_⟩
  have hz_mem : z ∈ Metric.closedBall (0 : ℂ) r0 := by
    rw [Metric.mem_closedBall, dist_zero_right]
    exact hz
  exact le_trans (hM1 z hz_mem) (le_max_left M1 1)

theorem riemannZeta_norm_le_on_half_plane : ∀ {s : ℂ}, 1 / 2 ≤ s.re → s ≠ 1 →
      ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 2 * ‖s‖ + 1 :=
by
  have s_meas_F : ∀ s : ℂ,
      MeasureTheory.AEStronglyMeasurable
        (fun t : ℝ => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
        (MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))) := by
    intro s
    have h1 : Measurable (fun t : ℝ => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        (measurable_id.sub (measurable_from_top.comp Nat.floor_mono.measurable))
    have h2 : Measurable (fun t : ℝ => Complex.exp ((Real.log t : ℂ) * -(s + 1))) :=
      Complex.continuous_exp.measurable.comp
        ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul_const (-(s + 1)))
    have h_ae : (fun t : ℝ => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * Complex.exp ((Real.log t : ℂ) * -(s + 1)))
        =ᵐ[MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))]
        (fun t : ℝ => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
      rw [Complex.cpow_def_of_ne_zero ht_ne, Complex.ofReal_log (le_of_lt ht0)]
    exact (h1.mul h2).aestronglyMeasurable.congr h_ae
  have s_integrable_frac : ∀ {s : ℂ}, 1 / 4 < s.re →
      MeasureTheory.IntegrableOn
        (fun t : ℝ => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
        (Set.Ioi (1 : ℝ)) := by
    intro s hs
    have h_dom : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-5 / 4 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-5 / 4 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)
    refine h_dom.mono' (s_meas_F s) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht1 : 1 < t := ht
    have ht0 : 0 < t := by linarith
    have h_floor_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (le_of_lt ht0)
    have h_lt_floor : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have h_norm1 : ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
      rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      linarith
    have h_norm2 : ‖(t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-5 / 4 : ℝ) := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
      have h_re : (-(s + 1)).re ≤ -5 / 4 := by
        simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
        linarith
      exact Real.rpow_le_rpow_of_exponent_le (le_of_lt ht1) h_re
    calc ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖
      _ = ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ := norm_mul _ _
      _ ≤ 1 * t ^ (-5 / 4 : ℝ) := mul_le_mul h_norm1 h_norm2 (norm_nonneg _) zero_le_one
      _ = t ^ (-5 / 4 : ℝ) := one_mul _
  have s1_riemannZeta_euler_maclaurin_gt_one : ∀ {s : ℂ}, 1 < s.re →
      (s - 1) * riemannZeta s - s =
        -s * (s - 1) * ∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
    intro s hs
    have h_bigO : (fun n : ℕ => ∑ _k ∈ Finset.Icc 1 n, (1 : ℝ)) =O[atTop] fun n : ℕ => (n : ℝ) ^ (1 : ℝ) := by
      apply Asymptotics.IsBigO.of_bound 1
      filter_upwards with n
      simp only [Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul, mul_one,
        Real.rpow_one, one_mul, le_refl]
    have h_ls := LSeries_eq_mul_integral_of_nonneg (fun _ : ℕ => (1 : ℝ))
      (by norm_num : (0 : ℝ) ≤ 1) hs h_bigO (fun _ => by norm_num)
    have h_lhs : LSeries (fun _ : ℕ => ((1 : ℝ) : ℂ)) s = riemannZeta s := by
      have h_f1 : (fun _ : ℕ => ((1 : ℝ) : ℂ)) = 1 := by
        ext n
        simp
      rw [h_f1, LSeries_one_eq_riemannZeta hs]
    rw [h_lhs] at h_ls
    have h_t_pow : ∀ t ∈ Set.Ioi (1 : ℝ),
        (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = (t : ℂ) ^ (-s) := by
      intro t ht
      have ht0 : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith [Set.mem_Ioi.mp ht])
      calc (t : ℂ) * (t : ℂ) ^ (-(s + 1))
        _ = (t : ℂ) ^ (1 : ℂ) * (t : ℂ) ^ (-(s + 1)) := by rw [Complex.cpow_one]
        _ = (t : ℂ) ^ ((1 : ℂ) + -(s + 1)) := (Complex.cpow_add _ _ ht0).symm
        _ = (t : ℂ) ^ (-s) := by congr 1; ring
    have h_neg_s_re : (-s).re < -1 := by
      rw [Complex.neg_re]
      linarith
    have hs1 : s - 1 ≠ 0 := by
      intro h
      have : (s - 1).re = 0 := by rw [h, Complex.zero_re]
      rw [Complex.sub_re, Complex.one_re] at this
      linarith
    have h_int_t_val : ∫ t in Set.Ioi (1 : ℝ), (t : ℂ) * (t : ℂ) ^ (-(s + 1)) = 1 / (s - 1) := by
      rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi h_t_pow]
      rw [integral_Ioi_cpow_of_lt h_neg_s_re (by norm_num : (0 : ℝ) < 1)]
      simp only [Complex.ofReal_one, Complex.one_cpow]
      have h_neg_eq : -s + 1 = -(s - 1) := by ring
      rw [h_neg_eq, neg_div_neg_eq]
    have h_int_t : MeasureTheory.IntegrableOn
        (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) :=
      (integrableOn_Ioi_cpow_of_lt h_neg_s_re (by norm_num : (0 : ℝ) < 1)).congr_fun
        (fun t ht => (h_t_pow t ht).symm) measurableSet_Ioi
    have h_int_frac : MeasureTheory.IntegrableOn
        (fun t : ℝ => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) (Set.Ioi (1 : ℝ)) :=
      s_integrable_frac (by linarith)
    have h_fun_eq :
        (fun t : ℝ => (∑ _k ∈ Finset.Icc 1 ⌊t⌋₊, ((1 : ℝ) : ℂ)) * (t : ℂ) ^ (-(s + 1))) =
        (fun t : ℝ => (t : ℂ) * (t : ℂ) ^ (-(s + 1)) -
          ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))) := by
      ext t
      simp only [Complex.ofReal_one, Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right,
        nsmul_eq_mul, mul_one, Complex.ofReal_sub, Complex.ofReal_natCast]
      ring
    rw [h_fun_eq, MeasureTheory.integral_sub h_int_t h_int_frac, h_int_t_val] at h_ls
    have h_inv : (s - 1) * (1 / (s - 1)) = 1 := mul_one_div_cancel hs1
    calc (s - 1) * riemannZeta s - s
      _ = (s - 1) * (s * (1 / (s - 1) -
          ∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))) - s := by
        rw [h_ls]
      _ = s * ((s - 1) * (1 / (s - 1))) - s -
          s * (s - 1) * ∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        ring
      _ = -s * (s - 1) * ∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)) := by
        rw [h_inv]
        ring
  have s2_euler_maclaurin_integral_differentiableOn :
      DifferentiableOn ℂ
        (fun s : ℂ => ∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1)))
        {s : ℂ | 1 / 4 < s.re} := by
    let μ : MeasureTheory.Measure ℝ := MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))
    let U : Set ℂ := {s : ℂ | 1 / 4 < s.re}
    let F : ℂ → ℝ → ℂ := fun s t => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
    let F' : ℂ → ℝ → ℂ := fun s t =>
      ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * ((t : ℂ) ^ (-(s + 1)) * Complex.log (t : ℂ) * (-1))
    let bound : ℝ → ℝ := fun t => 8 * t ^ (-9 / 8 : ℝ)
    have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
    intro s₀ hs₀
    have hU_nhds : U ∈ nhds s₀ := hU_open.mem_nhds hs₀
    have hF_meas : ∀ᶠ s in nhds s₀, MeasureTheory.AEStronglyMeasurable (F s) μ :=
      Filter.Eventually.of_forall s_meas_F
    have hF_int : MeasureTheory.Integrable (F s₀) μ := s_integrable_frac hs₀
    have hF'_meas : MeasureTheory.AEStronglyMeasurable (F' s₀) μ := by
      have h_log : Measurable (fun t : ℝ => (Real.log t : ℂ) * (-1 : ℂ)) :=
        (Complex.continuous_ofReal.measurable.comp Real.measurable_log).mul_const (-1 : ℂ)
      have h_ae : (fun t : ℝ => F s₀ t * ((Real.log t : ℂ) * (-1 : ℂ))) =ᵐ[μ] F' s₀ := by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
        have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
        dsimp [F, F']
        rw [Complex.ofReal_log (le_of_lt ht0)]
        ring
      exact ((s_meas_F s₀).mul h_log.aestronglyMeasurable).congr h_ae
    have h_bound : ∀ᵐ t ∂μ, ∀ s ∈ U, ‖F' s t‖ ≤ bound t := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht s hs
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := by linarith
      have h_floor_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (le_of_lt ht0)
      have h_lt_floor : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h_norm1 : ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
        linarith
      have h_norm2 : ‖(t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-5 / 4 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have h_re : (-(s + 1)).re ≤ -5 / 4 := by
          have : 1 / 4 < s.re := hs
          simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
          linarith
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt ht1) h_re
      have h_log_nonneg : 0 ≤ Real.log t := Real.log_nonneg (le_of_lt ht1)
      have h_log_bound : Real.log t ≤ 8 * t ^ (1 / 8 : ℝ) := by
        have h_rpow_pos : 0 < t ^ (1 / 8 : ℝ) := Real.rpow_pos_of_pos ht0 (1 / 8)
        have h_log_rpow : Real.log (t ^ (1 / 8 : ℝ)) = (1 / 8 : ℝ) * Real.log t :=
          Real.log_rpow ht0 (1 / 8)
        have h_log_le : Real.log (t ^ (1 / 8 : ℝ)) ≤ t ^ (1 / 8 : ℝ) - 1 :=
          Real.log_le_sub_one_of_pos h_rpow_pos
        linarith
      have h_norm3 : ‖Complex.log (t : ℂ)‖ ≤ 8 * t ^ (1 / 8 : ℝ) := by
        rw [← Complex.ofReal_log (le_of_lt ht0), Complex.norm_real, Real.norm_of_nonneg h_log_nonneg]
        exact h_log_bound
      have h_prod : ‖(t : ℂ) ^ (-(s + 1))‖ * ‖Complex.log (t : ℂ)‖ ≤
          t ^ (-5 / 4 : ℝ) * (8 * t ^ (1 / 8 : ℝ)) :=
        mul_le_mul h_norm2 h_norm3 (norm_nonneg _) (Real.rpow_nonneg (le_of_lt ht0) _)
      calc ‖F' s t‖
        _ = ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ * (‖(t : ℂ) ^ (-(s + 1))‖ * ‖Complex.log (t : ℂ)‖ * ‖(-1 : ℂ)‖) := by
          dsimp [F']
          rw [norm_mul, norm_mul, norm_mul]
        _ = ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ * (‖(t : ℂ) ^ (-(s + 1))‖ * ‖Complex.log (t : ℂ)‖) := by
          rw [norm_neg, norm_one, mul_one]
        _ ≤ 1 * (t ^ (-5 / 4 : ℝ) * (8 * t ^ (1 / 8 : ℝ))) :=
          mul_le_mul h_norm1 h_prod (mul_nonneg (norm_nonneg _) (norm_nonneg _)) zero_le_one
        _ = 8 * (t ^ (-5 / 4 : ℝ) * t ^ (1 / 8 : ℝ)) := by ring
        _ = 8 * t ^ (-9 / 8 : ℝ) := by
          rw [← Real.rpow_add ht0]
          norm_num
    have h_bound_int : MeasureTheory.Integrable bound μ :=
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-9 / 8 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)).const_mul 8
    have h_deriv : ∀ᵐ t ∂μ, ∀ s ∈ U, HasDerivAt (fun w => F w t) (F' s t) s := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht s _hs
      have ht0 : 0 < t := by linarith [Set.mem_Ioi.mp ht]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht0)
      have hd1 : HasDerivAt (fun w : ℂ => -(w + 1)) (-1) s :=
        ((hasDerivAt_id s).add_const (1 : ℂ)).neg
      have hd2 : HasDerivAt (fun w : ℂ => (t : ℂ) ^ (-(w + 1)))
          ((t : ℂ) ^ (-(s + 1)) * Complex.log (t : ℂ) * (-1)) s :=
        hd1.const_cpow (Or.inl ht_ne)
      exact hd2.const_mul ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)
    have h_main := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
      hU_nhds hF_meas hF_int hF'_meas h_bound h_bound_int h_deriv).2
    exact h_main.differentiableAt.differentiableWithinAt
  have s4_riemannZeta_mul_sub_one_differentiable :
      Differentiable ℂ (fun s : ℂ => if s = 1 then (1 : ℂ) else (s - 1) * riemannZeta s) := by
    rw [← differentiableOn_univ]
    apply (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (c := 1) Filter.univ_mem).mp
    constructor
    · intro s hs
      have hs1 : s ≠ 1 := hs.2
      have h_diff : DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) s :=
        ((differentiableAt_id.sub (differentiableAt_const 1)).mul (differentiableAt_riemannZeta hs1))
      have h_eq : (fun w : ℂ => if w = 1 then (1 : ℂ) else (w - 1) * riemannZeta w) =ᶠ[nhds s]
          (fun w : ℂ => (w - 1) * riemannZeta w) := by
        filter_upwards [isOpen_ne.mem_nhds hs1] with w hw
        exact if_neg hw
      exact (h_eq.differentiableAt_iff.mpr h_diff).differentiableWithinAt
    · rw [← continuousWithinAt_compl_self]
      have h_tendsto : Tendsto (fun w : ℂ => (w - 1) * riemannZeta w) (nhdsWithin 1 {1}ᶜ) (nhds 1) :=
        riemannZeta_residue_one
      have h_eq : (fun w : ℂ => (w - 1) * riemannZeta w) =ᶠ[nhdsWithin 1 {1}ᶜ]
          (fun w : ℂ => if w = 1 then (1 : ℂ) else (w - 1) * riemannZeta w) := by
        filter_upwards [self_mem_nhdsWithin] with w hw
        exact (if_neg (Set.mem_compl_singleton_iff.mp hw)).symm
      have h1 : (if (1 : ℂ) = 1 then (1 : ℂ) else (1 - 1) * riemannZeta 1) = 1 := if_pos rfl
      rw [ContinuousWithinAt, h1]
      exact h_tendsto.congr' h_eq
  have s3_euler_maclaurin_integral_norm_le_two : ∀ {s : ℂ}, 1 / 2 ≤ s.re →
      ‖∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))‖ ≤ 2 := by
    intro s hs
    let F : ℝ → ℂ := fun t => ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(s + 1))
    have h_norm_int : ‖∫ t in Set.Ioi (1 : ℝ), F t‖ ≤ ∫ t in Set.Ioi (1 : ℝ), ‖F t‖ :=
      MeasureTheory.norm_integral_le_integral_norm F
    have h_ae : ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Ioi (1 : ℝ))),
        ‖F t‖ ≤ t ^ (-3 / 2 : ℝ) := by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
      have ht1 : 1 < t := ht
      have ht0 : 0 < t := by linarith
      have h_floor_le : (⌊t⌋₊ : ℝ) ≤ t := Nat.floor_le (le_of_lt ht0)
      have h_lt_floor : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
      have h_frac_nonneg : 0 ≤ t - (⌊t⌋₊ : ℝ) := by linarith
      have h_frac_le : t - (⌊t⌋₊ : ℝ) ≤ 1 := by linarith
      have h_norm1 : ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_of_nonneg h_frac_nonneg]
        exact h_frac_le
      have h_norm2 : ‖(t : ℂ) ^ (-(s + 1))‖ ≤ t ^ (-3 / 2 : ℝ) := by
        rw [Complex.norm_cpow_eq_rpow_re_of_pos ht0]
        have h_re : (-(s + 1)).re ≤ -3 / 2 := by
          simp only [Complex.neg_re, Complex.add_re, Complex.one_re]
          linarith
        exact Real.rpow_le_rpow_of_exponent_le (le_of_lt ht1) h_re
      calc ‖F t‖
        _ = ‖((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ)‖ * ‖(t : ℂ) ^ (-(s + 1))‖ := norm_mul _ _
        _ ≤ 1 * t ^ (-3 / 2 : ℝ) := mul_le_mul h_norm1 h_norm2 (norm_nonneg _) zero_le_one
        _ = t ^ (-3 / 2 : ℝ) := one_mul _
    have h_int : MeasureTheory.IntegrableOn (fun t : ℝ => t ^ (-3 / 2 : ℝ)) (Set.Ioi (1 : ℝ)) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)
    have h_mono : ∫ t in Set.Ioi (1 : ℝ), ‖F t‖ ≤ ∫ t in Set.Ioi (1 : ℝ), t ^ (-3 / 2 : ℝ) :=
      MeasureTheory.integral_mono_of_nonneg
        (Filter.Eventually.of_forall (fun t => norm_nonneg (F t))) h_int h_ae
    have h_eval : ∫ t in Set.Ioi (1 : ℝ), t ^ (-3 / 2 : ℝ) = 2 := by
      rw [integral_Ioi_rpow_of_lt (by norm_num : (-3 / 2 : ℝ) < -1) (by norm_num : (0 : ℝ) < 1)]
      norm_num
    linarith
  intro s hs_re hs1
  let U : Set ℂ := {w : ℂ | 1 / 4 < w.re}
  let J : ℂ → ℂ := fun w => ∫ t in Set.Ioi (1 : ℝ), ((t - (⌊t⌋₊ : ℝ) : ℝ) : ℂ) * (t : ℂ) ^ (-(w + 1))
  let h : ℂ → ℂ := fun w => if w = 1 then (1 : ℂ) else (w - 1) * riemannZeta w
  let L : ℂ → ℂ := fun w => h w - w
  let R : ℂ → ℂ := fun w => -w * (w - 1) * J w
  have hU_open : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hU_conv : Convex ℝ U := convex_halfSpace_gt Complex.reCLM.isLinear (1 / 4)
  have hU_pre : IsPreconnected U := hU_conv.isPreconnected
  have hL_diff : Differentiable ℂ L := s4_riemannZeta_mul_sub_one_differentiable.sub differentiable_id
  have hL_an : AnalyticOnNhd ℂ L U := hL_diff.differentiableOn.analyticOnNhd hU_open
  have hR_diff : DifferentiableOn ℂ R U :=
    ((differentiableOn_id.neg.mul (differentiableOn_id.sub (differentiableOn_const 1))).mul
      s2_euler_maclaurin_integral_differentiableOn)
  have hR_an : AnalyticOnNhd ℂ R U := hR_diff.analyticOnNhd hU_open
  have h2_mem : (2 : ℂ) ∈ U := by
    simp only [U, Set.mem_setOf_eq]
    norm_num
  have h_ev : L =ᶠ[nhds (2 : ℂ)] R := by
    have hV_open : IsOpen {w : ℂ | 1 < w.re} := isOpen_lt continuous_const Complex.continuous_re
    have h2_V : (2 : ℂ) ∈ {w : ℂ | 1 < w.re} := by
      simp only [Set.mem_setOf_eq]
      norm_num
    filter_upwards [hV_open.mem_nhds h2_V] with w hw
    have hw1 : w ≠ 1 := by
      intro h_eq
      rw [h_eq, Complex.one_re] at hw
      exact lt_irrefl 1 hw
    dsimp [L, R, h, J]
    rw [if_neg hw1]
    exact s1_riemannZeta_euler_maclaurin_gt_one hw
  have h_eqOn : Set.EqOn L R U :=
    hL_an.eqOn_of_preconnected_of_eventuallyEq hR_an hU_pre h2_mem h_ev
  have hs_U : s ∈ U := by
    simp only [U, Set.mem_setOf_eq]
    linarith
  have h_LR : L s = R s := h_eqOn hs_U
  dsimp [L, R, h] at h_LR
  rw [if_neg hs1] at h_LR
  have hs_sub : s - 1 ≠ 0 := sub_ne_zero.mpr hs1
  have h_zeta_eq : riemannZeta s = 1 / (s - 1) - s * J s + 1 := by
    apply mul_left_cancel₀ hs_sub
    calc (s - 1) * riemannZeta s
      _ = -s * (s - 1) * J s + s := eq_add_of_sub_eq h_LR
      _ = (s - 1) * (1 / (s - 1) - s * J s + 1) := by
        linear_combination -mul_one_div_cancel hs_sub
  have hJ_bound : ‖J s‖ ≤ 2 := s3_euler_maclaurin_integral_norm_le_two hs_re
  have h_tri1 : ‖1 / (s - 1) - s * J s + 1‖ ≤ ‖1 / (s - 1) - s * J s‖ + ‖(1 : ℂ)‖ := norm_add_le _ _
  have h_tri2 : ‖1 / (s - 1) - s * J s‖ ≤ ‖1 / (s - 1)‖ + ‖s * J s‖ := norm_sub_le _ _
  rw [norm_div, norm_one, norm_mul] at h_tri2
  rw [norm_one] at h_tri1
  rw [h_zeta_eq]
  nlinarith [norm_nonneg s]

theorem riemannZeta_three_four_one_ineq : ∀ {σ t : ℝ}, 1 < σ →
      1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 3 * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 *
        ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖ :=
by
  have h_s1 : ∀ {u ψ : ℝ}, u < 0 →
      let w : ℂ := Complex.exp ((u : ℂ) + (ψ : ℂ) * Complex.I)
      ‖(1 - w)⁻¹‖ = Real.exp ((-Complex.log (1 - w)).re) ∧
      HasSum (fun n : ℕ => Real.exp ((n : ℝ) * u) / (n : ℝ) * Real.cos ((n : ℝ) * ψ))
        ((-Complex.log (1 - w)).re) := by
    intro u ψ hu
    dsimp only
    set z : ℂ := (u : ℂ) + (ψ : ℂ) * Complex.I
    set w : ℂ := Complex.exp z
    have hz_re : z.re = u := by simp [z]
    have hz_im : z.im = ψ := by simp [z]
    have hw_norm : ‖w‖ < 1 := by
      rw [Complex.norm_exp, hz_re, Real.exp_lt_one_iff]
      exact hu
    have h1w_ne : 1 - w ≠ 0 := by
      intro h
      have hw1 : w = 1 := (sub_eq_zero.mp h).symm
      rw [hw1, norm_one] at hw_norm
      exact lt_irrefl 1 hw_norm
    have h_norm_inv : ‖(1 - w)⁻¹‖ = Real.exp ((-Complex.log (1 - w)).re) := by
      have hexp : Complex.exp (-Complex.log (1 - w)) = (1 - w)⁻¹ := by
        rw [Complex.exp_neg, Complex.exp_log h1w_ne]
      rw [← hexp, Complex.norm_exp]
    refine ⟨h_norm_inv, ?_⟩
    have h_sum := Complex.hasSum_re (Complex.hasSum_taylorSeries_neg_log hw_norm)
    convert h_sum using 1
    ext n
    have hwn : w ^ n = Complex.exp ((n : ℂ) * z) := (Complex.exp_nat_mul z n).symm
    have hnz_re : ((n : ℂ) * z).re = (n : ℝ) * u := by simp [z]
    have hnz_im : ((n : ℂ) * z).im = (n : ℝ) * ψ := by simp [z]
    have hwn_re : (w ^ n).re = Real.exp ((n : ℝ) * u) * Real.cos ((n : ℝ) * ψ) := by
      rw [hwn, Complex.exp_re, hnz_re, hnz_im]
    rw [← Complex.ofReal_natCast, Complex.div_ofReal_re, hwn_re, mul_div_right_comm]
  have h_s2 : ∀ {σ t : ℝ}, 1 < σ → ∀ {p : ℕ}, Nat.Prime p →
      let s0 : ℂ := (σ : ℂ)
      let s1 : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
      let s2 : ℂ := (σ : ℂ) + (2 * t : ℂ) * Complex.I
      1 ≤ ‖(1 - (p : ℂ) ^ (-s0))⁻¹‖ ^ 3 * ‖(1 - (p : ℂ) ^ (-s1))⁻¹‖ ^ 4 *
        ‖(1 - (p : ℂ) ^ (-s2))⁻¹‖ := by
    intro σ t hσ p hp
    dsimp only
    set s0 : ℂ := (σ : ℂ)
    set s1 : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
    set s2 : ℂ := (σ : ℂ) + (2 * t : ℂ) * Complex.I
    have hp_ne : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
    have hp_gt1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
    have hlogp_pos : 0 < Real.log (p : ℝ) := Real.log_pos hp_gt1
    set u : ℝ := -σ * Real.log (p : ℝ)
    set θ : ℝ := -t * Real.log (p : ℝ)
    have hu : u < 0 := mul_neg_of_neg_of_pos (by linarith) hlogp_pos
    have h_cpow : ∀ s : ℂ, (p : ℂ) ^ (-s) = Complex.exp ((Real.log (p : ℝ) : ℂ) * (-s)) := by
      intro s
      rw [Complex.cpow_def_of_ne_zero hp_ne, ← Complex.natCast_log]
    have hw0 : (p : ℂ) ^ (-s0) = Complex.exp ((u : ℂ) + ((0 : ℝ) : ℂ) * Complex.I) := by
      rw [h_cpow]
      congr 1
      simp only [s0, u]
      push_cast
      ring
    have hw1 : (p : ℂ) ^ (-s1) = Complex.exp ((u : ℂ) + (θ : ℂ) * Complex.I) := by
      rw [h_cpow]
      congr 1
      simp only [s1, u, θ]
      push_cast
      ring
    have hw2 : (p : ℂ) ^ (-s2) = Complex.exp ((u : ℂ) + ((2 * θ : ℝ) : ℂ) * Complex.I) := by
      rw [h_cpow]
      congr 1
      simp only [s2, u, θ]
      push_cast
      ring
    obtain ⟨hn0, hs0⟩ := @h_s1 u 0 hu
    obtain ⟨hn1, hs1⟩ := @h_s1 u θ hu
    obtain ⟨hn2, hs2⟩ := @h_s1 u (2 * θ) hu
    set L0 := (-Complex.log (1 - Complex.exp ((u : ℂ) + ((0 : ℝ) : ℂ) * Complex.I))).re
    set L1 := (-Complex.log (1 - Complex.exp ((u : ℂ) + (θ : ℂ) * Complex.I))).re
    set L2 := (-Complex.log (1 - Complex.exp ((u : ℂ) + ((2 * θ : ℝ) : ℂ) * Complex.I))).re
    have h_comb := ((hs0.mul_left 3).add (hs1.mul_left 4)).add hs2
    have h_nonneg : 0 ≤ 3 * L0 + 4 * L1 + L2 := by
      refine h_comb.nonneg fun n => ?_
      have h_eq : 3 * (Real.exp ((n : ℝ) * u) / (n : ℝ) * Real.cos ((n : ℝ) * 0)) +
          4 * (Real.exp ((n : ℝ) * u) / (n : ℝ) * Real.cos ((n : ℝ) * θ)) +
          Real.exp ((n : ℝ) * u) / (n : ℝ) * Real.cos ((n : ℝ) * (2 * θ)) =
          Real.exp ((n : ℝ) * u) / (n : ℝ) * (2 * (1 + Real.cos ((n : ℝ) * θ)) ^ 2) := by
        have h2 : (n : ℝ) * (2 * θ) = 2 * ((n : ℝ) * θ) := by ring
        rw [mul_zero, Real.cos_zero, h2, Real.cos_two_mul]
        ring
      rw [h_eq]
      positivity
    have hexp_ge : 1 ≤ Real.exp (3 * L0 + 4 * L1 + L2) := Real.one_le_exp h_nonneg
    have hexp_eq : Real.exp (3 * L0 + 4 * L1 + L2) =
        Real.exp L0 ^ 3 * Real.exp L1 ^ 4 * Real.exp L2 := by
      have h3 : (3 : ℝ) * L0 = ((3 : ℕ) : ℝ) * L0 := by norm_num
      have h4 : (4 : ℝ) * L1 = ((4 : ℕ) : ℝ) * L1 := by norm_num
      rw [Real.exp_add, Real.exp_add, h3, h4, Real.exp_nat_mul, Real.exp_nat_mul]
    rw [hw0, hw1, hw2, hn0, hn1, hn2, ← hexp_eq]
    exact hexp_ge
  intro σ t hσ
  set s0 : ℂ := (σ : ℂ)
  set s1 : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I
  set s2 : ℂ := (σ : ℂ) + (2 * t : ℂ) * Complex.I
  have hs0_re : 1 < s0.re := by simp [s0, hσ]
  have hs1_re : 1 < s1.re := by simp [s1, hσ]
  have hs2_re : 1 < s2.re := by simp [s2, hσ]
  have hT0 := riemannZeta_eulerProduct hs0_re
  have hT1 := riemannZeta_eulerProduct hs1_re
  have hT2 := riemannZeta_eulerProduct hs2_re
  have hT_comb := ((hT0.norm.pow 3).mul (hT1.norm.pow 4)).mul hT2.norm
  have hT_prod : Filter.Tendsto
      (fun N : ℕ => ∏ p ∈ N.primesBelow,
        (‖(1 - (p : ℂ) ^ (-s0))⁻¹‖ ^ 3 * ‖(1 - (p : ℂ) ^ (-s1))⁻¹‖ ^ 4 *
          ‖(1 - (p : ℂ) ^ (-s2))⁻¹‖))
      Filter.atTop
      (nhds (‖riemannZeta s0‖ ^ 3 * ‖riemannZeta s1‖ ^ 4 * ‖riemannZeta s2‖)) := by
    refine hT_comb.congr fun N => ?_
    rw [norm_prod, norm_prod, norm_prod, ← Finset.prod_pow, ← Finset.prod_pow,
        ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine ge_of_tendsto' hT_prod fun N => ?_
  have h_prod : ∀ (S : Finset ℕ) (f : ℕ → ℝ),
      (∀ p ∈ S, 1 ≤ f p) → 1 ≤ ∏ p ∈ S, f p := by
    intro S f
    induction S using Finset.induction_on with
    | empty =>
      intro _
      rw [Finset.prod_empty]
    | @insert p S hpS ih =>
      intro hS
      rw [Finset.prod_insert hpS]
      have hp1 : 1 ≤ f p := hS p (Finset.mem_insert_self p S)
      have hS1 : 1 ≤ ∏ q ∈ S, f q := ih (fun q hq => hS q (Finset.mem_insert_of_mem hq))
      calc (1 : ℝ)
        _ = 1 * 1 := (mul_one 1).symm
        _ ≤ f p * ∏ q ∈ S, f q := mul_le_mul hp1 hS1 zero_le_one (le_trans zero_le_one hp1)
  exact h_prod N.primesBelow _ (fun p hp => h_s2 hσ (Nat.mem_primesBelow.mp hp).2)

theorem zeta_strip_nonvanishing_and_log_deriv_bound : ∀ {r0 : ℝ}, 0 < r0 → r0 ≤ 1 / 2 →
      (∀ {s : ℂ}, 1 / 2 ≤ s.re → s ≠ 1 → ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 2 * ‖s‖ + 1) →
      (∀ {σ t : ℝ}, 1 < σ →
        1 ≤ ‖riemannZeta (σ : ℂ)‖ ^ 3 * ‖riemannZeta ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ^ 4 *
          ‖riemannZeta ((σ : ℂ) + (2 * t : ℂ) * Complex.I)‖) →
      ∃ (a C1 : ℝ), 0 < a ∧ a ≤ r0 / 4 ∧ 0 < C1 ∧
        ∀ (R : ℝ), 1 ≤ R → ∀ (z : ℂ),
          -a * (R + 2) ^ (-5 : ℝ) ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → r0 < ‖z‖ →
          riemannZeta (1 + z) ≠ 0 ∧
          ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z‖ ≤ C1 * (R + 2) ^ (5 : ℝ) :=
by
  intro r0 hr0_pos hr0_le h_ub h_341
  have h_s1 : ∀ {R η t : ℝ}, 1 ≤ R → 0 < η → η ≤ 1 → r0 / 2 ≤ |t| → |t| ≤ R →
      η * ‖riemannZeta ((1 + η : ℝ) : ℂ)‖ ≤ 6 ∧
      ‖riemannZeta (((1 + η : ℝ) : ℂ) + (2 * t : ℂ) * Complex.I)‖ ≤ (1 / r0 + 5) * (R + 2) := by
    clear h_341
    intro R η t hR hη_pos hη_le1 ht_low ht_high
    refine ⟨?_, ?_⟩
    · let s1 : ℂ := ((1 + η : ℝ) : ℂ)
      have hs1_re : 1 / 2 ≤ s1.re := by
        simp only [s1, Complex.ofReal_re]
        linarith
      have hs1_sub : s1 - 1 = (η : ℂ) := by
        dsimp [s1]
        push_cast
        ring
      have hs1_sub_norm : ‖s1 - 1‖ = η := by
        rw [hs1_sub, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hη_pos)]
      have hs1_ne : s1 ≠ 1 := by
        intro h
        have : ‖s1 - 1‖ = 0 := by rw [h, sub_self, norm_zero]
        linarith
      have hs1_norm : ‖s1‖ = 1 + η := by
        dsimp [s1]
        rw [Complex.norm_real, Real.norm_of_nonneg (by linarith)]
      have hub1 := h_ub hs1_re hs1_ne
      rw [hs1_sub_norm, hs1_norm] at hub1
      have h_mul : η * ‖riemannZeta s1‖ ≤ η * (1 / η + 2 * (1 + η) + 1) :=
        mul_le_mul_of_nonneg_left hub1 (le_of_lt hη_pos)
      have h_eta_inv : η * (1 / η) = 1 := mul_one_div_cancel (ne_of_gt hη_pos)
      have h_expand : η * (1 / η + 2 * (1 + η) + 1) = η * (1 / η) + 3 * η + 2 * (η * η) := by ring
      have h_sq : η * η ≤ 1 * 1 := mul_le_mul hη_le1 hη_le1 (le_of_lt hη_pos) (by norm_num)
      linarith
    · let s2 : ℂ := ((1 + η : ℝ) : ℂ) + (2 * t : ℂ) * Complex.I
      have hs2_re_eq : s2.re = 1 + η := by simp [s2]
      have hs2_im_eq : s2.im = 2 * t := by simp [s2]
      have hs2_sub_im : (s2 - 1).im = 2 * t := by simp [s2]
      have hs2_sub_norm : r0 ≤ ‖s2 - 1‖ := by
        have h1 := Complex.abs_im_le_norm (s2 - 1)
        rw [hs2_sub_im, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
        linarith
      have hs2_ne : s2 ≠ 1 := by
        intro h
        rw [h, sub_self, norm_zero] at hs2_sub_norm
        linarith
      have hs2_inv : 1 / ‖s2 - 1‖ ≤ 1 / r0 :=
        one_div_le_one_div_of_le hr0_pos hs2_sub_norm
      have hs2_norm : ‖s2‖ ≤ 2 + 2 * R := by
        have h1 := Complex.norm_le_abs_re_add_abs_im s2
        rw [hs2_re_eq, hs2_im_eq, abs_of_pos (by linarith : 0 < 1 + η), abs_mul,
            abs_of_pos (by norm_num : (0 : ℝ) < 2)] at h1
        linarith
      have hub2 := h_ub (by linarith : 1 / 2 ≤ s2.re) hs2_ne
      have h_r0_inv_pos : 0 < 1 / r0 := one_div_pos.mpr hr0_pos
      have h_r0_R : 1 / r0 ≤ 1 / r0 * R := le_mul_of_one_le_right (le_of_lt h_r0_inv_pos) hR
      have h_expand : (1 / r0 + 5) * (R + 2) = 1 / r0 * R + 2 * (1 / r0) + 5 * R + 10 := by ring
      linarith
  have h_s2 : ∀ {R : ℝ}, 1 ≤ R → ∀ {s : ℂ},
      3 / 4 ≤ s.re → s.re ≤ 2 → r0 / 2 ≤ |s.im| → |s.im| ≤ R →
      ‖deriv riemannZeta s‖ ≤ (4 / r0 * (4 / r0 + 5)) * (R + 2) := by
    clear h_341 h_s1
    intro R hR s hs_re_low hs_re_high hs_im_low hs_im_high
    set ρ : ℝ := r0 / 4
    have hρ_pos : 0 < ρ := by dsimp [ρ]; linarith
    have hρ_le : ρ ≤ 1 / 8 := by dsimp [ρ]; linarith
    have h_ball : ∀ w ∈ Metric.closedBall s ρ,
        w ≠ 1 ∧ ‖riemannZeta w‖ ≤ (4 / r0 + 5) * (R + 2) := by
      intro w hw
      rw [Metric.mem_closedBall, dist_eq_norm] at hw
      have hw_re_diff : |w.re - s.re| ≤ ρ := by
        have h1 := Complex.abs_re_le_norm (w - s)
        simpa [Complex.sub_re] using le_trans h1 hw
      have hw_im_diff : |w.im - s.im| ≤ ρ := by
        have h1 := Complex.abs_im_le_norm (w - s)
        simpa [Complex.sub_im] using le_trans h1 hw
      have hw_re_low : 1 / 2 ≤ w.re := by
        rw [abs_le] at hw_re_diff
        linarith
      have hw_re_high : w.re ≤ 17 / 8 := by
        rw [abs_le] at hw_re_diff
        linarith
      have hw_im_low : r0 / 4 ≤ |w.im| := by
        have h_tri : |s.im| ≤ |w.im - s.im| + |w.im| := by
          have : s.im = -(w.im - s.im) + w.im := by ring
          calc |s.im| = |-(w.im - s.im) + w.im| := by rw [← this]
            _ ≤ |-(w.im - s.im)| + |w.im| := abs_add_le _ _
            _ = |w.im - s.im| + |w.im| := by rw [abs_neg]
        dsimp [ρ] at hw_im_diff
        linarith
      have hw_im_high : |w.im| ≤ R + 1 / 8 := by
        have h_tri : |w.im| ≤ |w.im - s.im| + |s.im| := by
          have : w.im = (w.im - s.im) + s.im := by ring
          calc |w.im| = |(w.im - s.im) + s.im| := by rw [← this]
            _ ≤ |w.im - s.im| + |s.im| := abs_add_le _ _
        linarith
      have hw_sub_norm : r0 / 4 ≤ ‖w - 1‖ := by
        have h1 := Complex.abs_im_le_norm (w - 1)
        simp only [Complex.sub_im, Complex.one_im, sub_zero] at h1
        linarith
      have hw_ne : w ≠ 1 := by
        intro h
        rw [h, sub_self, norm_zero] at hw_sub_norm
        linarith
      have hw_inv : 1 / ‖w - 1‖ ≤ 4 / r0 := by
        have h1 := one_div_le_one_div_of_le (by linarith : 0 < r0 / 4) hw_sub_norm
        have h2 : 1 / (r0 / 4) = 4 / r0 := by ring
        linarith
      have hw_norm : ‖w‖ ≤ R + 9 / 4 := by
        have h1 := Complex.norm_le_abs_re_add_abs_im w
        rw [abs_of_pos (by linarith : 0 < w.re)] at h1
        linarith
      have hub_w := h_ub hw_re_low hw_ne
      have h4r0_pos : 0 < 4 / r0 := div_pos (by norm_num) hr0_pos
      have h4r0_R : 4 / r0 ≤ 4 / r0 * R := le_mul_of_one_le_right (le_of_lt h4r0_pos) hR
      have h_expand : (4 / r0 + 5) * (R + 2) = 4 / r0 * R + 2 * (4 / r0) + 5 * R + 10 := by ring
      refine ⟨hw_ne, ?_⟩
      linarith
    have h_diff_on : DifferentiableOn ℂ riemannZeta {w : ℂ | w ≠ 1} :=
      fun w hw => (differentiableAt_riemannZeta hw).differentiableWithinAt
    have h_sub : Metric.closedBall s ρ ⊆ {w : ℂ | w ≠ 1} :=
      fun w hw => (h_ball w hw).1
    have h_diff_cont : DiffContOnCl ℂ riemannZeta (Metric.ball s ρ) :=
      h_diff_on.diffContOnCl_ball h_sub
    have h_sphere : ∀ w ∈ Metric.sphere s ρ, ‖riemannZeta w‖ ≤ (4 / r0 + 5) * (R + 2) :=
      fun w hw => (h_ball w (Metric.sphere_subset_closedBall hw)).2
    have h_cauchy := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hρ_pos h_diff_cont h_sphere
    have h_eq : (4 / r0 + 5) * (R + 2) / ρ = (4 / r0 * (4 / r0 + 5)) * (R + 2) := by
      dsimp [ρ]
      ring
    linarith
  have h_s3 : ∀ {R M η : ℝ} {z : ℂ},
      -1 / 4 ≤ z.re → z.re ≤ 0 → 0 < η → η ≤ 1 →
      r0 / 2 ≤ |z.im| → |z.im| ≤ R →
      (∀ s : ℂ, 3 / 4 ≤ s.re → s.re ≤ 2 → r0 / 2 ≤ |s.im| → |s.im| ≤ R →
        ‖deriv riemannZeta s‖ ≤ M) →
      ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) - riemannZeta (1 + z)‖ ≤
        M * (η - z.re) := by
    clear hr0_le h_ub h_341 h_s1 h_s2
    intro R M η z hz_re_low hz_re_high hη_pos hη_le1 hz_im_low hz_im_high h_deriv
    let S : Set ℂ := {w : ℂ | 3 / 4 ≤ w.re ∧ w.re ≤ 2 ∧ w.im = z.im}
    have hS_conv : Convex ℝ S := by
      intro u hu v hv a b ha hb hab
      rcases hu with ⟨hu1, hu2, hu3⟩
      rcases hv with ⟨hv1, hv2, hv3⟩
      simp only [S, Set.mem_setOf_eq, Complex.add_re, Complex.smul_re,
                 Complex.add_im, Complex.smul_im, smul_eq_mul]
      have h_low_a : a * (3 / 4) ≤ a * u.re := mul_le_mul_of_nonneg_left hu1 ha
      have h_low_b : b * (3 / 4) ≤ b * v.re := mul_le_mul_of_nonneg_left hv1 hb
      have h_high_a : a * u.re ≤ a * 2 := mul_le_mul_of_nonneg_left hu2 ha
      have h_high_b : b * v.re ≤ b * 2 := mul_le_mul_of_nonneg_left hv2 hb
      have h_im : a * u.im + b * v.im = z.im := by
        rw [hu3, hv3]
        calc a * z.im + b * z.im = (a + b) * z.im := by ring
          _ = 1 * z.im := by rw [hab]
          _ = z.im := one_mul _
      refine ⟨by linarith, by linarith, h_im⟩
    have hS_diff : ∀ w ∈ S, DifferentiableAt ℂ riemannZeta w := by
      intro w hw
      have hw_im : w.im = z.im := hw.2.2
      have hw_ne : w ≠ 1 := by
        intro h
        have h1 : w.im = 0 := by rw [h, Complex.one_im]
        have h2 : |z.im| = 0 := by rw [← hw_im, h1, abs_zero]
        linarith
      exact differentiableAt_riemannZeta hw_ne
    have hS_bound : ∀ w ∈ S, ‖deriv riemannZeta w‖ ≤ M := by
      intro w ⟨hw1, hw2, hw3⟩
      apply h_deriv w hw1 hw2
      · rw [hw3]; exact hz_im_low
      · rw [hw3]; exact hz_im_high
    let x : ℂ := 1 + z
    let y : ℂ := ((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I
    have hx_mem : x ∈ S := by
      simp only [S, x, Set.mem_setOf_eq, Complex.add_re, Complex.one_re,
                 Complex.add_im, Complex.one_im, zero_add]
      exact ⟨by linarith, by linarith, trivial⟩
    have hy_mem : y ∈ S := by
      simp only [S, y, Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re,
                 Complex.mul_re, Complex.I_re, mul_zero, Complex.ofReal_im,
                 Complex.I_im, mul_one, sub_zero, add_zero,
                 Complex.add_im, Complex.mul_im, zero_add]
      exact ⟨by linarith, by linarith, trivial⟩
    have h_mvt := hS_conv.norm_image_sub_le_of_norm_deriv_le hS_diff hS_bound hx_mem hy_mem
    have hyx_eq : y - x = ((η - z.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [x, y]
    have hyx_norm : ‖y - x‖ = η - z.re := by
      rw [hyx_eq, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    rw [hyx_norm] at h_mvt
    exact h_mvt
  have h_s4 : ∀ {R K1 K2 a η : ℝ} {z : ℂ},
      1 ≤ R → 0 < K1 → 0 < K2 → 0 < a →
      η = 2 * a * (R + 2) ^ (-5 : ℝ) →
      a ≤ 1 / (110592 * K1 * K2 ^ 4) →
      -a * (R + 2) ^ (-5 : ℝ) ≤ z.re → z.re ≤ 0 →
      1 / 2 ≤ (1 + z).re → r0 < ‖z‖ →
      1 ≤ ‖riemannZeta ((1 + η : ℝ) : ℂ)‖ ^ 3 *
        ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)‖ ^ 4 *
        ‖riemannZeta (((1 + η : ℝ) : ℂ) + (2 * z.im : ℂ) * Complex.I)‖ →
      η * ‖riemannZeta ((1 + η : ℝ) : ℂ)‖ ≤ 6 →
      ‖riemannZeta (((1 + η : ℝ) : ℂ) + (2 * z.im : ℂ) * Complex.I)‖ ≤ K1 * (R + 2) →
      ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) - riemannZeta (1 + z)‖ ≤
        K2 * (R + 2) * (η - z.re) →
      ‖deriv riemannZeta (1 + z)‖ ≤ K2 * (R + 2) →
      riemannZeta (1 + z) ≠ 0 ∧
      ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z‖ ≤
        (1 / (2 * a) + 1 / r0) * (R + 2) ^ (5 : ℝ) := by
    clear hr0_le h_ub h_341 h_s1 h_s2 h_s3
    intro R K1 K2 a η z hR hK1_pos hK2_pos ha_pos hη_def ha_le_K
      hz_re_low hz_re_high h1z_re_low hz_norm h_341_pt h_pole h_double h_step h_deriv_1z
    have hR2_pos : 0 < R + 2 := by linarith
    have hR2_ge1 : 1 ≤ R + 2 := by linarith
    have hrpow_neg5_pos : 0 < (R + 2) ^ (-5 : ℝ) := Real.rpow_pos_of_pos hR2_pos (-5 : ℝ)
    have hrpow_5_ge1 : 1 ≤ (R + 2) ^ (5 : ℝ) := by
      calc (1 : ℝ)
        _ = (R + 2) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ (R + 2) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR2_ge1 (by norm_num)
    have hrpow_mul : (R + 2) ^ (-5 : ℝ) * (R + 2) ^ (5 : ℝ) = 1 := by
      rw [← Real.rpow_add hR2_pos]
      norm_num
    have hrpow_5_eq_pow : (R + 2) ^ (5 : ℝ) = (R + 2) ^ 5 := by norm_cast
    have hη_pos : 0 < η := by rw [hη_def]; positivity
    set Z0 : ℝ := ‖riemannZeta ((1 + η : ℝ) : ℂ)‖
    set Z1 : ℝ := ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)‖
    set Z2 : ℝ := ‖riemannZeta (((1 + η : ℝ) : ℂ) + (2 * z.im : ℂ) * Complex.I)‖
    have hZ0_nonneg : 0 ≤ Z0 := norm_nonneg _
    have hZ1_nonneg : 0 ≤ Z1 := norm_nonneg _
    have hZ2_nonneg : 0 ≤ Z2 := norm_nonneg _
    have h_eta_Z0_cube : (η * Z0) ^ 3 ≤ 216 := by
      have h0 : 0 ≤ η * Z0 := mul_nonneg (le_of_lt hη_pos) hZ0_nonneg
      calc (η * Z0) ^ 3
        _ ≤ 6 ^ 3 := pow_le_pow_left₀ h0 h_pole 3
        _ = 216 := by norm_num
    have h_eta3_le : η ^ 3 ≤ 216 * K1 * (R + 2) * Z1 ^ 4 := by
      calc η ^ 3
        _ = η ^ 3 * 1 := (mul_one _).symm
        _ ≤ η ^ 3 * (Z0 ^ 3 * Z1 ^ 4 * Z2) :=
          mul_le_mul_of_nonneg_left h_341_pt (by positivity)
        _ = (η * Z0) ^ 3 * Z1 ^ 4 * Z2 := by ring
        _ ≤ (216 * Z1 ^ 4) * (K1 * (R + 2)) := by
          have hZ1_4 : 0 ≤ Z1 ^ 4 := by positivity
          have h_a : (η * Z0) ^ 3 * Z1 ^ 4 ≤ 216 * Z1 ^ 4 :=
            mul_le_mul_of_nonneg_right h_eta_Z0_cube hZ1_4
          exact mul_le_mul h_a h_double hZ2_nonneg (by positivity)
        _ = 216 * K1 * (R + 2) * Z1 ^ 4 := by ring
    have h_eta_R5 : η * (R + 2) ^ 5 = 2 * a := by
      calc η * (R + 2) ^ 5
        _ = 2 * a * ((R + 2) ^ (-5 : ℝ) * (R + 2) ^ (5 : ℝ)) := by
          rw [hη_def, ← hrpow_5_eq_pow]
          ring
        _ = 2 * a := by rw [hrpow_mul, mul_one]
    have h_a_bound : 110592 * K1 * K2 ^ 4 * a ≤ 1 := by
      have h_denom_pos : 0 < 110592 * K1 * K2 ^ 4 := by positivity
      exact (le_div_iff₀' h_denom_pos).mp ha_le_K
    have h_lhs_le_eta3 : 216 * K1 * (R + 2) * (4 * K2 * (R + 2) * η) ^ 4 ≤ η ^ 3 := by
      calc 216 * K1 * (R + 2) * (4 * K2 * (R + 2) * η) ^ 4
        _ = 55296 * K1 * K2 ^ 4 * (η * (R + 2) ^ 5) * η ^ 3 := by ring
        _ = (110592 * K1 * K2 ^ 4 * a) * η ^ 3 := by
          rw [h_eta_R5]
          ring
        _ ≤ 1 * η ^ 3 := mul_le_mul_of_nonneg_right h_a_bound (by positivity)
        _ = η ^ 3 := one_mul _
    have h_pow4_le : (4 * K2 * (R + 2) * η) ^ 4 ≤ Z1 ^ 4 := by
      have h_comb : 216 * K1 * (R + 2) * (4 * K2 * (R + 2) * η) ^ 4 ≤ 216 * K1 * (R + 2) * Z1 ^ 4 :=
        le_trans h_lhs_le_eta3 h_eta3_le
      exact le_of_mul_le_mul_left h_comb (by positivity)
    have h_Z1_low : 4 * K2 * (R + 2) * η ≤ Z1 :=
      le_of_pow_le_pow_left₀ (by omega : 4 ≠ 0) hZ1_nonneg h_pow4_le
    have h_step_le : ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) - riemannZeta (1 + z)‖ ≤
        2 * K2 * (R + 2) * η := by
      have h_eta_zre : η - z.re ≤ 2 * η := by
        linarith [hz_re_low, hη_def, hη_pos]
      calc ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) - riemannZeta (1 + z)‖
        _ ≤ K2 * (R + 2) * (η - z.re) := h_step
        _ ≤ K2 * (R + 2) * (2 * η) :=
          mul_le_mul_of_nonneg_left h_eta_zre (by positivity)
        _ = 2 * K2 * (R + 2) * η := by ring
    have h_tri_zeta : Z1 ≤ ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) - riemannZeta (1 + z)‖ +
        ‖riemannZeta (1 + z)‖ :=
      norm_le_norm_sub_add _ _
    have h_zeta_1z_low : 2 * K2 * (R + 2) * η ≤ ‖riemannZeta (1 + z)‖ := by
      linarith [h_Z1_low, h_step_le, h_tri_zeta]
    have h_zeta_1z_pos : 0 < ‖riemannZeta (1 + z)‖ := by
      have hpos : 0 < 2 * K2 * (R + 2) * η := by positivity
      linarith [hpos, h_zeta_1z_low]
    have h_zeta_1z_ne : riemannZeta (1 + z) ≠ 0 := norm_pos_iff.mp h_zeta_1z_pos
    have h_1z_norm : 1 / 2 ≤ ‖1 + z‖ := by
      have h1 := Complex.abs_re_le_norm (1 + z)
      have h2 : 1 / 2 ≤ |(1 + z).re| := by
        rw [abs_of_pos (by linarith [h1z_re_low])]
        linarith [h1z_re_low]
      linarith [h1, h2]
    have h_prod_norm : K2 * (R + 2) * η ≤ ‖(1 + z) * riemannZeta (1 + z)‖ := by
      rw [norm_mul]
      calc K2 * (R + 2) * η
        _ = (1 / 2) * (2 * K2 * (R + 2) * η) := by ring
        _ ≤ ‖1 + z‖ * ‖riemannZeta (1 + z)‖ :=
          mul_le_mul h_1z_norm h_zeta_1z_low (by positivity) (norm_nonneg _)
    have h_div1 : ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z))‖ ≤ 1 / η := by
      rw [norm_div, norm_neg]
      have h_denom_pos : 0 < K2 * (R + 2) * η := by positivity
      calc ‖deriv riemannZeta (1 + z)‖ / ‖(1 + z) * riemannZeta (1 + z)‖
        _ ≤ (K2 * (R + 2)) / (K2 * (R + 2) * η) :=
          div_le_div₀ (by positivity) h_deriv_1z h_denom_pos h_prod_norm
        _ = 1 / η := by
          have hK2R_ne : K2 * (R + 2) ≠ 0 := by positivity
          field_simp [hK2R_ne]
    have h_div2 : ‖(1 / z : ℂ)‖ ≤ 1 / r0 := by
      rw [norm_div, norm_one]
      exact one_div_le_one_div_of_le hr0_pos (le_of_lt hz_norm)
    have h_inv_eta : 1 / η = 1 / (2 * a) * (R + 2) ^ (5 : ℝ) := by
      have h_eq : (1 / (2 * a) * (R + 2) ^ (5 : ℝ)) * η = 1 := by
        rw [hrpow_5_eq_pow]
        calc (1 / (2 * a) * (R + 2) ^ 5) * η
          _ = (η * (R + 2) ^ 5) * (1 / (2 * a)) := by ring
          _ = (2 * a) * (1 / (2 * a)) := by rw [h_eta_R5]
          _ = 1 := mul_one_div_cancel (by positivity)
      exact (div_eq_iff (ne_of_gt hη_pos)).mpr h_eq.symm
    have h_r0_R5 : 1 / r0 * 1 ≤ 1 / r0 * (R + 2) ^ (5 : ℝ) :=
      mul_le_mul_of_nonneg_left hrpow_5_ge1 (by positivity)
    have h_final : ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z‖ ≤
        (1 / (2 * a) + 1 / r0) * (R + 2) ^ (5 : ℝ) := by
      calc ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z‖
        _ ≤ ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z))‖ + ‖(1 / z : ℂ)‖ :=
          norm_sub_le _ _
        _ ≤ 1 / η + 1 / r0 := add_le_add h_div1 h_div2
        _ = 1 / (2 * a) * (R + 2) ^ (5 : ℝ) + 1 / r0 * 1 := by rw [h_inv_eta, mul_one]
        _ ≤ 1 / (2 * a) * (R + 2) ^ (5 : ℝ) + 1 / r0 * (R + 2) ^ (5 : ℝ) := by
          linarith [h_r0_R5]
        _ = (1 / (2 * a) + 1 / r0) * (R + 2) ^ (5 : ℝ) := by ring
    exact ⟨h_zeta_1z_ne, h_final⟩
  obtain ⟨K1, hK1_def⟩ : ∃ K1 : ℝ, K1 = 1 / r0 + 5 := ⟨_, rfl⟩
  obtain ⟨K2, hK2_def⟩ : ∃ K2 : ℝ, K2 = 4 / r0 * (4 / r0 + 5) := ⟨_, rfl⟩
  obtain ⟨a, ha_def⟩ : ∃ a : ℝ, a = min (r0 / 4) (1 / (110592 * K1 * K2 ^ 4)) := ⟨_, rfl⟩
  obtain ⟨C1, hC1_def⟩ : ∃ C1 : ℝ, C1 = 1 / (2 * a) + 1 / r0 := ⟨_, rfl⟩
  have hK1_pos : 0 < K1 := by rw [hK1_def]; positivity
  have hK2_pos : 0 < K2 := by rw [hK2_def]; positivity
  have ha_pos : 0 < a := by rw [ha_def]; positivity
  have ha_le_r0 : a ≤ r0 / 4 := by rw [ha_def]; exact min_le_left _ _
  have ha_le_K : a ≤ 1 / (110592 * K1 * K2 ^ 4) := by rw [ha_def]; exact min_le_right _ _
  have hC1_pos : 0 < C1 := by rw [hC1_def]; positivity
  refine ⟨a, C1, ha_pos, ha_le_r0, hC1_pos, ?_⟩
  intro R hR z hz_re_low hz_re_high hz_im_high hz_norm
  obtain ⟨η, hη_def⟩ : ∃ η : ℝ, η = 2 * a * (R + 2) ^ (-5 : ℝ) := ⟨_, rfl⟩
  have hR2_pos : 0 < R + 2 := by linarith
  have hR2_ge1 : 1 ≤ R + 2 := by linarith
  have hrpow_neg5_pos : 0 < (R + 2) ^ (-5 : ℝ) := Real.rpow_pos_of_pos hR2_pos (-5 : ℝ)
  have hrpow_neg5_le1 : (R + 2) ^ (-5 : ℝ) ≤ 1 := by
    calc (R + 2) ^ (-5 : ℝ)
      _ ≤ (R + 2) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR2_ge1 (by norm_num)
      _ = 1 := Real.rpow_zero _
  have hη_pos : 0 < η := by rw [hη_def]; positivity
  have hη_le_2a : η ≤ 2 * a := by
    rw [hη_def]
    exact mul_le_of_le_one_right (by positivity) hrpow_neg5_le1
  have hη_le1 : η ≤ 1 := by linarith
  have hz_re_ge_neg_a : -a ≤ z.re := by
    have : a * (R + 2) ^ (-5 : ℝ) ≤ a := mul_le_of_le_one_right (le_of_lt ha_pos) hrpow_neg5_le1
    linarith
  have hz_re_ge_neg_quarter : -1 / 4 ≤ z.re := by linarith
  have hz_re_abs : |z.re| ≤ r0 / 4 := by
    rw [abs_le]
    constructor <;> linarith
  have hz_im_low : r0 / 2 ≤ |z.im| := by
    have h1 := Complex.norm_le_abs_re_add_abs_im z
    linarith
  obtain ⟨h_pole, h_double⟩ := h_s1 hR hη_pos hη_le1 hz_im_low hz_im_high
  rw [← hK1_def] at h_double
  have h1z_re_low : 3 / 4 ≤ (1 + z).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h1z_re_high : (1 + z).re ≤ 2 := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h1z_re_half : 1 / 2 ≤ (1 + z).re := by linarith
  have h1z_im_low : r0 / 2 ≤ |(1 + z).im| := by
    simpa [Complex.add_im, Complex.one_im] using hz_im_low
  have h1z_im_high : |(1 + z).im| ≤ R := by
    simpa [Complex.add_im, Complex.one_im] using hz_im_high
  have h_deriv_1z : ‖deriv riemannZeta (1 + z)‖ ≤ K2 * (R + 2) := by
    rw [hK2_def]
    exact h_s2 hR h1z_re_low h1z_re_high h1z_im_low h1z_im_high
  have h_step : ‖riemannZeta (((1 + η : ℝ) : ℂ) + (z.im : ℂ) * Complex.I) - riemannZeta (1 + z)‖ ≤
      K2 * (R + 2) * (η - z.re) := by
    apply h_s3 hz_re_ge_neg_quarter hz_re_high hη_pos hη_le1 hz_im_low hz_im_high
    intro s hs1 hs2 hs3 hs4
    rw [hK2_def]
    exact h_s2 hR hs1 hs2 hs3 hs4
  have h_341_pt := @h_341 (1 + η) z.im (by linarith)
  rw [hC1_def]
  exact h_s4 hR hK1_pos hK2_pos ha_pos hη_def ha_le_K
    hz_re_low hz_re_high h1z_re_half hz_norm h_341_pt h_pole h_double h_step h_deriv_1z

theorem zeta_log_deriv_sub_pole_analytic_bound : ∃ (g : ℂ → ℂ) (a C : ℝ), 0 < a ∧ 0 < C ∧
      (∀ z : ℂ, 0 < z.re →
        g z = -deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, -a * (R + 2) ^ (-5 : ℝ) ≤ z.re → |z.im| ≤ R →
        DifferentiableAt ℂ g z) ∧
      (∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, -a * (R + 2) ^ (-5 : ℝ) ≤ z.re → z.re ≤ 0 → |z.im| ≤ R →
        ‖g z‖ ≤ C * (R + 2) ^ (5 : ℝ)) :=
by
  obtain ⟨g, r0, M0, hr0_pos, hr0_le, hM0_pos, hg_away, hg_right, hg_ball⟩ :=
    zeta_log_deriv_sub_pole_extension
  obtain ⟨a, C1, ha_pos, ha_le, hC1_pos, h_strip⟩ :=
    zeta_strip_nonvanishing_and_log_deriv_bound hr0_pos hr0_le
      (@riemannZeta_norm_le_on_half_plane) (@riemannZeta_three_four_one_ineq)
  have hC_pos : 0 < max M0 C1 := lt_max_of_lt_left hM0_pos
  refine ⟨g, a, max M0 C1, ha_pos, hC_pos, ?_, ?_, ?_⟩
  · intro z hz_re
    have hz_ne : z ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at hz_re
      exact lt_irrefl 0 hz_re
    have h1z_re : 1 ≤ (1 + z).re := by
      rw [Complex.add_re, Complex.one_re]
      linarith
    have h1z_ne : 1 + z ≠ 0 := by
      intro h
      rw [h, Complex.zero_re] at h1z_re
      linarith
    have hzeta_ne : riemannZeta (1 + z) ≠ 0 := riemannZeta_ne_zero_of_one_le_re h1z_re
    exact (hg_away z hz_ne h1z_ne hzeta_ne).2
  · intro R hR z hz_low hz_im
    rcases le_or_gt 0 z.re with hz_nonneg | hz_neg
    · exact hg_right z hz_nonneg
    · rcases le_or_gt ‖z‖ r0 with hz_norm | hz_norm
      · exact (hg_ball z hz_norm).1
      · have hz_ne : z ≠ 0 := by
          intro h
          rw [h, norm_zero] at hz_norm
          linarith
        have hR2_pos : 0 < R + 2 := by linarith
        have hR2_ge1 : 1 ≤ R + 2 := by linarith
        have hrpow_le1 : (R + 2) ^ (-5 : ℝ) ≤ 1 := by
          calc (R + 2) ^ (-5 : ℝ)
            _ ≤ (R + 2) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR2_ge1 (by norm_num)
            _ = 1 := Real.rpow_zero _
        have hrpow_nonneg : 0 ≤ (R + 2) ^ (-5 : ℝ) := Real.rpow_nonneg (le_of_lt hR2_pos) _
        have hz_re_ge : -a ≤ z.re := by nlinarith
        have h1z_re : 0 < (1 + z).re := by
          rw [Complex.add_re, Complex.one_re]
          linarith
        have h1z_ne : 1 + z ≠ 0 := by
          intro h
          rw [h, Complex.zero_re] at h1z_re
          exact lt_irrefl 0 h1z_re
        have hzeta_ne : riemannZeta (1 + z) ≠ 0 :=
          (h_strip R hR z hz_low (le_of_lt hz_neg) hz_im hz_norm).1
        exact (hg_away z hz_ne h1z_ne hzeta_ne).1
  · intro R hR z hz_low hz_high hz_im
    have hR2_pos : 0 < R + 2 := by linarith
    have hR2_ge1 : 1 ≤ R + 2 := by linarith
    have hrpow5_ge1 : 1 ≤ (R + 2) ^ (5 : ℝ) := by
      calc (1 : ℝ)
        _ = (R + 2) ^ (0 : ℝ) := (Real.rpow_zero _).symm
        _ ≤ (R + 2) ^ (5 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR2_ge1 (by norm_num)
    have hrpow5_nonneg : 0 ≤ (R + 2) ^ (5 : ℝ) := by linarith
    rcases le_or_gt ‖z‖ r0 with hz_norm | hz_norm
    · have hg_le : ‖g z‖ ≤ M0 := (hg_ball z hz_norm).2
      have hM0_le : M0 ≤ max M0 C1 := le_max_left M0 C1
      calc ‖g z‖
        _ ≤ M0 := hg_le
        _ ≤ max M0 C1 * 1 := by linarith
        _ ≤ max M0 C1 * (R + 2) ^ (5 : ℝ) := by nlinarith
    · have hz_ne : z ≠ 0 := by
        intro h
        rw [h, norm_zero] at hz_norm
        linarith
      have hrpow_le1 : (R + 2) ^ (-5 : ℝ) ≤ 1 := by
        calc (R + 2) ^ (-5 : ℝ)
          _ ≤ (R + 2) ^ (0 : ℝ) := Real.rpow_le_rpow_of_exponent_le hR2_ge1 (by norm_num)
          _ = 1 := Real.rpow_zero _
      have hrpow_nonneg : 0 ≤ (R + 2) ^ (-5 : ℝ) := Real.rpow_nonneg (le_of_lt hR2_pos) _
      have hz_re_ge : -a ≤ z.re := by nlinarith
      have h1z_re : 0 < (1 + z).re := by
        rw [Complex.add_re, Complex.one_re]
        linarith
      have h1z_ne : 1 + z ≠ 0 := by
        intro h
        rw [h, Complex.zero_re] at h1z_re
        exact lt_irrefl 0 h1z_re
      obtain ⟨hzeta_ne, hbound⟩ := h_strip R hR z hz_low hz_high hz_im hz_norm
      rw [(hg_away z hz_ne h1z_ne hzeta_ne).2]
      have hC1_le : C1 ≤ max M0 C1 := le_max_right M0 C1
      calc ‖-deriv riemannZeta (1 + z) / ((1 + z) * riemannZeta (1 + z)) - 1 / z‖
        _ ≤ C1 * (R + 2) ^ (5 : ℝ) := hbound
        _ ≤ max M0 C1 * (R + 2) ^ (5 : ℝ) := by nlinarith

theorem truncated_laplace_holomorphic_and_bounds {f : ℝ → ℝ} {M : ℝ} {g : ℂ → ℂ}
    (hf_meas : Measurable f) (hM : 0 < M)
    (hf_bound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (hg_laplace : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
    (T : ℝ) (hT : 0 ≤ T) :
    let g_T : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))
    Differentiable ℂ g_T ∧
    (∀ z : ℂ, 0 < z.re → ‖g z - g_T z‖ ≤ M * Real.exp (-T * z.re) / z.re) ∧
    (∀ z : ℂ, z.re < 0 → ‖g_T z‖ ≤ M * Real.exp (-T * z.re) / (-z.re)) :=
by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · intro z₀
    let F : ℂ → ℝ → ℂ := fun z t => (f t : ℂ) * Complex.exp (-z * (t : ℂ))
    let F' : ℂ → ℝ → ℂ := fun z t => (f t : ℂ) * (Complex.exp (-z * (t : ℂ)) * -(t : ℂ))
    let s : Set ℂ := Metric.ball z₀ 1
    let bound : ℝ → ℝ := fun _ => M * T * Real.exp ((‖z₀‖ + 1) * T)
    have hs : s ∈ nhds z₀ := Metric.ball_mem_nhds z₀ zero_lt_one
    have hF_meas : ∀ z : ℂ, Measurable (F z) := by
      intro z
      exact (Complex.measurable_ofReal.comp hf_meas).mul
        (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
    have hF'_meas : ∀ z : ℂ, Measurable (F' z) := by
      intro z
      exact (Complex.measurable_ofReal.comp hf_meas).mul
        ((Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal)).mul
          Complex.measurable_ofReal.neg)
    have h1 : ∀ᶠ z in nhds z₀, MeasureTheory.AEStronglyMeasurable (F z) (MeasureTheory.volume.restrict (Set.uIoc 0 T)) :=
      Filter.Eventually.of_forall (fun z => (hF_meas z).aestronglyMeasurable)
    have h2 : IntervalIntegrable (F z₀) MeasureTheory.volume 0 T := by
      have h_const : IntervalIntegrable (fun _ : ℝ => M * Real.exp (‖z₀‖ * T)) MeasureTheory.volume 0 T :=
        intervalIntegral.intervalIntegrable_const
      apply h_const.mono_fun' (hF_meas z₀).aestronglyMeasurable
      change ∀ᵐ t ∂MeasureTheory.volume.restrict (Set.uIoc 0 T), ‖F z₀ t‖ ≤ M * Real.exp (‖z₀‖ * T)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc, Set.uIoc_of_le hT]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have htT : t ≤ T := ht.2
      dsimp [F]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have h_re : (-z₀ * (t : ℂ)).re = -z₀.re * t := by simp
      rw [h_re]
      have h_re_le : -z₀.re * t ≤ ‖z₀‖ * T := by
        have h_z0 : -z₀.re ≤ ‖z₀‖ := by
          calc -z₀.re ≤ |z₀.re| := neg_le_abs _
          _ ≤ ‖z₀‖ := Complex.abs_re_le_norm z₀
        nlinarith [norm_nonneg z₀]
      exact mul_le_mul (hf_bound t ht0) (Real.exp_le_exp.mpr h_re_le) (Real.exp_nonneg _) (le_of_lt hM)
    have h3 : MeasureTheory.AEStronglyMeasurable (F' z₀) (MeasureTheory.volume.restrict (Set.uIoc 0 T)) :=
      (hF'_meas z₀).aestronglyMeasurable
    have h4 : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc 0 T → ∀ z ∈ s, ‖F' z t‖ ≤ bound t := by
      refine Filter.Eventually.of_forall (fun t ht z hz => ?_)
      rw [Set.uIoc_of_le hT] at ht
      have ht0 : 0 ≤ t := le_of_lt ht.1
      have htT : t ≤ T := ht.2
      have hz_norm : ‖z‖ ≤ ‖z₀‖ + 1 := by
        have hz_dist : ‖z - z₀‖ < 1 := by simpa [s, Metric.mem_ball, dist_eq_norm] using hz
        have h_tri : ‖z‖ ≤ ‖z - z₀‖ + ‖z₀‖ := norm_le_norm_sub_add z z₀
        linarith
      dsimp [F', bound]
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp,
          norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht0]
      have h_re : (-z * (t : ℂ)).re = -z.re * t := by simp
      rw [h_re]
      have h_re_le : -z.re * t ≤ (‖z₀‖ + 1) * T := by
        have h_z : -z.re ≤ ‖z‖ := by
          calc -z.re ≤ |z.re| := neg_le_abs _
          _ ≤ ‖z‖ := Complex.abs_re_le_norm z
        nlinarith [norm_nonneg z₀]
      have hexp_le : Real.exp (-z.re * t) ≤ Real.exp ((‖z₀‖ + 1) * T) :=
        Real.exp_le_exp.mpr h_re_le
      have hf_le : |f t| ≤ M := hf_bound t ht0
      calc |f t| * (Real.exp (-z.re * t) * t)
        _ = (|f t| * t) * Real.exp (-z.re * t) := by ring
        _ ≤ (M * T) * Real.exp ((‖z₀‖ + 1) * T) := by
          apply mul_le_mul
          · exact mul_le_mul hf_le htT ht0 (le_of_lt hM)
          · exact hexp_le
          · exact Real.exp_nonneg _
          · positivity
    have h5 : IntervalIntegrable bound MeasureTheory.volume 0 T := intervalIntegral.intervalIntegrable_const
    have h6 : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc 0 T → ∀ z ∈ s, HasDerivAt (fun x => F x t) (F' z t) z := by
      refine Filter.Eventually.of_forall (fun t _ z _ => ?_)
      dsimp [F, F']
      have hd1 : HasDerivAt (fun x : ℂ => -x * (t : ℂ)) (-(t : ℂ)) z := by
        simpa using ((hasDerivAt_id z).neg.mul_const (t : ℂ))
      exact (hd1.cexp).const_mul (f t : ℂ)
    exact (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le hs h1 h2 h3 h4 h5 h6).2.differentiableAt
  · intro z hz
    let h : ℝ → ℂ := fun t => (f t : ℂ) * Complex.exp (-z * (t : ℂ))
    let b : ℝ → ℝ := fun t => M * Real.exp (-z.re * t)
    have hz_neg : -z.re < 0 := neg_lt_zero.mpr hz
    have hh_meas : Measurable h :=
      (Complex.measurable_ofReal.comp hf_meas).mul
        (Complex.measurable_exp.comp (measurable_const.mul Complex.measurable_ofReal))
    have hb_int : ∀ c : ℝ, MeasureTheory.IntegrableOn b (Set.Ioi c) MeasureTheory.volume := by
      intro c
      exact (integrableOn_exp_mul_Ioi hz_neg c).const_mul M
    have hh_int : ∀ c : ℝ, 0 ≤ c → MeasureTheory.IntegrableOn h (Set.Ioi c) MeasureTheory.volume := by
      intro c hc
      apply MeasureTheory.Integrable.mono' (hb_int c) hh_meas.aestronglyMeasurable
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht_pos : 0 ≤ t := le_trans hc (le_of_lt ht)
      dsimp [h, b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have h_re : (-z * (t : ℂ)).re = -z.re * t := by simp
      rw [h_re]
      exact mul_le_mul_of_nonneg_right (hf_bound t ht_pos) (Real.exp_nonneg _)
    have hh_int_Ioc : MeasureTheory.IntegrableOn h (Set.Ioc 0 T) MeasureTheory.volume :=
      (hh_int 0 le_rfl).mono_set Set.Ioc_subset_Ioi_self
    have h_union : Set.Ioc (0 : ℝ) T ∪ Set.Ioi T = Set.Ioi (0 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hT
    have h_disj : Disjoint (Set.Ioc (0 : ℝ) T) (Set.Ioi T) :=
      Set.Ioc_disjoint_Ioi le_rfl
    have h_split : ∫ t in Set.Ioi (0 : ℝ), h t =
        (∫ t in Set.Ioc (0 : ℝ) T, h t) + ∫ t in Set.Ioi T, h t := by
      rw [← h_union]
      exact MeasureTheory.setIntegral_union h_disj measurableSet_Ioi hh_int_Ioc (hh_int T hT)
    have h_diff_eq : g z - (∫ t in (0 : ℝ)..T, h t) = ∫ t in Set.Ioi T, h t := by
      rw [hg_laplace z hz, intervalIntegral.integral_of_le hT]
      change (∫ t in Set.Ioi (0 : ℝ), h t) - (∫ t in Set.Ioc (0 : ℝ) T, h t) = ∫ t in Set.Ioi T, h t
      rw [h_split, add_sub_cancel_left]
    rw [h_diff_eq]
    have h_norm_le : ‖∫ t in Set.Ioi T, h t‖ ≤ ∫ t in Set.Ioi T, b t := by
      apply MeasureTheory.norm_integral_le_of_norm_le (hb_int T)
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall (fun t ht => ?_)
      have ht_pos : 0 ≤ t := le_trans hT (le_of_lt ht)
      dsimp [h, b]
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
      have h_re : (-z * (t : ℂ)).re = -z.re * t := by simp
      rw [h_re]
      exact mul_le_mul_of_nonneg_right (hf_bound t ht_pos) (Real.exp_nonneg _)
    have h_tail_val : ∫ t in Set.Ioi T, b t = M * Real.exp (-T * z.re) / z.re := by
      dsimp [b]
      rw [MeasureTheory.integral_const_mul, integral_exp_mul_Ioi hz_neg T]
      have : -z.re * T = -T * z.re := by ring
      rw [this]
      ring
    linarith
  · intro z hz
    let b : ℝ → ℝ := fun t => M * Real.exp (-z.re * t)
    have hb_cont : Continuous b :=
      continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul continuous_id))
    have hb_int : IntervalIntegrable b MeasureTheory.volume 0 T := hb_cont.intervalIntegrable 0 T
    have h_norm_le : ‖∫ t in (0 : ℝ)..T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))‖ ≤
        ∫ t in (0 : ℝ)..T, b t := by
      apply intervalIntegral.norm_integral_le_of_norm_le hT
      · refine Filter.Eventually.of_forall (fun t ht => ?_)
        have ht0 : 0 ≤ t := le_of_lt ht.1
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, Complex.norm_exp]
        have h_re : (-z * (t : ℂ)).re = -z.re * t := by simp
        rw [h_re]
        exact mul_le_mul_of_nonneg_right (hf_bound t ht0) (Real.exp_nonneg _)
      · exact hb_int
    let B : ℝ → ℝ := fun t => (M / (-z.re)) * Real.exp (-z.re * t)
    have hz_pos : 0 < -z.re := neg_pos.mpr hz
    have hz_ne : z.re ≠ 0 := ne_of_lt hz
    have hB_deriv : ∀ t ∈ Set.uIcc (0 : ℝ) T, HasDerivAt B (b t) t := by
      intro t _
      have h1 : HasDerivAt (fun x : ℝ => -z.re * x) (-z.re) t := by
        simpa using (hasDerivAt_id t).const_mul (-z.re)
      have h2 : HasDerivAt (fun x : ℝ => Real.exp (-z.re * x)) (Real.exp (-z.re * t) * (-z.re)) t :=
        h1.exp
      have h3 := h2.const_mul (M / (-z.re))
      have h_eq : (M / (-z.re)) * (Real.exp (-z.re * t) * (-z.re)) = b t := by
        dsimp [b]
        field_simp [hz_ne]
      rwa [h_eq] at h3
    have h_ftc : ∫ t in (0 : ℝ)..T, b t = B T - B 0 :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt hB_deriv hb_int
    have hB0_pos : 0 ≤ B 0 := by
      dsimp [B]
      simp only [mul_zero, Real.exp_zero, mul_one]
      exact div_nonneg (le_of_lt hM) (le_of_lt hz_pos)
    have hBT : B T = M * Real.exp (-T * z.re) / (-z.re) := by
      dsimp [B]
      have : -z.re * T = -T * z.re := by ring
      rw [this, div_mul_eq_mul_div]
    linarith

theorem rect_cauchy_norm_at_zero_le {δ R : ℝ} {F : ℂ → ℂ} (hδ : 0 < δ) (hδR : δ ≤ R)
    (hF : DifferentiableOn ℂ F (Complex.reProdIm (Set.uIcc (-δ) R) (Set.uIcc (-R) R))) :
    ‖F 0‖ ≤ ‖((∫ x : ℝ in (-δ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-δ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
      Complex.I * (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I))‖ :=
by
  have hR : 0 < R := lt_of_lt_of_le hδ hδR
  set S : Set ℂ := Complex.reProdIm (Set.uIcc (-δ) R) (Set.uIcc (-R) R)
  have hS_nhds : S ∈ nhds (0 : ℂ) := by
    apply Filter.mem_of_superset (Metric.ball_mem_nhds (0 : ℂ) hδ)
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz
    have h_uIcc_re : Set.uIcc (-δ) R = Set.Icc (-δ) R := Set.uIcc_of_le (by linarith)
    have h_uIcc_im : Set.uIcc (-R) R = Set.Icc (-R) R := Set.uIcc_of_le (by linarith)
    have h_re : |z.re| < δ := lt_of_le_of_lt (Complex.abs_re_le_norm z) hz
    have h_im : |z.im| < δ := lt_of_le_of_lt (Complex.abs_im_le_norm z) hz
    rw [abs_lt] at h_re h_im
    refine ⟨?_, ?_⟩
    · rw [h_uIcc_re]
      exact ⟨by linarith, by linarith⟩
    · rw [h_uIcc_im]
      exact ⟨by linarith, by linarith⟩
  have hdslope_diff : DifferentiableOn ℂ (dslope F 0) S :=
    (Complex.differentiableOn_dslope hS_nhds).mpr hF
  let z0 : ℂ := (-δ : ℝ) + (-R : ℝ) * Complex.I
  let w0 : ℂ := (R : ℝ) + (R : ℝ) * Complex.I
  have hz0_re : z0.re = -δ := by simp [z0]
  have hz0_im : z0.im = -R := by simp [z0]
  have hw0_re : w0.re = R := by simp [w0]
  have hw0_im : w0.im = R := by simp [w0]
  have h_rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (dslope F 0) z0 w0
  rw [hz0_re, hz0_im, hw0_re, hw0_im, smul_eq_mul, smul_eq_mul] at h_rect
  have h_zero := h_rect hdslope_diff
  have h_dslope_seg : ∀ (a b : ℝ) (γ : ℝ → ℂ), Continuous γ →
      Set.MapsTo γ (Set.uIcc a b) S →
      (∀ t ∈ Set.uIcc a b, γ t ≠ 0) →
      (∫ t in a..b, dslope F 0 (γ t)) =
        (∫ t in a..b, F (γ t) / γ t) - F 0 * (∫ t in a..b, (γ t)⁻¹) := by
    intro a b γ hγ_cont hγ_mem hγ_ne
    have hF_γ : ContinuousOn (fun t => F (γ t)) (Set.uIcc a b) :=
      hF.continuousOn.comp hγ_cont.continuousOn hγ_mem
    have h_div_int : IntervalIntegrable (fun t => F (γ t) / γ t) MeasureTheory.volume a b :=
      (hF_γ.div hγ_cont.continuousOn hγ_ne).intervalIntegrable
    have h_mul_int : IntervalIntegrable (fun t => F 0 * (γ t)⁻¹) MeasureTheory.volume a b :=
      (continuousOn_const.mul (hγ_cont.continuousOn.inv₀ hγ_ne)).intervalIntegrable
    have h_congr : (∫ t in a..b, dslope F 0 (γ t)) =
        ∫ t in a..b, (F (γ t) / γ t - F 0 * (γ t)⁻¹) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      rw [dslope_of_ne F (hγ_ne t ht), slope_def_field, sub_zero, sub_div,
          div_eq_mul_inv (F 0) (γ t)]
    rw [h_congr, intervalIntegral.integral_sub h_div_int h_mul_int,
        intervalIntegral.integral_const_mul]
  have h1_cont : Continuous (fun x : ℝ => (x : ℂ) + (-R : ℝ) * Complex.I) := by fun_prop
  have h2_cont : Continuous (fun x : ℝ => (x : ℂ) + (R : ℝ) * Complex.I) := by fun_prop
  have h3_cont : Continuous (fun y : ℝ => (R : ℝ) + (y : ℂ) * Complex.I) := by fun_prop
  have h4_cont : Continuous (fun y : ℝ => (-δ : ℝ) + (y : ℂ) * Complex.I) := by fun_prop
  have h_im_negR : (-R : ℝ) ∈ Set.uIcc (-R) R := Set.left_mem_uIcc
  have h_im_R : (R : ℝ) ∈ Set.uIcc (-R) R := Set.right_mem_uIcc
  have h_re_negδ : (-δ : ℝ) ∈ Set.uIcc (-δ) R := Set.left_mem_uIcc
  have h_re_R : (R : ℝ) ∈ Set.uIcc (-δ) R := Set.right_mem_uIcc
  have h1_mem : Set.MapsTo (fun x : ℝ => (x : ℂ) + (-R : ℝ) * Complex.I) (Set.uIcc (-δ) R) S := by
    intro x hx; refine ⟨?_, ?_⟩ <;> simp [hx, h_im_negR]
  have h2_mem : Set.MapsTo (fun x : ℝ => (x : ℂ) + (R : ℝ) * Complex.I) (Set.uIcc (-δ) R) S := by
    intro x hx; refine ⟨?_, ?_⟩ <;> simp [hx, h_im_R]
  have h3_mem : Set.MapsTo (fun y : ℝ => (R : ℝ) + (y : ℂ) * Complex.I) (Set.uIcc (-R) R) S := by
    intro y hy; refine ⟨?_, ?_⟩ <;> simp [hy, h_re_R]
  have h4_mem : Set.MapsTo (fun y : ℝ => (-δ : ℝ) + (y : ℂ) * Complex.I) (Set.uIcc (-R) R) S := by
    intro y hy; refine ⟨?_, ?_⟩ <;> simp [hy, h_re_negδ]
  have h1_ne : ∀ x ∈ Set.uIcc (-δ) R, (x : ℂ) + (-R : ℝ) * Complex.I ≠ 0 := by
    intro x _ h0; have := congr_arg Complex.im h0; simp at this; linarith
  have h2_ne : ∀ x ∈ Set.uIcc (-δ) R, (x : ℂ) + (R : ℝ) * Complex.I ≠ 0 := by
    intro x _ h0; have := congr_arg Complex.im h0; simp at this; linarith
  have h3_ne : ∀ y ∈ Set.uIcc (-R) R, (R : ℝ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro y _ h0; have := congr_arg Complex.re h0; simp at this; linarith
  have h4_ne : ∀ y ∈ Set.uIcc (-R) R, (-δ : ℝ) + (y : ℂ) * Complex.I ≠ 0 := by
    intro y _ h0; have := congr_arg Complex.re h0; simp at this; linarith
  have h_seg1 := h_dslope_seg (-δ) R _ h1_cont h1_mem h1_ne
  have h_seg2 := h_dslope_seg (-δ) R _ h2_cont h2_mem h2_ne
  have h_seg3 := h_dslope_seg (-R) R _ h3_cont h3_mem h3_ne
  have h_seg4 := h_dslope_seg (-R) R _ h4_cont h4_mem h4_ne
  rw [h_seg1, h_seg2, h_seg3, h_seg4] at h_zero
  have h_eq : ((∫ x : ℝ in (-δ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-δ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
      Complex.I * (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I)) =
    F 0 * (((∫ x : ℝ in (-δ)..R, (x + (-R : ℝ) * Complex.I)⁻¹) -
      (∫ x : ℝ in (-δ)..R, (x + (R : ℝ) * Complex.I)⁻¹) +
      Complex.I * (∫ y : ℝ in (-R)..R, ((R : ℝ) + y * Complex.I)⁻¹)) -
      Complex.I * (∫ y : ℝ in (-R)..R, ((-δ : ℝ) + y * Complex.I)⁻¹)) := by
    linear_combination h_zero
  rw [h_eq, norm_mul]
  have h1_int : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (-R : ℝ) * Complex.I)⁻¹) MeasureTheory.volume (-δ) R :=
    (h1_cont.continuousOn.inv₀ h1_ne).intervalIntegrable
  have h2_int : IntervalIntegrable (fun x : ℝ => ((x : ℂ) + (R : ℝ) * Complex.I)⁻¹) MeasureTheory.volume (-δ) R :=
    (h2_cont.continuousOn.inv₀ h2_ne).intervalIntegrable
  have h3_int : IntervalIntegrable (fun y : ℝ => ((R : ℝ) + (y : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-R) R :=
    (h3_cont.continuousOn.inv₀ h3_ne).intervalIntegrable
  have h4_int : IntervalIntegrable (fun y : ℝ => ((-δ : ℝ) + (y : ℂ) * Complex.I)⁻¹) MeasureTheory.volume (-R) R :=
    (h4_cont.continuousOn.inv₀ h4_ne).intervalIntegrable
  have him1 : (∫ x : ℝ in (-δ)..R, ((x : ℂ) + (-R : ℝ) * Complex.I)⁻¹).im =
      ∫ x : ℝ in (-δ)..R, (((x : ℂ) + (-R : ℝ) * Complex.I)⁻¹).im :=
    (Complex.imCLM.intervalIntegral_comp_comm h1_int).symm
  have him2 : (∫ x : ℝ in (-δ)..R, ((x : ℂ) + (R : ℝ) * Complex.I)⁻¹).im =
      ∫ x : ℝ in (-δ)..R, (((x : ℂ) + (R : ℝ) * Complex.I)⁻¹).im :=
    (Complex.imCLM.intervalIntegral_comp_comm h2_int).symm
  have hre3 : (∫ y : ℝ in (-R)..R, ((R : ℝ) + (y : ℂ) * Complex.I)⁻¹).re =
      ∫ y : ℝ in (-R)..R, (((R : ℝ) + (y : ℂ) * Complex.I)⁻¹).re :=
    (Complex.reCLM.intervalIntegral_comp_comm h3_int).symm
  have hre4 : (∫ y : ℝ in (-R)..R, ((-δ : ℝ) + (y : ℂ) * Complex.I)⁻¹).re =
      ∫ y : ℝ in (-R)..R, (((-δ : ℝ) + (y : ℂ) * Complex.I)⁻¹).re :=
    (Complex.reCLM.intervalIntegral_comp_comm h4_int).symm
  have h_im1_nonneg : 0 ≤ ∫ x : ℝ in (-δ)..R, (((x : ℂ) + (-R : ℝ) * Complex.I)⁻¹).im := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro x _
    rw [Complex.inv_im]
    simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_re, mul_zero, Complex.I_im, mul_one, add_zero, zero_add, neg_neg]
    exact div_nonneg (le_of_lt hR) (Complex.normSq_nonneg _)
  have h_im2_nonpos : ∫ x : ℝ in (-δ)..R, (((x : ℂ) + (R : ℝ) * Complex.I)⁻¹).im ≤ 0 := by
    have : (fun x : ℝ => (((x : ℂ) + (R : ℝ) * Complex.I)⁻¹).im) =
        fun x : ℝ => -(((x : ℂ) + (-R : ℝ) * Complex.I)⁻¹).im := by
      ext x
      rw [Complex.inv_im, Complex.inv_im]
      simp [Complex.normSq_apply]
      ring
    rw [this, intervalIntegral.integral_neg]
    linarith
  have h_re4_nonpos : ∫ y : ℝ in (-R)..R, (((-δ : ℝ) + (y : ℂ) * Complex.I)⁻¹).re ≤ 0 := by
    have h_neg_nonneg : 0 ≤ ∫ y : ℝ in (-R)..R, -((((-δ : ℝ) + (y : ℂ) * Complex.I)⁻¹).re) := by
      apply intervalIntegral.integral_nonneg (by linarith)
      intro y _
      rw [Complex.inv_re]
      simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
        Complex.I_re, mul_zero, Complex.I_im, mul_one, sub_self, add_zero, neg_div, neg_neg]
      exact div_nonneg (le_of_lt hδ) (Complex.normSq_nonneg _)
    rw [intervalIntegral.integral_neg] at h_neg_nonneg
    linarith
  have h_re3_ge_one : 1 ≤ ∫ y : ℝ in (-R)..R, (((R : ℝ) + (y : ℂ) * Complex.I)⁻¹).re := by
    have h_re3_int : IntervalIntegrable (fun y : ℝ => (((R : ℝ) + (y : ℂ) * Complex.I)⁻¹).re) MeasureTheory.volume (-R) R :=
      (Complex.reCLM.continuous.comp_continuousOn (h3_cont.continuousOn.inv₀ h3_ne)).intervalIntegrable
    have h_const_int : IntervalIntegrable (fun _ : ℝ => (1 / (2 * R) : ℝ)) MeasureTheory.volume (-R) R :=
      intervalIntegrable_const
    have h_mono : (∫ y : ℝ in (-R)..R, (1 / (2 * R) : ℝ)) ≤
        ∫ y : ℝ in (-R)..R, (((R : ℝ) + (y : ℂ) * Complex.I)⁻¹).re := by
      apply intervalIntegral.integral_mono_on (by linarith) h_const_int h_re3_int
      intro y hy
      rw [Complex.inv_re]
      have h_re_val : ((R : ℝ) + (y : ℂ) * Complex.I).re = R := by simp
      have h_normSq : Complex.normSq ((R : ℝ) + (y : ℂ) * Complex.I) = R * R + y * y := by
        simp [Complex.normSq_apply]
      rw [h_re_val, h_normSq]
      have hy_sq : y * y ≤ R * R := by
        nlinarith [hy.1, hy.2]
      have h_denom_pos : 0 < R * R + y * y := by
        nlinarith [mul_self_nonneg y, mul_pos hR hR]
      have h2R_pos : 0 < 2 * R := by linarith
      rw [div_le_div_iff₀ h2R_pos h_denom_pos]
      nlinarith
    have h_const_eval : (∫ y : ℝ in (-R)..R, (1 / (2 * R) : ℝ)) = 1 := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      have : R - -R = 2 * R := by ring
      rw [this]
      have h2R_ne : 2 * R ≠ 0 := by linarith
      exact mul_one_div_cancel h2R_ne
    linarith
  have h_im_le : 1 ≤ (((∫ x : ℝ in (-δ)..R, (x + (-R : ℝ) * Complex.I)⁻¹) -
      (∫ x : ℝ in (-δ)..R, (x + (R : ℝ) * Complex.I)⁻¹) +
      Complex.I * (∫ y : ℝ in (-R)..R, ((R : ℝ) + y * Complex.I)⁻¹)) -
      Complex.I * (∫ y : ℝ in (-R)..R, ((-δ : ℝ) + y * Complex.I)⁻¹)).im := by
    simp only [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im,
      one_mul, zero_mul, zero_add, him1, him2, hre3, hre4]
    linarith
  have h_one_le_norm : 1 ≤ ‖(((∫ x : ℝ in (-δ)..R, (x + (-R : ℝ) * Complex.I)⁻¹) -
      (∫ x : ℝ in (-δ)..R, (x + (R : ℝ) * Complex.I)⁻¹) +
      Complex.I * (∫ y : ℝ in (-R)..R, ((R : ℝ) + y * Complex.I)⁻¹)) -
      Complex.I * (∫ y : ℝ in (-R)..R, ((-δ : ℝ) + y * Complex.I)⁻¹))‖ :=
    le_trans h_im_le (le_trans (le_abs_self _) (Complex.abs_im_le_norm _))
  exact le_mul_of_one_le_right (norm_nonneg (F 0)) h_one_le_norm

theorem newman_rect_contour_shift_decomp {H_g H_T : ℂ → ℂ} {R δ : ℝ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hHg : ∀ z : ℂ, -δ ≤ z.re → |z.im| ≤ R → DifferentiableAt ℂ H_g z)
    (hHT : Differentiable ℂ H_T) :
    let F : ℂ → ℂ := fun z => H_g z - H_T z
    ((∫ x : ℝ in (-δ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-δ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
      Complex.I * (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I)) =
    (((∫ x : ℝ in (0 : ℝ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (0 : ℝ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
    ((∫ x : ℝ in (-R)..(0 : ℝ), H_T (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-R)..(0 : ℝ), H_T (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-R)..R, H_T ((-R : ℝ) + y * Complex.I) / ((-R : ℝ) + y * Complex.I)))) +
    ((∫ x : ℝ in (-δ)..(0 : ℝ), H_g (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-δ)..(0 : ℝ), H_g (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) -
      Complex.I * (∫ y : ℝ in (-R)..R, H_g ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I))) :=
by
  intro F
  have h_cauchy :
      ((∫ x : ℝ in (-R)..(-δ), H_T (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
        (∫ x : ℝ in (-R)..(-δ), H_T (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-R)..R, H_T ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I))) -
        Complex.I * (∫ y : ℝ in (-R)..R, H_T ((-R : ℝ) + y * Complex.I) / ((-R : ℝ) + y * Complex.I)) = 0 := by
    let z1 : ℂ := (-R : ℝ) + (-R : ℝ) * Complex.I
    let w1 : ℂ := (-δ : ℝ) + (R : ℝ) * Complex.I
    have hz1_re : z1.re = -R := by simp [z1]
    have hz1_im : z1.im = -R := by simp [z1]
    have hw1_re : w1.re = -δ := by simp [w1]
    have hw1_im : w1.im = R := by simp [w1]
    have h_diff : DifferentiableOn ℂ (fun z : ℂ => H_T z / z)
        (Complex.reProdIm (Set.uIcc z1.re w1.re) (Set.uIcc z1.im w1.im)) := by
      intro z hz
      have h_uIcc : Set.uIcc z1.re w1.re = Set.Icc (-R) (-δ) := by
        rw [hz1_re, hw1_re]
        exact Set.uIcc_of_le (by linarith)
      have hz_re : z.re ≤ -δ := by
        have h1 : z.re ∈ Set.uIcc z1.re w1.re := hz.1
        rw [h_uIcc] at h1
        exact h1.2
      have hz_ne : z ≠ 0 := by
        intro h0
        have : z.re = 0 := by simp [h0]
        linarith
      exact ((hHT z).div differentiableAt_id hz_ne).differentiableWithinAt
    have h_rect := Complex.integral_boundary_rect_eq_zero_of_differentiableOn (fun z : ℂ => H_T z / z) z1 w1 h_diff
    rw [hz1_re, hz1_im, hw1_re, hw1_im, smul_eq_mul, smul_eq_mul] at h_rect
    exact h_rect
  have h_horiz : ∀ (y0 : ℝ), |y0| = R →
      (∫ x : ℝ in (-δ)..R, F (x + (y0 : ℝ) * Complex.I) / (x + (y0 : ℝ) * Complex.I)) =
        (∫ x : ℝ in (0 : ℝ)..R, F (x + (y0 : ℝ) * Complex.I) / (x + (y0 : ℝ) * Complex.I)) +
        (∫ x : ℝ in (-δ)..(0 : ℝ), H_g (x + (y0 : ℝ) * Complex.I) / (x + (y0 : ℝ) * Complex.I)) -
        ((∫ x : ℝ in (-R)..(0 : ℝ), H_T (x + (y0 : ℝ) * Complex.I) / (x + (y0 : ℝ) * Complex.I)) -
         (∫ x : ℝ in (-R)..(-δ), H_T (x + (y0 : ℝ) * Complex.I) / (x + (y0 : ℝ) * Complex.I))) := by
    intro y0 hy0
    let γ : ℝ → ℂ := fun x => (x : ℂ) + (y0 : ℝ) * Complex.I
    have hγ_cont : Continuous γ := by fun_prop
    have hγ_ne : ∀ x : ℝ, γ x ≠ 0 := by
      intro x h0
      have him : (γ x).im = 0 := by rw [h0, Complex.zero_im]
      have him_eq : (γ x).im = y0 := by simp [γ]
      have hy0_zero : y0 = 0 := by linarith
      have : |y0| = 0 := by simp [hy0_zero]
      linarith
    have hHT_cont : Continuous (fun x : ℝ => H_T (γ x) / γ x) :=
      (hHT.continuous.comp hγ_cont).div hγ_cont hγ_ne
    have hHg_on : ContinuousOn (fun x : ℝ => H_g (γ x)) (Set.Icc (-δ) R) := by
      intro x hx
      have hx_re : -δ ≤ (γ x).re := by
        have : (γ x).re = x := by simp [γ]
        linarith [hx.1]
      have hx_im : |(γ x).im| ≤ R := by
        have : (γ x).im = y0 := by simp [γ]
        rw [this, hy0]
      exact ((hHg (γ x) hx_re hx_im).continuousAt.comp hγ_cont.continuousAt).continuousWithinAt
    have hHg_div_on : ContinuousOn (fun x : ℝ => H_g (γ x) / γ x) (Set.Icc (-δ) R) :=
      hHg_on.div hγ_cont.continuousOn (fun x _ => hγ_ne x)
    have hHg_int_negδ_0 : IntervalIntegrable (fun x : ℝ => H_g (γ x) / γ x) MeasureTheory.volume (-δ) 0 := by
      apply ContinuousOn.intervalIntegrable
      apply hHg_div_on.mono
      rw [Set.uIcc_of_le (by linarith)]
      intro x hx
      exact ⟨hx.1, by linarith [hx.2]⟩
    have hHg_int_0_R : IntervalIntegrable (fun x : ℝ => H_g (γ x) / γ x) MeasureTheory.volume 0 R := by
      apply ContinuousOn.intervalIntegrable
      apply hHg_div_on.mono
      rw [Set.uIcc_of_le (by linarith)]
      intro x hx
      exact ⟨by linarith [hx.1], hx.2⟩
    have hHT_int_negR_negδ : IntervalIntegrable (fun x : ℝ => H_T (γ x) / γ x) MeasureTheory.volume (-R) (-δ) :=
      hHT_cont.intervalIntegrable (-R) (-δ)
    have hHT_int_negδ_0 : IntervalIntegrable (fun x : ℝ => H_T (γ x) / γ x) MeasureTheory.volume (-δ) 0 :=
      hHT_cont.intervalIntegrable (-δ) 0
    have hHT_int_0_R : IntervalIntegrable (fun x : ℝ => H_T (γ x) / γ x) MeasureTheory.volume 0 R :=
      hHT_cont.intervalIntegrable 0 R
    have hF_div : (fun x : ℝ => F (γ x) / γ x) = fun x : ℝ => H_g (γ x) / γ x - H_T (γ x) / γ x := by
      ext x
      exact sub_div (H_g (γ x)) (H_T (γ x)) (γ x)
    have hF_int_negδ_0 : IntervalIntegrable (fun x : ℝ => F (γ x) / γ x) MeasureTheory.volume (-δ) 0 := by
      rw [hF_div]
      exact hHg_int_negδ_0.sub hHT_int_negδ_0
    have hF_int_0_R : IntervalIntegrable (fun x : ℝ => F (γ x) / γ x) MeasureTheory.volume 0 R := by
      rw [hF_div]
      exact hHg_int_0_R.sub hHT_int_0_R
    have h_split_F := intervalIntegral.integral_add_adjacent_intervals hF_int_negδ_0 hF_int_0_R
    have h_sub_F : (∫ x : ℝ in (-δ)..(0 : ℝ), F (γ x) / γ x) =
        (∫ x : ℝ in (-δ)..(0 : ℝ), H_g (γ x) / γ x) - (∫ x : ℝ in (-δ)..(0 : ℝ), H_T (γ x) / γ x) := by
      rw [hF_div]
      exact intervalIntegral.integral_sub hHg_int_negδ_0 hHT_int_negδ_0
    have h_split_HT := intervalIntegral.integral_add_adjacent_intervals hHT_int_negR_negδ hHT_int_negδ_0
    dsimp [γ] at h_split_F h_sub_F h_split_HT
    linear_combination -h_split_F + h_sub_F - h_split_HT
  have h_vert :
      (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I)) =
        (∫ y : ℝ in (-R)..R, H_g ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I)) -
        (∫ y : ℝ in (-R)..R, H_T ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I)) := by
    let γv : ℝ → ℂ := fun y => (-δ : ℝ) + (y : ℂ) * Complex.I
    have hγv_cont : Continuous γv := by fun_prop
    have hγv_ne : ∀ y : ℝ, γv y ≠ 0 := by
      intro y h0
      have hre : (γv y).re = 0 := by rw [h0, Complex.zero_re]
      have hre_eq : (γv y).re = -δ := by simp [γv]
      linarith
    have hHT_int : IntervalIntegrable (fun y : ℝ => H_T (γv y) / γv y) MeasureTheory.volume (-R) R :=
      ((hHT.continuous.comp hγv_cont).div hγv_cont hγv_ne).intervalIntegrable (-R) R
    have hHg_on : ContinuousOn (fun y : ℝ => H_g (γv y)) (Set.uIcc (-R) R) := by
      intro y hy
      rw [Set.uIcc_of_le (by linarith)] at hy
      have hy_re : -δ ≤ (γv y).re := by
        have : (γv y).re = -δ := by simp [γv]
        linarith
      have hy_im : |(γv y).im| ≤ R := by
        have : (γv y).im = y := by simp [γv]
        rw [this]
        exact abs_le.mpr ⟨hy.1, hy.2⟩
      exact ((hHg (γv y) hy_re hy_im).continuousAt.comp hγv_cont.continuousAt).continuousWithinAt
    have hHg_int : IntervalIntegrable (fun y : ℝ => H_g (γv y) / γv y) MeasureTheory.volume (-R) R :=
      (hHg_on.div hγv_cont.continuousOn (fun y _ => hγv_ne y)).intervalIntegrable
    have hF_div : (fun y : ℝ => F (γv y) / γv y) = fun y : ℝ => H_g (γv y) / γv y - H_T (γv y) / γv y := by
      ext y
      exact sub_div (H_g (γv y)) (H_T (γv y)) (γv y)
    change (∫ y : ℝ in (-R)..R, F (γv y) / γv y) =
      (∫ y : ℝ in (-R)..R, H_g (γv y) / γv y) - (∫ y : ℝ in (-R)..R, H_T (γv y) / γv y)
    rw [hF_div]
    exact intervalIntegral.integral_sub hHg_int hHT_int
  have hy_neg : |-R| = R := by
    rw [abs_neg, abs_of_pos (by linarith)]
  have hy_pos : |R| = R := abs_of_pos (by linarith)
  have h_bot := h_horiz (-R) hy_neg
  have h_top := h_horiz R hy_pos
  linear_combination h_bot - h_top - Complex.I * h_vert + h_cauchy

theorem newman_horiz_segments_norm_le {g g_T : ℂ → ℂ} {T R M B δ y : ℝ}
    (hT : 0 < T) (hR : 1 ≤ R) (hM : 0 < M) (hB : 0 ≤ B) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hy : |y| = R)
    (h_right : ∀ z : ℂ, 0 < z.re → ‖g z - g_T z‖ ≤ M * Real.exp (-T * z.re) / z.re)
    (h_left : ∀ z : ℂ, z.re < 0 → ‖g_T z‖ ≤ M * Real.exp (-T * z.re) / (-z.re))
    (h_strip : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → ‖g z‖ ≤ B) :
    let K : ℂ → ℂ := fun z => Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
    let F : ℂ → ℂ := fun z => (g z - g_T z) * Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
    ‖∫ x : ℝ in (0 : ℝ)..R, F (x + (y : ℝ) * Complex.I) / (x + (y : ℝ) * Complex.I)‖ ≤ 3 * M / R ∧
    ‖∫ x : ℝ in (-R)..(0 : ℝ), (g_T (x + (y : ℝ) * Complex.I) * K (x + (y : ℝ) * Complex.I)) /
      (x + (y : ℝ) * Complex.I)‖ ≤ 3 * M / R ∧
    ‖∫ x : ℝ in (-δ)..(0 : ℝ), (g (x + (y : ℝ) * Complex.I) * K (x + (y : ℝ) * Complex.I)) /
      (x + (y : ℝ) * Complex.I)‖ ≤ 3 * δ * B / R :=
by
  intro K F
  have hR_pos : 0 < R := by linarith
  have hR_nonneg : 0 ≤ R := by linarith
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_sq_pos : 0 < R ^ 2 := sq_pos_of_pos hR_pos
  have hRC_ne : (R : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hR_ne
  have hRC_sq_ne : (R : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 hRC_ne
  have hy_sq : y ^ 2 = R ^ 2 := by rw [← sq_abs y, hy]
  have hy_sq_C : (y : ℂ) ^ 2 = (R : ℂ) ^ 2 := by exact_mod_cast hy_sq
  have hz_re : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).re = x := by
    intro x
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
  have hz_im : ∀ x : ℝ, ((x : ℂ) + (y : ℂ) * Complex.I).im = y := by
    intro x
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re]
  have hTz_re : ∀ x : ℝ, ((T : ℂ) * ((x : ℂ) + (y : ℂ) * Complex.I)).re = T * x := by
    intro x
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have h_factor : ∀ x : ℝ,
      1 + ((x : ℂ) + (y : ℂ) * Complex.I) ^ 2 / (R : ℂ) ^ 2 =
        (x : ℂ) * ((x : ℂ) + 2 * (y : ℂ) * Complex.I) / (R : ℂ) ^ 2 := by
    intro x
    rw [one_add_div hRC_sq_ne]
    congr 1
    calc (R : ℂ) ^ 2 + ((x : ℂ) + (y : ℂ) * Complex.I) ^ 2
      _ = (y : ℂ) ^ 2 + ((x : ℂ) ^ 2 + 2 * (x : ℂ) * (y : ℂ) * Complex.I +
            (y : ℂ) ^ 2 * Complex.I ^ 2) := by
        rw [← hy_sq_C]; ring
      _ = (y : ℂ) ^ 2 + ((x : ℂ) ^ 2 + 2 * (x : ℂ) * (y : ℂ) * Complex.I +
            (y : ℂ) ^ 2 * (-1)) := by
        rw [Complex.I_sq]
      _ = (x : ℂ) * ((x : ℂ) + 2 * (y : ℂ) * Complex.I) := by ring
  have hK_div_norm : ∀ x : ℝ, |x| ≤ R →
      ‖K ((x : ℂ) + (y : ℂ) * Complex.I) / ((x : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        3 * |x| * Real.exp (T * x) / R ^ 2 := by
    intro x hx_abs
    set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
    have hz_norm : R ≤ ‖z‖ := by
      have h_im := Complex.abs_im_le_norm z
      rw [hz_im x, hy] at h_im
      exact h_im
    have h_lin_norm : ‖(x : ℂ) + 2 * (y : ℂ) * Complex.I‖ ≤ 3 * R := by
      calc ‖(x : ℂ) + 2 * (y : ℂ) * Complex.I‖
        _ ≤ ‖(x : ℂ)‖ + ‖2 * (y : ℂ) * Complex.I‖ := norm_add_le _ _
        _ = |x| + 2 * |y| := by
          rw [Complex.norm_real, Real.norm_eq_abs, norm_mul, norm_mul,
              Complex.norm_real, Real.norm_eq_abs, Complex.norm_I, mul_one]
          norm_num
        _ = |x| + 2 * R := by rw [hy]
        _ ≤ R + 2 * R := by linarith
        _ = 3 * R := by ring
    have h_poly_norm : ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 * |x| / R := by
      have h_eq : 1 + z ^ 2 / (R : ℂ) ^ 2 =
          (x : ℂ) * ((x : ℂ) + 2 * (y : ℂ) * Complex.I) / (R : ℂ) ^ 2 := h_factor x
      rw [h_eq, norm_div, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR_pos]
      calc |x| * ‖(x : ℂ) + 2 * (y : ℂ) * Complex.I‖ / R ^ 2
        _ ≤ |x| * (3 * R) / R ^ 2 := by
          apply div_le_div_of_nonneg_right _ (le_of_lt hR_sq_pos)
          exact mul_le_mul_of_nonneg_left h_lin_norm (abs_nonneg x)
        _ = 3 * |x| / R := by
          field_simp [hR_ne]
    have h_exp_norm : ‖Complex.exp ((T : ℂ) * z)‖ = Real.exp (T * x) := by
      rw [Complex.norm_exp, hTz_re x]
    have hK_norm : ‖K z‖ ≤ 3 * |x| * Real.exp (T * x) / R := by
      dsimp [K]
      rw [norm_mul, h_exp_norm]
      calc Real.exp (T * x) * ‖1 + z ^ 2 / (R : ℂ) ^ 2‖
        _ ≤ Real.exp (T * x) * (3 * |x| / R) :=
          mul_le_mul_of_nonneg_left h_poly_norm (Real.exp_nonneg _)
        _ = 3 * |x| * Real.exp (T * x) / R := by ring
    rw [norm_div]
    calc ‖K z‖ / ‖z‖
      _ ≤ ‖K z‖ / R := div_le_div_of_nonneg_left (norm_nonneg _) hR_pos hz_norm
      _ ≤ (3 * |x| * Real.exp (T * x) / R) / R :=
        div_le_div_of_nonneg_right hK_norm hR_nonneg
      _ = 3 * |x| * Real.exp (T * x) / R ^ 2 := by ring
  refine ⟨?_, ?_, ?_⟩
  · have h_int : ‖∫ x : ℝ in (0 : ℝ)..R, F (x + (y : ℝ) * Complex.I) / (x + (y : ℝ) * Complex.I)‖ ≤
        (3 * M / R ^ 2) * |R - 0| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hR_nonneg] at hx
      have hx_pos : 0 < x := hx.1
      have hx_le : x ≤ R := hx.2
      have hx_ne : x ≠ 0 := ne_of_gt hx_pos
      have hx_abs : |x| = x := abs_of_pos hx_pos
      have hx_abs_le : |x| ≤ R := by rw [hx_abs]; exact hx_le
      set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
      have hz_re_pos : 0 < z.re := by rw [hz_re x]; exact hx_pos
      have h_g_bound : ‖g z - g_T z‖ ≤ M * Real.exp (-T * x) / x := by
        have h := h_right z hz_re_pos
        rw [hz_re x] at h
        exact h
      have h_K_bound : ‖K z / z‖ ≤ 3 * x * Real.exp (T * x) / R ^ 2 := by
        have h := hK_div_norm x hx_abs_le
        rw [hx_abs] at h
        exact h
      have hF_eq : F z / z = (g z - g_T z) * (K z / z) := by
        dsimp [F, K]
        ring
      change ‖F z / z‖ ≤ 3 * M / R ^ 2
      rw [hF_eq, norm_mul]
      have h_exp_cancel : Real.exp (-T * x) * Real.exp (T * x) = 1 := by
        rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
      calc ‖g z - g_T z‖ * ‖K z / z‖
        _ ≤ (M * Real.exp (-T * x) / x) * (3 * x * Real.exp (T * x) / R ^ 2) :=
          mul_le_mul h_g_bound h_K_bound (norm_nonneg _) (by positivity)
        _ = (3 * M / R ^ 2) * (Real.exp (-T * x) * Real.exp (T * x)) * (x / x) := by ring
        _ = (3 * M / R ^ 2) * 1 * 1 := by rw [h_exp_cancel, div_self hx_ne]
        _ = 3 * M / R ^ 2 := by ring
    calc ‖∫ x : ℝ in (0 : ℝ)..R, F (x + (y : ℝ) * Complex.I) / (x + (y : ℝ) * Complex.I)‖
      _ ≤ (3 * M / R ^ 2) * |R - 0| := h_int
      _ = (3 * M / R ^ 2) * R := by rw [sub_zero, abs_of_pos hR_pos]
      _ = 3 * M / R := by field_simp [hR_ne]
  · have h_negR_le : -R ≤ 0 := by linarith
    have h_int : ‖∫ x : ℝ in (-R)..(0 : ℝ),
        (g_T (x + (y : ℝ) * Complex.I) * K (x + (y : ℝ) * Complex.I)) /
          (x + (y : ℝ) * Complex.I)‖ ≤ (3 * M / R ^ 2) * |0 - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le h_negR_le] at hx
      have hx_gt : -R < x := hx.1
      have hx_le : x ≤ 0 := hx.2
      set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
      change ‖(g_T z * K z) / z‖ ≤ 3 * M / R ^ 2
      rcases eq_or_lt_of_le hx_le with rfl | hx_neg
      · have hK0 : K z = 0 := by
          dsimp only [K, z]
          rw [h_factor 0]
          simp
        rw [hK0, mul_zero, zero_div, norm_zero]
        positivity
      · have h_negx_pos : 0 < -x := neg_pos.mpr hx_neg
        have h_negx_ne : -x ≠ 0 := ne_of_gt h_negx_pos
        have hx_abs : |x| = -x := abs_of_neg hx_neg
        have hx_abs_le : |x| ≤ R := by rw [hx_abs]; linarith
        have hz_re_neg : z.re < 0 := by rw [hz_re x]; exact hx_neg
        have h_gT_bound : ‖g_T z‖ ≤ M * Real.exp (-T * x) / (-x) := by
          have h := h_left z hz_re_neg
          rw [hz_re x] at h
          exact h
        have h_K_bound : ‖K z / z‖ ≤ 3 * (-x) * Real.exp (T * x) / R ^ 2 := by
          have h := hK_div_norm x hx_abs_le
          rw [hx_abs] at h
          exact h
        have h_exp_cancel : Real.exp (-T * x) * Real.exp (T * x) = 1 := by
          rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
        rw [mul_div_assoc, norm_mul]
        calc ‖g_T z‖ * ‖K z / z‖
          _ ≤ (M * Real.exp (-T * x) / (-x)) * (3 * (-x) * Real.exp (T * x) / R ^ 2) :=
            mul_le_mul h_gT_bound h_K_bound (norm_nonneg _) (by positivity)
          _ = (3 * M / R ^ 2) * (Real.exp (-T * x) * Real.exp (T * x)) * ((-x) / (-x)) := by ring
          _ = (3 * M / R ^ 2) * 1 * 1 := by rw [h_exp_cancel, div_self h_negx_ne]
          _ = 3 * M / R ^ 2 := by ring
    calc ‖∫ x : ℝ in (-R)..(0 : ℝ),
          (g_T (x + (y : ℝ) * Complex.I) * K (x + (y : ℝ) * Complex.I)) /
            (x + (y : ℝ) * Complex.I)‖
      _ ≤ (3 * M / R ^ 2) * |0 - (-R)| := h_int
      _ = (3 * M / R ^ 2) * R := by rw [zero_sub, neg_neg, abs_of_pos hR_pos]
      _ = 3 * M / R := by field_simp [hR_ne]
  · have h_negδ_le : -δ ≤ 0 := by linarith
    have h_int : ‖∫ x : ℝ in (-δ)..(0 : ℝ),
        (g (x + (y : ℝ) * Complex.I) * K (x + (y : ℝ) * Complex.I)) /
          (x + (y : ℝ) * Complex.I)‖ ≤ (3 * B / R) * |0 - (-δ)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le h_negδ_le] at hx
      have hx_gt : -δ < x := hx.1
      have hx_le : x ≤ 0 := hx.2
      have hx_ge : -δ ≤ x := le_of_lt hx_gt
      have hx_abs : |x| = -x := abs_of_nonpos hx_le
      have hx_abs_le_δ : |x| ≤ δ := by rw [hx_abs]; linarith
      have hx_abs_le_R : |x| ≤ R := le_trans hx_abs_le_δ hδR
      set z : ℂ := (x : ℂ) + (y : ℂ) * Complex.I
      have h_g_bound : ‖g z‖ ≤ B := by
        apply h_strip z
        · rw [hz_re x]; exact hx_ge
        · rw [hz_re x]; exact hx_le
        · rw [hz_im x, hy]
      have hTx_nonpos : T * x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos (le_of_lt hT) hx_le
      have hexp_le_one : Real.exp (T * x) ≤ 1 := Real.exp_le_one_iff.mpr hTx_nonpos
      have h_x_exp : |x| * Real.exp (T * x) ≤ R := by
        calc |x| * Real.exp (T * x)
          _ ≤ R * 1 := mul_le_mul hx_abs_le_R hexp_le_one (Real.exp_nonneg _) (by linarith)
          _ = R := mul_one R
      have h_K_bound : ‖K z / z‖ ≤ 3 / R := by
        calc ‖K z / z‖
          _ ≤ 3 * |x| * Real.exp (T * x) / R ^ 2 := hK_div_norm x hx_abs_le_R
          _ = 3 * (|x| * Real.exp (T * x)) / R ^ 2 := by ring
          _ ≤ 3 * R / R ^ 2 := by
            apply div_le_div_of_nonneg_right _ (le_of_lt hR_sq_pos)
            linarith
          _ = 3 / R := by field_simp [hR_ne]
      change ‖(g z * K z) / z‖ ≤ 3 * B / R
      rw [mul_div_assoc, norm_mul]
      calc ‖g z‖ * ‖K z / z‖
        _ ≤ B * (3 / R) := mul_le_mul h_g_bound h_K_bound (norm_nonneg _) hB
        _ = 3 * B / R := by ring
    calc ‖∫ x : ℝ in (-δ)..(0 : ℝ),
          (g (x + (y : ℝ) * Complex.I) * K (x + (y : ℝ) * Complex.I)) /
            (x + (y : ℝ) * Complex.I)‖
      _ ≤ (3 * B / R) * |0 - (-δ)| := h_int
      _ = (3 * B / R) * δ := by rw [zero_sub, neg_neg, abs_of_pos hδ]
      _ = 3 * δ * B / R := by ring

theorem newman_vert_segments_norm_le {g g_T : ℂ → ℂ} {T R M B δ : ℝ}
    (hT : 0 < T) (hR : 1 ≤ R) (hM : 0 < M) (hB : 0 ≤ B) (hδ : 0 < δ) (hδR : δ ≤ R)
    (h_right : ∀ z : ℂ, 0 < z.re → ‖g z - g_T z‖ ≤ M * Real.exp (-T * z.re) / z.re)
    (h_left : ∀ z : ℂ, z.re < 0 → ‖g_T z‖ ≤ M * Real.exp (-T * z.re) / (-z.re))
    (h_strip : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → ‖g z‖ ≤ B) :
    let K : ℂ → ℂ := fun z => Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
    let F : ℂ → ℂ := fun z => (g z - g_T z) * Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
    ‖∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I)‖ ≤ 6 * M / R ∧
    ‖∫ y : ℝ in (-R)..R, (g_T ((-R : ℝ) + y * Complex.I) * K ((-R : ℝ) + y * Complex.I)) /
      ((-R : ℝ) + y * Complex.I)‖ ≤ 6 * M / R ∧
    ‖∫ y : ℝ in (-R)..R, (g ((-δ : ℝ) + y * Complex.I) * K ((-δ : ℝ) + y * Complex.I)) /
      ((-δ : ℝ) + y * Complex.I)‖ ≤ 6 * R * B * Real.exp (-T * δ) / δ :=
by
  intro K F
  have hR_pos : 0 < R := by linarith
  have hR_nonneg : 0 ≤ R := by linarith
  have hR_ne : R ≠ 0 := ne_of_gt hR_pos
  have hR_sq_pos : 0 < R ^ 2 := sq_pos_of_pos hR_pos
  have h_negR_le_R : -R ≤ R := by linarith
  have h_len : |R - (-R)| = 2 * R := by
    have h2R : R - (-R) = 2 * R := by ring
    rw [h2R, abs_of_pos (by linarith)]
  have hz_re : ∀ σ y : ℝ, ((σ : ℂ) + (y : ℂ) * Complex.I).re = σ := by
    intro σ y
    simp [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im,
      Complex.I_im]
  have hz_im : ∀ σ y : ℝ, ((σ : ℂ) + (y : ℂ) * Complex.I).im = y := by
    intro σ y
    simp [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im, Complex.ofReal_re,
      Complex.I_re]
  have hTz_re : ∀ σ y : ℝ, ((T : ℂ) * ((σ : ℂ) + (y : ℂ) * Complex.I)).re = T * σ := by
    intro σ y
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
      Complex.I_im]
  have hK_div_norm : ∀ σ y : ℝ, 0 < |σ| → |σ| ≤ R → |y| ≤ R →
      ‖K ((σ : ℂ) + (y : ℂ) * Complex.I) / ((σ : ℂ) + (y : ℂ) * Complex.I)‖ ≤
        3 * Real.exp (T * σ) / |σ| := by
    intro σ y hσ_pos hσ_le hy_le
    set z : ℂ := (σ : ℂ) + (y : ℂ) * Complex.I
    have hσ_sq : σ ^ 2 ≤ R ^ 2 := by
      have h1 : |σ| ^ 2 = σ ^ 2 := sq_abs σ
      nlinarith [abs_nonneg σ]
    have hy_sq : y ^ 2 ≤ R ^ 2 := by
      have h1 : |y| ^ 2 = y ^ 2 := sq_abs y
      nlinarith [abs_nonneg y]
    have hz_sq_norm : ‖z‖ ^ 2 ≤ 2 * R ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply, hz_re σ y, hz_im σ y]
      nlinarith
    have h_poly_norm : ‖1 + z ^ 2 / (R : ℂ) ^ 2‖ ≤ 3 := by
      calc ‖1 + z ^ 2 / (R : ℂ) ^ 2‖
        _ ≤ ‖(1 : ℂ)‖ + ‖z ^ 2 / (R : ℂ) ^ 2‖ := norm_add_le _ _
        _ = 1 + ‖z‖ ^ 2 / R ^ 2 := by
          rw [norm_one, norm_div, norm_pow, norm_pow, Complex.norm_real, Real.norm_eq_abs,
              abs_of_pos hR_pos]
        _ ≤ 1 + (2 * R ^ 2) / R ^ 2 := by
          have h_div : ‖z‖ ^ 2 / R ^ 2 ≤ (2 * R ^ 2) / R ^ 2 :=
            div_le_div_of_nonneg_right hz_sq_norm (le_of_lt hR_sq_pos)
          linarith
        _ = 3 := by
          field_simp [hR_ne]
          ring
    have hz_norm_ge : |σ| ≤ ‖z‖ := by
      have h_re := Complex.abs_re_le_norm z
      rw [hz_re σ y] at h_re
      exact h_re
    have h_exp_norm : ‖Complex.exp ((T : ℂ) * z)‖ = Real.exp (T * σ) := by
      rw [Complex.norm_exp, hTz_re σ y]
    have hK_norm : ‖K z‖ ≤ 3 * Real.exp (T * σ) := by
      dsimp [K]
      rw [norm_mul, h_exp_norm]
      calc Real.exp (T * σ) * ‖1 + z ^ 2 / (R : ℂ) ^ 2‖
        _ ≤ Real.exp (T * σ) * 3 :=
          mul_le_mul_of_nonneg_left h_poly_norm (Real.exp_nonneg _)
        _ = 3 * Real.exp (T * σ) := by ring
    rw [norm_div]
    calc ‖K z‖ / ‖z‖
      _ ≤ ‖K z‖ / |σ| := div_le_div_of_nonneg_left (norm_nonneg _) hσ_pos hz_norm_ge
      _ ≤ (3 * Real.exp (T * σ)) / |σ| :=
        div_le_div_of_nonneg_right hK_norm (le_of_lt hσ_pos)
  have hy_abs : ∀ y ∈ Set.uIoc (-R) R, |y| ≤ R := by
    intro y hy
    rw [Set.uIoc_of_le h_negR_le_R] at hy
    exact abs_le.mpr ⟨by linarith [hy.1], hy.2⟩
  refine ⟨?_, ?_, ?_⟩
  · have h_int : ‖∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I)‖ ≤
        (3 * M / R ^ 2) * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hy_le : |y| ≤ R := hy_abs y hy
      set z : ℂ := (R : ℂ) + (y : ℂ) * Complex.I
      have hz_re_pos : 0 < z.re := by rw [hz_re R y]; exact hR_pos
      have h_g_bound : ‖g z - g_T z‖ ≤ M * Real.exp (-T * R) / R := by
        have h := h_right z hz_re_pos
        rw [hz_re R y] at h
        exact h
      have hR_abs : |R| = R := abs_of_pos hR_pos
      have h_K_bound : ‖K z / z‖ ≤ 3 * Real.exp (T * R) / R := by
        have h := hK_div_norm R y (by rw [hR_abs]; exact hR_pos) (by rw [hR_abs]) hy_le
        rw [hR_abs] at h
        exact h
      have hF_eq : F z / z = (g z - g_T z) * (K z / z) := by
        dsimp [F, K]
        ring
      change ‖F z / z‖ ≤ 3 * M / R ^ 2
      rw [hF_eq, norm_mul]
      have h_exp_cancel : Real.exp (-T * R) * Real.exp (T * R) = 1 := by
        rw [← Real.exp_add, neg_mul, neg_add_cancel, Real.exp_zero]
      calc ‖g z - g_T z‖ * ‖K z / z‖
        _ ≤ (M * Real.exp (-T * R) / R) * (3 * Real.exp (T * R) / R) :=
          mul_le_mul h_g_bound h_K_bound (norm_nonneg _) (by positivity)
        _ = (3 * M / R ^ 2) * (Real.exp (-T * R) * Real.exp (T * R)) := by ring
        _ = (3 * M / R ^ 2) * 1 := by rw [h_exp_cancel]
        _ = 3 * M / R ^ 2 := by ring
    calc ‖∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I)‖
      _ ≤ (3 * M / R ^ 2) * |R - (-R)| := h_int
      _ = (3 * M / R ^ 2) * (2 * R) := by rw [h_len]
      _ = 6 * M / R := by field_simp [hR_ne]; ring
  · have h_int : ‖∫ y : ℝ in (-R)..R,
        (g_T ((-R : ℝ) + y * Complex.I) * K ((-R : ℝ) + y * Complex.I)) /
          ((-R : ℝ) + y * Complex.I)‖ ≤ (3 * M / R ^ 2) * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hy_le : |y| ≤ R := hy_abs y hy
      set z : ℂ := ((-R : ℝ) : ℂ) + (y : ℂ) * Complex.I
      have hz_re_neg : z.re < 0 := by rw [hz_re (-R) y]; linarith
      have h_gT_bound : ‖g_T z‖ ≤ M * Real.exp (T * R) / R := by
        have h := h_left z hz_re_neg
        rw [hz_re (-R) y] at h
        have h_eq : M * Real.exp (-T * -R) / -(-R) = M * Real.exp (T * R) / R := by
          have h1 : -T * -R = T * R := by ring
          have h2 : -(-R) = R := by ring
          rw [h1, h2]
        rw [← h_eq]
        exact h
      have h_negR_abs : |-R| = R := by rw [abs_neg, abs_of_pos hR_pos]
      have h_K_bound : ‖K z / z‖ ≤ 3 * Real.exp (-T * R) / R := by
        have h := hK_div_norm (-R) y (by rw [h_negR_abs]; exact hR_pos) (by rw [h_negR_abs]) hy_le
        rw [h_negR_abs] at h
        have h_eq : 3 * Real.exp (T * -R) / R = 3 * Real.exp (-T * R) / R := by
          congr 2; ring
        rw [← h_eq]
        exact h
      have h_exp_cancel : Real.exp (T * R) * Real.exp (-T * R) = 1 := by
        rw [← Real.exp_add, neg_mul, add_neg_cancel, Real.exp_zero]
      change ‖(g_T z * K z) / z‖ ≤ 3 * M / R ^ 2
      rw [mul_div_assoc, norm_mul]
      calc ‖g_T z‖ * ‖K z / z‖
        _ ≤ (M * Real.exp (T * R) / R) * (3 * Real.exp (-T * R) / R) :=
          mul_le_mul h_gT_bound h_K_bound (norm_nonneg _) (by positivity)
        _ = (3 * M / R ^ 2) * (Real.exp (T * R) * Real.exp (-T * R)) := by ring
        _ = (3 * M / R ^ 2) * 1 := by rw [h_exp_cancel]
        _ = 3 * M / R ^ 2 := by ring
    calc ‖∫ y : ℝ in (-R)..R,
          (g_T ((-R : ℝ) + y * Complex.I) * K ((-R : ℝ) + y * Complex.I)) /
            ((-R : ℝ) + y * Complex.I)‖
      _ ≤ (3 * M / R ^ 2) * |R - (-R)| := h_int
      _ = (3 * M / R ^ 2) * (2 * R) := by rw [h_len]
      _ = 6 * M / R := by field_simp [hR_ne]; ring
  · have h_int : ‖∫ y : ℝ in (-R)..R,
        (g ((-δ : ℝ) + y * Complex.I) * K ((-δ : ℝ) + y * Complex.I)) /
          ((-δ : ℝ) + y * Complex.I)‖ ≤ (3 * B * Real.exp (-T * δ) / δ) * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y hy
      have hy_le : |y| ≤ R := hy_abs y hy
      set z : ℂ := ((-δ : ℝ) : ℂ) + (y : ℂ) * Complex.I
      have h_g_bound : ‖g z‖ ≤ B := by
        apply h_strip z
        · rw [hz_re (-δ) y]
        · rw [hz_re (-δ) y]; linarith
        · rw [hz_im (-δ) y]; exact hy_le
      have h_negδ_abs : |-δ| = δ := by rw [abs_neg, abs_of_pos hδ]
      have h_K_bound : ‖K z / z‖ ≤ 3 * Real.exp (-T * δ) / δ := by
        have h := hK_div_norm (-δ) y (by rw [h_negδ_abs]; exact hδ)
          (by rw [h_negδ_abs]; exact hδR) hy_le
        rw [h_negδ_abs] at h
        have h_eq : 3 * Real.exp (T * -δ) / δ = 3 * Real.exp (-T * δ) / δ := by
          congr 2; ring
        rw [← h_eq]
        exact h
      change ‖(g z * K z) / z‖ ≤ 3 * B * Real.exp (-T * δ) / δ
      rw [mul_div_assoc, norm_mul]
      calc ‖g z‖ * ‖K z / z‖
        _ ≤ B * (3 * Real.exp (-T * δ) / δ) :=
          mul_le_mul h_g_bound h_K_bound (norm_nonneg _) hB
        _ = 3 * B * Real.exp (-T * δ) / δ := by ring
    calc ‖∫ y : ℝ in (-R)..R,
          (g ((-δ : ℝ) + y * Complex.I) * K ((-δ : ℝ) + y * Complex.I)) /
            ((-δ : ℝ) + y * Complex.I)‖
      _ ≤ (3 * B * Real.exp (-T * δ) / δ) * |R - (-R)| := h_int
      _ = (3 * B * Real.exp (-T * δ) / δ) * (2 * R) := by rw [h_len]
      _ = 6 * R * B * Real.exp (-T * δ) / δ := by ring

theorem newman_rect_contour_bound_of_laplace_bounds {g g_T : ℂ → ℂ} {T R M B δ : ℝ}
    (hT : 0 < T) (hR : 1 ≤ R) (hM : 0 < M) (hB : 0 ≤ B) (hδ : 0 < δ) (hδR : δ ≤ R)
    (hg_diff : ∀ z : ℂ, -δ ≤ z.re → |z.im| ≤ R → DifferentiableAt ℂ g z)
    (hgT_diff : Differentiable ℂ g_T)
    (h_right : ∀ z : ℂ, 0 < z.re → ‖g z - g_T z‖ ≤ M * Real.exp (-T * z.re) / z.re)
    (h_left : ∀ z : ℂ, z.re < 0 → ‖g_T z‖ ≤ M * Real.exp (-T * z.re) / (-z.re))
    (h_strip : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → ‖g z‖ ≤ B) :
    let F : ℂ → ℂ := fun z => (g z - g_T z) * Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
    ‖((∫ x : ℝ in (-δ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
      (∫ x : ℝ in (-δ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
      Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
      Complex.I * (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I))‖ ≤
      (24 * M + 6 * δ * B) / R + 6 * R * B * Real.exp (-T * δ) / δ :=
by
  intro F
  set K : ℂ → ℂ := fun z => Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
  set H_g : ℂ → ℂ := fun z => g z * K z
  set H_T : ℂ → ℂ := fun z => g_T z * K z
  have hK_diff : Differentiable ℂ K := by
    intro z
    have hexp : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((T : ℂ) * w)) z :=
      (differentiableAt_id.const_mul (T : ℂ)).cexp
    have hpoly : DifferentiableAt ℂ (fun w : ℂ => 1 + w ^ 2 / (R : ℂ) ^ 2) z :=
      (differentiableAt_const (1 : ℂ)).add ((differentiableAt_id.pow 2).div_const ((R : ℂ) ^ 2))
    exact hexp.mul hpoly
  have hHg_diff : ∀ z : ℂ, -δ ≤ z.re → |z.im| ≤ R → DifferentiableAt ℂ H_g z := by
    intro z hz_re hz_im
    exact (hg_diff z hz_re hz_im).mul (hK_diff z)
  have hHT_diff : Differentiable ℂ H_T := by
    intro z
    exact (hgT_diff z).mul (hK_diff z)
  set I_right : ℂ :=
    (∫ x : ℝ in (0 : ℝ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
    (∫ x : ℝ in (0 : ℝ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
    Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))
  set I_left : ℂ :=
    (∫ x : ℝ in (-R)..(0 : ℝ), H_T (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
    (∫ x : ℝ in (-R)..(0 : ℝ), H_T (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in (-R)..R, H_T ((-R : ℝ) + y * Complex.I) / ((-R : ℝ) + y * Complex.I))
  set I_strip : ℂ :=
    (∫ x : ℝ in (-δ)..(0 : ℝ), H_g (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
    (∫ x : ℝ in (-δ)..(0 : ℝ), H_g (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) -
    Complex.I * (∫ y : ℝ in (-R)..R, H_g ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I))
  have h_decomp :
      ((∫ x : ℝ in (-δ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
        (∫ x : ℝ in (-δ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
        Complex.I * (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I)) =
      (I_right - I_left) + I_strip := by
    have hF_eq : F = fun z => H_g z - H_T z := by
      ext z
      dsimp [F, H_g, H_T, K]
      ring
    dsimp [I_right, I_left, I_strip]
    rw [hF_eq]
    exact newman_rect_contour_shift_decomp hR hδ hδR hHg_diff hHT_diff
  have hy_neg : |-R| = R := by
    rw [abs_neg, abs_of_pos (by linarith)]
  have hy_pos : |R| = R := abs_of_pos (by linarith)
  obtain ⟨h_horiz_bot_right, h_horiz_bot_left, h_horiz_bot_strip⟩ :=
    newman_horiz_segments_norm_le hT hR hM hB hδ hδR hy_neg h_right h_left h_strip
  obtain ⟨h_horiz_top_right, h_horiz_top_left, h_horiz_top_strip⟩ :=
    newman_horiz_segments_norm_le hT hR hM hB hδ hδR hy_pos h_right h_left h_strip
  obtain ⟨h_vert_right, h_vert_left, h_vert_strip⟩ :=
    newman_vert_segments_norm_le hT hR hM hB hδ hδR h_right h_left h_strip
  have h_tri_add : ∀ A B C : ℂ, ‖A - B + Complex.I * C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    intro A B C
    calc ‖A - B + Complex.I * C‖
      _ ≤ ‖A - B‖ + ‖Complex.I * C‖ := norm_add_le _ _
      _ ≤ (‖A‖ + ‖B‖) + ‖Complex.I * C‖ := add_le_add (norm_sub_le A B) (le_refl _)
      _ = ‖A‖ + ‖B‖ + ‖C‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h_tri_sub : ∀ A B C : ℂ, ‖A - B - Complex.I * C‖ ≤ ‖A‖ + ‖B‖ + ‖C‖ := by
    intro A B C
    calc ‖A - B - Complex.I * C‖
      _ ≤ ‖A - B‖ + ‖Complex.I * C‖ := norm_sub_le _ _
      _ ≤ (‖A‖ + ‖B‖) + ‖Complex.I * C‖ := add_le_add (norm_sub_le A B) (le_refl _)
      _ = ‖A‖ + ‖B‖ + ‖C‖ := by rw [norm_mul, Complex.norm_I, one_mul]
  have h_tri_outer : ∀ X Y Z : ℂ, ‖(X - Y) + Z‖ ≤ ‖X‖ + ‖Y‖ + ‖Z‖ := by
    intro X Y Z
    calc ‖(X - Y) + Z‖
      _ ≤ ‖X - Y‖ + ‖Z‖ := norm_add_le _ _
      _ ≤ (‖X‖ + ‖Y‖) + ‖Z‖ := add_le_add (norm_sub_le X Y) (le_refl _)
  have h_I_right : ‖I_right‖ ≤ 3 * M / R + 3 * M / R + 6 * M / R :=
    le_trans (h_tri_add _ _ _)
      (add_le_add (add_le_add h_horiz_bot_right h_horiz_top_right) h_vert_right)
  have h_I_left : ‖I_left‖ ≤ 3 * M / R + 3 * M / R + 6 * M / R :=
    le_trans (h_tri_sub _ _ _)
      (add_le_add (add_le_add h_horiz_bot_left h_horiz_top_left) h_vert_left)
  have h_I_strip : ‖I_strip‖ ≤ 3 * δ * B / R + 3 * δ * B / R + 6 * R * B * Real.exp (-T * δ) / δ :=
    le_trans (h_tri_sub _ _ _)
      (add_le_add (add_le_add h_horiz_bot_strip h_horiz_top_strip) h_vert_strip)
  calc ‖((∫ x : ℝ in (-δ)..R, F (x + (-R : ℝ) * Complex.I) / (x + (-R : ℝ) * Complex.I)) -
        (∫ x : ℝ in (-δ)..R, F (x + (R : ℝ) * Complex.I) / (x + (R : ℝ) * Complex.I)) +
        Complex.I * (∫ y : ℝ in (-R)..R, F ((R : ℝ) + y * Complex.I) / ((R : ℝ) + y * Complex.I))) -
        Complex.I * (∫ y : ℝ in (-R)..R, F ((-δ : ℝ) + y * Complex.I) / ((-δ : ℝ) + y * Complex.I))‖
    _ = ‖(I_right - I_left) + I_strip‖ := by rw [h_decomp]
    _ ≤ ‖I_right‖ + ‖I_left‖ + ‖I_strip‖ := h_tri_outer I_right I_left I_strip
    _ ≤ (3 * M / R + 3 * M / R + 6 * M / R) +
        (3 * M / R + 3 * M / R + 6 * M / R) +
        (3 * δ * B / R + 3 * δ * B / R + 6 * R * B * Real.exp (-T * δ) / δ) :=
      add_le_add (add_le_add h_I_right h_I_left) h_I_strip
    _ = (24 * M + 6 * δ * B) / R + 6 * R * B * Real.exp (-T * δ) / δ := by ring

theorem tauberian_parameter_choice_bound {M a C : ℝ} (hM : 0 < M) (ha : 0 < a) (hC : 0 < C) :
    ∃ (C1 T0 : ℝ), 0 < C1 ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        ∃ R : ℝ, 1 ≤ R ∧
          let δ := a * (R + 2) ^ (-5 : ℝ)
          0 < δ ∧ δ ≤ R ∧
            (24 * M + 6 * a * C) / R + 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) / δ ≤
              C1 * (Real.log T / T) ^ (1 / 5 : ℝ) :=
by
  obtain ⟨c, hc_def⟩ : ∃ c : ℝ, c = (a / 3) ^ (1 / 5 : ℝ) := ⟨_, rfl⟩
  have ha3_pos : 0 < a / 3 := div_pos ha zero_lt_three
  have hc_pos : 0 < c := hc_def ▸ Real.rpow_pos_of_pos ha3_pos (1 / 5 : ℝ)
  have hc5 : c ^ 5 = a / 3 := by
    rw [← Real.rpow_natCast c 5, hc_def, ← Real.rpow_mul (le_of_lt ha3_pos)]
    have h5 : (1 / 5 : ℝ) * ((5 : ℕ) : ℝ) = 1 := by norm_num
    rw [h5, Real.rpow_one]
  obtain ⟨C1, hC1_def⟩ : ∃ C1 : ℝ, C1 = 3 * (24 * M + 6 * a * C) / c + 2 * a * C * c / 3 := ⟨_, rfl⟩
  obtain ⟨T0, hT0_def⟩ : ∃ T0 : ℝ, T0 = 2 + Real.exp 1 + 64 ^ 2 + (1458 / a) ^ 2 := ⟨_, rfl⟩
  have hC1_pos : 0 < C1 := by
    rw [hC1_def]
    positivity
  have hexp1_pos : 0 < Real.exp 1 := Real.exp_pos 1
  have hsq_nonneg : 0 ≤ (1458 / a) ^ 2 := sq_nonneg (1458 / a)
  have hT0_ge : 2 ≤ T0 := by linarith only [hT0_def, hexp1_pos, hsq_nonneg]
  refine ⟨C1, T0, hC1_pos, hT0_ge, fun T hT => ?_⟩
  have hT_pos : 0 < T := by linarith only [hT0_ge, hT]
  have hT_ge_exp1 : Real.exp 1 ≤ T := by linarith only [hT0_def, hT, hsq_nonneg]
  have hT_ge_64sq : (64 : ℝ) ^ 2 ≤ T := by linarith only [hT0_def, hT, hexp1_pos, hsq_nonneg]
  have hT_ge_1458sq : (1458 / a) ^ 2 ≤ T := by linarith only [hT0_def, hT, hexp1_pos]
  have hlogT_ge_1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log hexp1_pos hT_ge_exp1
  have hlogT_pos : 0 < Real.log T := lt_of_lt_of_le zero_lt_one hlogT_ge_1
  have hsqrtT_pos : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT_pos
  have hsqrtT_sq : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt (le_of_lt hT_pos)
  have hlogT_le_sqrt : Real.log T ≤ 2 * Real.sqrt T := by
    have hlog_mul : Real.log T = Real.log (Real.sqrt T) + Real.log (Real.sqrt T) := by
      conv_lhs => rw [← hsqrtT_sq]
      exact Real.log_mul (ne_of_gt hsqrtT_pos) (ne_of_gt hsqrtT_pos)
    have hlog_sub : Real.log (Real.sqrt T) ≤ Real.sqrt T - 1 :=
      Real.log_le_sub_one_of_pos hsqrtT_pos
    linarith only [hlog_mul, hlog_sub]
  have hsqrtT_ge_64 : 64 ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hT_ge_64sq
  have hsqrtT_ge_1458 : 1458 / a ≤ Real.sqrt T := Real.le_sqrt_of_sq_le hT_ge_1458sq
  have ha_sqrtT : 1458 ≤ Real.sqrt T * a := (div_le_iff₀ ha).mp hsqrtT_ge_1458
  have h32_logT : 32 * Real.log T ≤ T := by
    calc 32 * Real.log T
      _ ≤ 32 * (2 * Real.sqrt T) := by linarith only [hlogT_le_sqrt]
      _ = 64 * Real.sqrt T := by ring
      _ ≤ Real.sqrt T * Real.sqrt T :=
        mul_le_mul_of_nonneg_right hsqrtT_ge_64 (le_of_lt hsqrtT_pos)
      _ = T := hsqrtT_sq
  have h_ratio_le_32 : Real.log T / T ≤ 1 / 32 := by
    rw [div_le_iff₀ hT_pos]
    linarith only [h32_logT]
  have h_ratio_le_half : Real.log T / T ≤ (1 / 2 : ℝ) ^ 5 := by
    have h_pow : (1 / 32 : ℝ) = (1 / 2 : ℝ) ^ 5 := by norm_num
    rw [← h_pow]
    exact h_ratio_le_32
  have h729_logT : 729 * Real.log T ≤ a * T := by
    calc 729 * Real.log T
      _ ≤ 729 * (2 * Real.sqrt T) := by linarith only [hlogT_le_sqrt]
      _ = 1458 * Real.sqrt T := by ring
      _ ≤ (Real.sqrt T * a) * Real.sqrt T :=
        mul_le_mul_of_nonneg_right ha_sqrtT (le_of_lt hsqrtT_pos)
      _ = a * (Real.sqrt T * Real.sqrt T) := by ring
      _ = a * T := by rw [hsqrtT_sq]
  have h_ratio_le_c3 : Real.log T / T ≤ (c / 3) ^ 5 := by
    have hc3_5 : (c / 3) ^ 5 = a / 729 := by
      calc (c / 3) ^ 5 = c ^ 5 / 3 ^ 5 := div_pow c 3 5
        _ = (a / 3) / 3 ^ 5 := by rw [hc5]
        _ = a / 729 := by ring
    rw [hc3_5, div_le_iff₀ hT_pos]
    linarith only [h729_logT]
  obtain ⟨u, hu_def⟩ : ∃ u : ℝ, u = (Real.log T / T) ^ (1 / 5 : ℝ) := ⟨_, rfl⟩
  have h_ratio_pos : 0 < Real.log T / T := div_pos hlogT_pos hT_pos
  have hu_pos : 0 < u := hu_def ▸ Real.rpow_pos_of_pos h_ratio_pos (1 / 5 : ℝ)
  have hu5 : u ^ 5 = Real.log T / T := by
    rw [← Real.rpow_natCast u 5, hu_def, ← Real.rpow_mul (le_of_lt h_ratio_pos)]
    have h5 : (1 / 5 : ℝ) * ((5 : ℕ) : ℝ) = 1 := by norm_num
    rw [h5, Real.rpow_one]
  have hu_le_half : u ≤ 1 / 2 := by
    have h5 : u ^ 5 ≤ (1 / 2 : ℝ) ^ 5 := by
      rw [hu5]
      exact h_ratio_le_half
    exact (pow_le_pow_iff_left₀ (le_of_lt hu_pos) (by norm_num) (by decide : 5 ≠ 0)).mp h5
  have hu_le_c3 : u ≤ c / 3 := by
    have h5 : u ^ 5 ≤ (c / 3) ^ 5 := by
      rw [hu5]
      exact h_ratio_le_c3
    exact (pow_le_pow_iff_left₀ (le_of_lt hu_pos) (le_of_lt (div_pos hc_pos zero_lt_three)) (by decide : 5 ≠ 0)).mp h5
  obtain ⟨R, hR_def⟩ : ∃ R : ℝ, R = c / u - 2 := ⟨_, rfl⟩
  have hR2_eq : R + 2 = c / u := by linarith only [hR_def]
  have hR2_mul_u : (R + 2) * u = c := by
    rw [hR2_eq, div_mul_cancel₀ c (ne_of_gt hu_pos)]
  have h3_le_cu : 3 ≤ c / u := by
    rw [le_div_iff₀ hu_pos]
    linarith only [hu_le_c3]
  have hR1 : 1 ≤ R := by linarith only [hR2_eq, h3_le_cu]
  have hR_pos : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hR2_pos : 0 < R + 2 := by linarith only [hR_pos]
  have hR2_u_expand : (R + 2) * u = R * u + 2 * u := by ring
  have h_inv_R : (24 * M + 6 * a * C) / R ≤ (3 * (24 * M + 6 * a * C) / c) * u := by
    have hu_le_Ru : 1 * u ≤ R * u := mul_le_mul_of_nonneg_right hR1 (le_of_lt hu_pos)
    have h_3uR_eq : 3 * u * R = 3 * (R * u) := by ring
    have hc_le_3uR : 1 * c ≤ 3 * u * R := by
      linarith only [hR2_mul_u, hR2_u_expand, hu_le_Ru, h_3uR_eq]
    have h_1R : 1 / R ≤ 3 * u / c := (div_le_div_iff₀ hR_pos hc_pos).mpr hc_le_3uR
    have h_num_pos : 0 ≤ 24 * M + 6 * a * C := by positivity
    calc (24 * M + 6 * a * C) / R
      _ = (24 * M + 6 * a * C) * (1 / R) := by ring
      _ ≤ (24 * M + 6 * a * C) * (3 * u / c) :=
        mul_le_mul_of_nonneg_left h_1R h_num_pos
      _ = (3 * (24 * M + 6 * a * C) / c) * u := by ring
  refine ⟨R, hR1, ?_⟩
  dsimp only
  obtain ⟨δ, hδ_def⟩ : ∃ δ : ℝ, δ = a * (R + 2) ^ (-5 : ℝ) := ⟨_, rfl⟩
  rw [← hδ_def]
  have hR2_u5 : (R + 2) ^ (5 : ℝ) * (3 * u ^ 5) = a := by
    calc (R + 2) ^ (5 : ℝ) * (3 * u ^ 5)
      _ = (R + 2) ^ (5 : ℕ) * (3 * u ^ 5) := by rw [Real.rpow_ofNat]
      _ = 3 * ((R + 2) * u) ^ 5 := by ring
      _ = 3 * c ^ 5 := by rw [hR2_mul_u]
      _ = 3 * (a / 3) := by rw [hc5]
      _ = a := by ring
  have hR2_rpow5_pos : 0 < (R + 2) ^ (5 : ℝ) := Real.rpow_pos_of_pos hR2_pos 5
  have hδ_eq : δ = 3 * u ^ 5 := by
    calc δ = a * (R + 2) ^ (-5 : ℝ) := hδ_def
      _ = a * ((R + 2) ^ (5 : ℝ))⁻¹ := by rw [Real.rpow_neg (le_of_lt hR2_pos) 5]
      _ = ((R + 2) ^ (5 : ℝ) * (3 * u ^ 5)) * ((R + 2) ^ (5 : ℝ))⁻¹ := by
        conv_lhs => enter [1]; rw [← hR2_u5]
      _ = 3 * u ^ 5 * ((R + 2) ^ (5 : ℝ) * ((R + 2) ^ (5 : ℝ))⁻¹) := by ring
      _ = 3 * u ^ 5 * 1 := by rw [mul_inv_cancel₀ (ne_of_gt hR2_rpow5_pos)]
      _ = 3 * u ^ 5 := mul_one _
  have hu5_pos : 0 < u ^ 5 := pow_pos hu_pos 5
  have hδ_pos : 0 < δ := by linarith only [hδ_eq, hu5_pos]
  have hδ_le_R : δ ≤ R := by
    have hδ_le_1 : δ ≤ 1 := by linarith only [hδ_eq, hu5, h_ratio_le_32]
    linarith only [hδ_le_1, hR1]
  have hexp_eq : Real.exp (-T * δ) = 1 / T ^ 3 := by
    have hTδ : -T * δ = -(((3 : ℕ) : ℝ) * Real.log T) := by
      rw [hδ_eq, hu5]
      push_cast
      calc -T * (3 * (Real.log T / T))
        _ = -(3 * (T * (Real.log T / T))) := by ring
        _ = -(3 * Real.log T) := by rw [mul_div_cancel₀ _ (ne_of_gt hT_pos)]
    rw [hTδ, Real.exp_neg, Real.exp_nat_mul, Real.exp_log hT_pos, one_div]
  have hexp_le_u15 : Real.exp (-T * δ) ≤ u ^ 15 := by
    have hlog2 : 1 * 1 ≤ Real.log T * Real.log T :=
      mul_le_mul hlogT_ge_1 hlogT_ge_1 zero_le_one (le_of_lt hlogT_pos)
    have hlog3 : 1 ≤ (Real.log T) ^ 3 := by
      calc (1 : ℝ) = 1 * (1 * 1) := by ring
        _ ≤ Real.log T * (Real.log T * Real.log T) :=
          mul_le_mul hlogT_ge_1 hlog2 (by norm_num) (le_of_lt hlogT_pos)
        _ = (Real.log T) ^ 3 := by ring
    have hT3_pos : 0 < T ^ 3 := pow_pos hT_pos 3
    calc Real.exp (-T * δ)
      _ = 1 / T ^ 3 := hexp_eq
      _ ≤ (Real.log T) ^ 3 / T ^ 3 := div_le_div_of_nonneg_right hlog3 (le_of_lt hT3_pos)
      _ = (Real.log T / T) ^ 3 := (div_pow (Real.log T) T 3).symm
      _ = (u ^ 5) ^ 3 := by rw [← hu5]
      _ = u ^ 15 := by ring
  have hexp_pos : 0 < Real.exp (-T * δ) := Real.exp_pos (-T * δ)
  have hRu_le_c : R * u ≤ c := by linarith only [hR2_mul_u, hR2_u_expand, hu_pos]
  have hu1 : u ≤ 1 := by linarith only [hu_le_half]
  have hu2_le_1 : u * u ≤ 1 * 1 :=
    mul_le_mul hu1 hu1 (le_of_lt hu_pos) zero_le_one
  have hu3_le_1 : u ^ 3 ≤ 1 := by
    calc u ^ 3 = u * (u * u) := by ring
      _ ≤ 1 * (1 * 1) := mul_le_mul hu1 hu2_le_1 (by positivity) zero_le_one
      _ = 1 := by ring
  have h_term2 : 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) / δ ≤
      (2 * a * C * c / 3) * u := by
    rw [div_le_iff₀ hδ_pos]
    have huδ_pos : 0 < u * δ := mul_pos hu_pos hδ_pos
    have h6aC_nonneg : 0 ≤ 6 * a * C := by positivity
    have h6aCc_u12_nonneg : 0 ≤ 6 * a * C * c * u ^ 12 := by positivity
    have h_mul_ineq :
        6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) * (u * δ) ≤
          (2 * a * C * c / 3) * u * δ * (u * δ) := by
      calc 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) * (u * δ)
        _ = 6 * C * ((R + 2) ^ (5 : ℝ) * (3 * u ^ 5)) * ((R * u) * Real.exp (-T * δ)) := by
          rw [hδ_eq]; ring
        _ = 6 * a * C * ((R * u) * Real.exp (-T * δ)) := by
          rw [hR2_u5]; ring
        _ ≤ 6 * a * C * (c * u ^ 15) :=
          mul_le_mul_of_nonneg_left
            (mul_le_mul hRu_le_c hexp_le_u15 (le_of_lt hexp_pos) (le_of_lt hc_pos))
            h6aC_nonneg
        _ = 6 * a * C * c * u ^ 12 * u ^ 3 := by ring
        _ ≤ 6 * a * C * c * u ^ 12 * 1 :=
          mul_le_mul_of_nonneg_left hu3_le_1 h6aCc_u12_nonneg
        _ = (2 * a * C * c / 3) * u * δ * (u * δ) := by
          rw [hδ_eq]; ring
    calc 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ)
      _ = 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) * ((u * δ) / (u * δ)) := by
        rw [div_self (ne_of_gt huδ_pos), mul_one]
      _ = (6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) * (u * δ)) / (u * δ) := by ring
      _ ≤ ((2 * a * C * c / 3) * u * δ * (u * δ)) / (u * δ) :=
        div_le_div_of_nonneg_right h_mul_ineq (le_of_lt huδ_pos)
      _ = (2 * a * C * c / 3) * u * δ * ((u * δ) / (u * δ)) := by ring
      _ = (2 * a * C * c / 3) * u * δ := by
        rw [div_self (ne_of_gt huδ_pos), mul_one]
  refine ⟨hδ_pos, hδ_le_R, ?_⟩
  calc (24 * M + 6 * a * C) / R + 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) / δ
    _ ≤ (3 * (24 * M + 6 * a * C) / c) * u + (2 * a * C * c / 3) * u :=
      add_le_add h_inv_R h_term2
    _ = C1 * (Real.log T / T) ^ (1 / 5 : ℝ) := by
      rw [hC1_def, ← hu_def]
      ring

theorem quantitative_newman_tauberian_poly {f : ℝ → ℝ} {M : ℝ} {g : ℂ → ℂ} {a C : ℝ}
    (hf_meas : Measurable f) (hM : 0 < M) (hf_bound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ M)
    (ha : 0 < a) (hC : 0 < C)
    (hg_laplace : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)))
    (hg_diff : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, -a * (R + 2) ^ (-5 : ℝ) ≤ z.re → |z.im| ≤ R →
      DifferentiableAt ℂ g z)
    (hg_bound : ∀ R : ℝ, 1 ≤ R → ∀ z : ℂ, -a * (R + 2) ^ (-5 : ℝ) ≤ z.re → z.re ≤ 0 → |z.im| ≤ R →
      ‖g z‖ ≤ C * (R + 2) ^ (5 : ℝ)) :
    ∃ (C1 T0 : ℝ), 0 < C1 ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        |(∫ t in (0 : ℝ)..T, f t) - (g 0).re| ≤ C1 * (Real.log T / T) ^ (1 / 5 : ℝ) :=
by
  obtain ⟨C1, T0, hC1, hT0, h_param⟩ := tauberian_parameter_choice_bound hM ha hC
  refine ⟨C1, T0, hC1, hT0, fun T hT => ?_⟩
  have hT_pos : 0 < T := by linarith
  have hT_nonneg : 0 ≤ T := le_of_lt hT_pos
  obtain ⟨R, hR1, hδ_pos, hδ_le_R, h_bound⟩ := h_param T hT
  set δ : ℝ := a * (R + 2) ^ (-5 : ℝ)
  set B : ℝ := C * (R + 2) ^ (5 : ℝ)
  have hR2_pos : 0 < R + 2 := by linarith
  have hB_nonneg : 0 ≤ B := mul_nonneg (le_of_lt hC) (Real.rpow_nonneg (le_of_lt hR2_pos) _)
  obtain ⟨hgT_diff, h_right, h_left⟩ :=
    truncated_laplace_holomorphic_and_bounds hf_meas hM hf_bound hg_laplace T hT_nonneg
  set g_T : ℂ → ℂ := fun z => ∫ t in (0 : ℝ)..T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))
  set F : ℂ → ℂ := fun z => (g z - g_T z) * Complex.exp ((T : ℂ) * z) * (1 + z ^ 2 / (R : ℂ) ^ 2)
  have hF_diff : DifferentiableOn ℂ F (Complex.reProdIm (Set.uIcc (-δ) R) (Set.uIcc (-R) R)) := by
    intro z hz
    have h_uIcc_re : Set.uIcc (-δ) R = Set.Icc (-δ) R := Set.uIcc_of_le (by linarith)
    have h_uIcc_im : Set.uIcc (-R) R = Set.Icc (-R) R := Set.uIcc_of_le (by linarith)
    have hz_re : z.re ∈ Set.Icc (-δ) R := by
      rw [← h_uIcc_re]
      exact hz.1
    have hz_im : z.im ∈ Set.Icc (-R) R := by
      rw [← h_uIcc_im]
      exact hz.2
    have hz_re_ge : -a * (R + 2) ^ (-5 : ℝ) ≤ z.re := by
      have : -δ ≤ z.re := hz_re.1
      dsimp [δ] at this
      linarith
    have hz_im_abs : |z.im| ≤ R := abs_le.mpr ⟨hz_im.1, hz_im.2⟩
    have hg_at : DifferentiableAt ℂ g z := hg_diff R hR1 z hz_re_ge hz_im_abs
    have hgT_at : DifferentiableAt ℂ g_T z := hgT_diff z
    have hexp_at : DifferentiableAt ℂ (fun w : ℂ => Complex.exp ((T : ℂ) * w)) z :=
      (differentiableAt_id.const_mul (T : ℂ)).cexp
    have hpoly_at : DifferentiableAt ℂ (fun w : ℂ => 1 + w ^ 2 / (R : ℂ) ^ 2) z :=
      (differentiableAt_const (1 : ℂ)).add ((differentiableAt_id.pow 2).div_const ((R : ℂ) ^ 2))
    exact (((hg_at.sub hgT_at).mul hexp_at).mul hpoly_at).differentiableWithinAt
  have h_cauchy := rect_cauchy_norm_at_zero_le hδ_pos hδ_le_R hF_diff
  have hg_diff_strip : ∀ z : ℂ, -δ ≤ z.re → |z.im| ≤ R → DifferentiableAt ℂ g z := by
    intro z hz_re hz_im
    apply hg_diff R hR1 z _ hz_im
    dsimp [δ] at hz_re
    linarith
  have h_strip : ∀ z : ℂ, -δ ≤ z.re → z.re ≤ 0 → |z.im| ≤ R → ‖g z‖ ≤ B := by
    intro z hz_re hz_re0 hz_im
    apply hg_bound R hR1 z _ hz_re0 hz_im
    dsimp [δ] at hz_re
    linarith
  have h_contour := newman_rect_contour_bound_of_laplace_bounds
    hT_pos hR1 hM hB_nonneg hδ_pos hδ_le_R hg_diff_strip hgT_diff h_right h_left h_strip
  have h_δB : δ * B = a * C := by
    dsimp [δ, B]
    have h_rpow : (R + 2) ^ (-5 : ℝ) * (R + 2) ^ (5 : ℝ) = 1 := by
      rw [← Real.rpow_add hR2_pos]
      norm_num
    calc a * (R + 2) ^ (-5 : ℝ) * (C * (R + 2) ^ (5 : ℝ))
      _ = a * C * ((R + 2) ^ (-5 : ℝ) * (R + 2) ^ (5 : ℝ)) := by ring
      _ = a * C * 1 := by rw [h_rpow]
      _ = a * C := mul_one _
  have h_F0_norm : ‖F 0‖ ≤ C1 * (Real.log T / T) ^ (1 / 5 : ℝ) := by
    calc ‖F 0‖
      _ ≤ _ := h_cauchy
      _ ≤ (24 * M + 6 * δ * B) / R + 6 * R * B * Real.exp (-T * δ) / δ := h_contour
      _ = (24 * M + 6 * a * C) / R + 6 * R * (C * (R + 2) ^ (5 : ℝ)) * Real.exp (-T * δ) / δ := by
        have h6 : 6 * δ * B = 6 * a * C := by linarith [h_δB]
        rw [h6]
      _ ≤ C1 * (Real.log T / T) ^ (1 / 5 : ℝ) := h_bound
  have hgT0 : g_T 0 = ((∫ t in (0 : ℝ)..T, f t : ℝ) : ℂ) := by
    dsimp [g_T]
    have h_integrand : (fun t : ℝ => (f t : ℂ) * Complex.exp (-0 * (t : ℂ))) =
        (fun t : ℝ => (f t : ℂ)) := by
      ext t
      simp
    rw [h_integrand, intervalIntegral.integral_ofReal]
  have hF0 : F 0 = g 0 - ((∫ t in (0 : ℝ)..T, f t : ℝ) : ℂ) := by
    dsimp [F]
    rw [hgT0]
    simp
  have h_lhs_le : |(∫ t in (0 : ℝ)..T, f t) - (g 0).re| ≤ ‖F 0‖ := by
    have h_re : (F 0).re = (g 0).re - (∫ t in (0 : ℝ)..T, f t) := by
      rw [hF0, Complex.sub_re, Complex.ofReal_re]
    have h_abs : |(∫ t in (0 : ℝ)..T, f t) - (g 0).re| = |(F 0).re| := by
      rw [h_re, abs_sub_comm]
    rw [h_abs]
    exact Complex.abs_re_le_norm (F 0)
  exact le_trans h_lhs_le h_F0_norm

theorem psi_rel_error_of_tauberian_integral (h_taub : ∃ (c C1 T0 : ℝ), 0 < C1 ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        |(∫ t in (0 : ℝ)..T, (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤
          C1 * (Real.log T / T) ^ (1 / 5 : ℝ)) :
    ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ 0.004 * x / Real.log (Real.log x) :=
by
  have psi_exp_pointwise_shift_bounds : ∀ {T η : ℝ}, 0 ≤ η → η ≤ 1 / 2 →
      (∀ t ∈ Set.Icc T (T + η),
        (Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1) - 6 * η ≤
          Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1) ∧
      (∀ t ∈ Set.Icc (T - η) T,
        Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1 ≤
          (Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1) + 12 * η) := by
    intro T η hη0 hη1
    set A := Real.exp (-T) * Chebyshev.psi (Real.exp T)
    have h_psi_nonneg : 0 ≤ Chebyshev.psi (Real.exp T) := Chebyshev.psi_nonneg (Real.exp T)
    have hA_nonneg : 0 ≤ A := mul_nonneg (le_of_lt (Real.exp_pos (-T))) h_psi_nonneg
    have h_psi_upper : Chebyshev.psi (Real.exp T) ≤ (Real.log 4 + 4) * Real.exp T :=
      Chebyshev.psi_le_const_mul_self (le_of_lt (Real.exp_pos T))
    have h_log4 : Real.log 4 ≤ 2 := by
      have h4 : (4 : ℝ) = 2 * 2 := by norm_num
      rw [h4, Real.log_mul (by norm_num) (by norm_num)]
      linarith [Real.log_two_lt_d9]
    have h_exp_cancel : Real.exp (-T) * Real.exp T = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hA_le : A ≤ 6 := by
      calc A = Real.exp (-T) * Chebyshev.psi (Real.exp T) := rfl
        _ ≤ Real.exp (-T) * ((Real.log 4 + 4) * Real.exp T) :=
          mul_le_mul_of_nonneg_left h_psi_upper (le_of_lt (Real.exp_pos (-T)))
        _ = (Real.log 4 + 4) * (Real.exp (-T) * Real.exp T) := by ring
        _ = Real.log 4 + 4 := by rw [h_exp_cancel, mul_one]
        _ ≤ 6 := by linarith
    have h_exp_low : 1 - η ≤ Real.exp (-η) := by linarith [Real.add_one_le_exp (-η)]
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rcases ht with ⟨ht1, ht2⟩
      have h_psi_mono : Chebyshev.psi (Real.exp T) ≤ Chebyshev.psi (Real.exp t) :=
        Chebyshev.psi_mono (Real.exp_le_exp.mpr ht1)
      have h_exp_mono : Real.exp (-η) * Real.exp (-T) ≤ Real.exp (-t) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h_prod : Real.exp (-η) * A ≤ Real.exp (-t) * Chebyshev.psi (Real.exp t) := by
        calc Real.exp (-η) * A
          _ = (Real.exp (-η) * Real.exp (-T)) * Chebyshev.psi (Real.exp T) := by ring
          _ ≤ Real.exp (-t) * Chebyshev.psi (Real.exp t) :=
            mul_le_mul h_exp_mono h_psi_mono h_psi_nonneg (le_of_lt (Real.exp_pos (-t)))
      nlinarith
    · rcases ht with ⟨ht1, ht2⟩
      have h_psi_t_nonneg : 0 ≤ Chebyshev.psi (Real.exp t) := Chebyshev.psi_nonneg (Real.exp t)
      have h_psi_mono : Chebyshev.psi (Real.exp t) ≤ Chebyshev.psi (Real.exp T) :=
        Chebyshev.psi_mono (Real.exp_le_exp.mpr ht2)
      have h_exp_mono : Real.exp (-t) ≤ Real.exp η * Real.exp (-T) := by
        rw [← Real.exp_add]
        exact Real.exp_le_exp.mpr (by linarith)
      have h_prod : Real.exp (-t) * Chebyshev.psi (Real.exp t) ≤ Real.exp η * A := by
        calc Real.exp (-t) * Chebyshev.psi (Real.exp t)
          _ ≤ (Real.exp η * Real.exp (-T)) * Chebyshev.psi (Real.exp T) :=
            mul_le_mul h_exp_mono h_psi_mono h_psi_t_nonneg (by positivity)
          _ = Real.exp η * A := by ring
      have h_exp_eta_cancel : Real.exp η * Real.exp (-η) = 1 := by
        rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
      have h_exp_high : Real.exp η ≤ 1 + 2 * η := by
        nlinarith [Real.exp_pos η]
      nlinarith

  have psi_tauberian_diff_squeeze : ∀ {T c E η : ℝ}, 0 < η →
      (∀ t ∈ Set.Icc T (T + η),
        (Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1) - 6 * η ≤
          Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1) →
      (∀ t ∈ Set.Icc (T - η) T,
        Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1 ≤
          (Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1) + 12 * η) →
      |(∫ t in (0 : ℝ)..T, (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤ E →
      |(∫ t in (0 : ℝ)..(T + η), (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤ E →
      |(∫ t in (0 : ℝ)..(T - η), (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤ E →
      |Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1| ≤ 2 * E / η + 12 * η := by
    intro T c E η hη0 h_low h_high hI_T hI_plus hI_minus
    let f : ℝ → ℝ := fun t => Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1
    have hf_int : ∀ a b : ℝ, IntervalIntegrable f MeasureTheory.volume a b := fun a b =>
      (((Chebyshev.psi_mono.comp Real.exp_monotone).intervalIntegrable.continuousOn_mul
        (Real.continuous_exp.comp continuous_neg).continuousOn).sub intervalIntegrable_const)
    have h_adj_plus : (∫ t in (0 : ℝ)..T, f t) + (∫ t in T..(T + η), f t) =
        ∫ t in (0 : ℝ)..(T + η), f t :=
      intervalIntegral.integral_add_adjacent_intervals (hf_int 0 T) (hf_int T (T + η))
    have h_adj_minus : (∫ t in (0 : ℝ)..(T - η), f t) + (∫ t in (T - η)..T, f t) =
        ∫ t in (0 : ℝ)..T, f t :=
      intervalIntegral.integral_add_adjacent_intervals (hf_int 0 (T - η)) (hf_int (T - η) T)
    have hI_T_bounds := abs_le.mp hI_T
    have hI_plus_bounds := abs_le.mp hI_plus
    have hI_minus_bounds := abs_le.mp hI_minus
    have h_int_plus_le : (∫ t in T..(T + η), f t) ≤ 2 * E := by
      linarith [h_adj_plus, hI_T_bounds.1, hI_plus_bounds.2]
    have h_int_minus_ge : -2 * E ≤ (∫ t in (T - η)..T, f t) := by
      linarith [h_adj_minus, hI_T_bounds.1, hI_minus_bounds.2]
    have h_mono_plus : (∫ t in T..(T + η), (f T - 6 * η)) ≤ ∫ t in T..(T + η), f t :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hf_int T (T + η)) h_low
    rw [intervalIntegral.integral_const, smul_eq_mul] at h_mono_plus
    have h_mono_minus : (∫ t in (T - η)..T, f t) ≤ ∫ t in (T - η)..T, (f T + 12 * η) :=
      intervalIntegral.integral_mono_on (by linarith) (hf_int (T - η) T)
        intervalIntegrable_const h_high
    rw [intervalIntegral.integral_const, smul_eq_mul] at h_mono_minus
    have h_div_cancel : 2 * E / η * η = 2 * E := div_mul_cancel₀ (2 * E) (ne_of_gt hη0)
    rw [abs_le]
    constructor <;> nlinarith

  obtain ⟨c, C1, T0, hC1, hT0, h_taub_T⟩ := h_taub
  set M := max C1 1
  have hM_ge1 : 1 ≤ M := le_max_right C1 1
  have hC1_le_M : C1 ≤ M := le_max_left C1 1
  have hM_pos : 0 < M := by linarith
  set c0 := 1 / (2 * 10000000 * M)
  have hc0_pos : 0 < c0 := by positivity
  have h_littleo : (fun T : ℝ => Real.log T) =o[atTop] (fun T : ℝ => T ^ (1 / 11 : ℝ)) :=
    isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 11)
  have h_ev_T : ∀ᶠ T : ℝ in atTop,
      ‖Real.log T‖ ≤ c0 * ‖T ^ (1 / 11 : ℝ)‖ ∧ max (max (T0 + 1) 4) (Real.exp 2) ≤ T :=
    (h_littleo.bound hc0_pos).and (eventually_ge_atTop (max (max (T0 + 1) 4) (Real.exp 2)))
  have h_ev_x := (Real.tendsto_log_atTop.eventually h_ev_T).and (eventually_gt_atTop (1 : ℝ))
  filter_upwards [h_ev_x] with x ⟨⟨h_log_bound, hT_max⟩, hx1⟩
  have hx_pos : 0 < x := by linarith
  set T := Real.log x
  have hT_ge_T01 : T0 + 1 ≤ T :=
    le_trans (le_trans (le_max_left (T0 + 1) 4) (le_max_left _ (Real.exp 2))) hT_max
  have hT_ge4 : 4 ≤ T :=
    le_trans (le_trans (le_max_right (T0 + 1) 4) (le_max_left _ (Real.exp 2))) hT_max
  have hT_ge_exp2 : Real.exp 2 ≤ T := le_trans (le_max_right _ (Real.exp 2)) hT_max
  have hT_pos : 0 < T := by linarith
  have hlogT_ge2 : 2 ≤ Real.log T := by
    rw [← Real.log_exp 2]
    exact Real.log_le_log (Real.exp_pos 2) hT_ge_exp2
  have hlogT_pos : 0 < Real.log T := by linarith
  set η := 1 / (10000 * Real.log T)
  set E := 1 / (10000000 * (Real.log T) ^ 2)
  have hη_pos : 0 < η := by positivity
  have hE_pos : 0 < E := by positivity
  have hη_le_half : η ≤ 1 / 2 := by
    dsimp [η]
    rw [div_le_iff₀ (by positivity)]
    linarith
  have hT_minus_ge_T0 : T0 ≤ T - η := by linarith
  rw [Real.norm_of_nonneg (le_of_lt hlogT_pos),
      Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hT_pos) _)] at h_log_bound
  have h_mul_c0 : 2 * 10000000 * M * Real.log T ≤ T ^ (1 / 11 : ℝ) := by
    have hc0_inv : 2 * 10000000 * M * c0 = 1 := by
      dsimp [c0]
      exact mul_one_div_cancel (by positivity)
    calc 2 * 10000000 * M * Real.log T
      _ ≤ 2 * 10000000 * M * (c0 * T ^ (1 / 11 : ℝ)) :=
        mul_le_mul_of_nonneg_left h_log_bound (by positivity)
      _ = (2 * 10000000 * M * c0) * T ^ (1 / 11 : ℝ) := by ring
      _ = T ^ (1 / 11 : ℝ) := by rw [hc0_inv, one_mul]
  have h_pow11 : (2 * 10000000 * M * Real.log T) ^ 11 ≤ T := by
    calc (2 * 10000000 * M * Real.log T) ^ 11
      _ ≤ (T ^ (1 / 11 : ℝ)) ^ 11 := pow_le_pow_left₀ (by positivity) h_mul_c0 11
      _ = T := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hT_pos)]
        norm_num
  have h_T_dom : 4 * (10000000 * C1) ^ 5 * (Real.log T) ^ 11 ≤ T := by
    have h_C1_M5 : (10000000 * C1) ^ 5 ≤ (10000000 * M) ^ 5 :=
      pow_le_pow_left₀ (by positivity) (by linarith) 5
    have h_M5_M11 : (10000000 * M) ^ 5 ≤ (10000000 * M) ^ 11 :=
      pow_le_pow_right₀ (by linarith) (by omega)
    have h_C1_M11 : (10000000 * C1) ^ 5 ≤ (10000000 * M) ^ 11 := le_trans h_C1_M5 h_M5_M11
    have h_4_211 : (4 : ℝ) ≤ 2 ^ 11 := by norm_num
    have h_prod_pow : 4 * (10000000 * C1) ^ 5 ≤ 2 ^ 11 * (10000000 * M) ^ 11 :=
      mul_le_mul h_4_211 h_C1_M11 (by positivity) (by positivity)
    calc 4 * (10000000 * C1) ^ 5 * (Real.log T) ^ 11
      _ ≤ (2 ^ 11 * (10000000 * M) ^ 11) * (Real.log T) ^ 11 :=
        mul_le_mul_of_nonneg_right h_prod_pow (by positivity)
      _ = (2 * 10000000 * M * Real.log T) ^ 11 := by ring
      _ ≤ T := h_pow11
  have h_u_bound : ∀ u ∈ Set.Icc (T - η) (T + η),
      C1 * (Real.log u / u) ^ (1 / 5 : ℝ) ≤ E := by
    intro u ⟨hu_low, hu_high⟩
    have hu_ge_half : T / 2 ≤ u := by linarith
    have hu_pos : 0 < u := by linarith
    have hu_ge1 : 1 ≤ u := by linarith
    have hu_le_sq : u ≤ T ^ 2 := by nlinarith
    have hlogu_nonneg : 0 ≤ Real.log u := Real.log_nonneg hu_ge1
    have hlogu_le : Real.log u ≤ 2 * Real.log T := by
      calc Real.log u ≤ Real.log (T ^ 2) := Real.log_le_log hu_pos hu_le_sq
        _ = 2 * Real.log T := by rw [Real.log_pow]; ring
    have h_quot_u : Real.log u / u ≤ 4 * Real.log T / T := by
      rw [div_le_div_iff₀ hu_pos hT_pos]
      nlinarith
    have h_quot_E5 : 4 * Real.log T / T ≤ (E / C1) ^ 5 := by
      have h_E_C1 : (E / C1) ^ 5 = 1 / ((10000000 * C1) ^ 5 * (Real.log T) ^ 10) := by
        dsimp [E]
        ring
      rw [h_E_C1, div_le_div_iff₀ hT_pos (by positivity)]
      calc 4 * Real.log T * ((10000000 * C1) ^ 5 * (Real.log T) ^ 10)
        _ = 4 * (10000000 * C1) ^ 5 * (Real.log T) ^ 11 := by ring
        _ ≤ 1 * T := by linarith [h_T_dom]
    have h_u_E5 : Real.log u / u ≤ (E / C1) ^ 5 := le_trans h_quot_u h_quot_E5
    have h_rpow : (Real.log u / u) ^ (1 / 5 : ℝ) ≤ E / C1 := by
      calc (Real.log u / u) ^ (1 / 5 : ℝ)
        _ ≤ ((E / C1) ^ (5 : ℕ)) ^ (1 / 5 : ℝ) :=
          Real.rpow_le_rpow (div_nonneg hlogu_nonneg (le_of_lt hu_pos)) h_u_E5 (by norm_num)
        _ = E / C1 := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
          norm_num
    calc C1 * (Real.log u / u) ^ (1 / 5 : ℝ)
      _ ≤ C1 * (E / C1) := mul_le_mul_of_nonneg_left h_rpow (le_of_lt hC1)
      _ = E := mul_div_cancel₀ E (ne_of_gt hC1)
  have hI_T : |(∫ t in (0 : ℝ)..T, (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤ E :=
    le_trans (h_taub_T T (by linarith)) (h_u_bound T ⟨by linarith, by linarith⟩)
  have hI_plus : |(∫ t in (0 : ℝ)..(T + η), (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤ E :=
    le_trans (h_taub_T (T + η) (by linarith)) (h_u_bound (T + η) ⟨by linarith, by linarith⟩)
  have hI_minus : |(∫ t in (0 : ℝ)..(T - η), (Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1)) - c| ≤ E :=
    le_trans (h_taub_T (T - η) hT_minus_ge_T0) (h_u_bound (T - η) ⟨by linarith, by linarith⟩)
  obtain ⟨h_low, h_high⟩ := psi_exp_pointwise_shift_bounds (le_of_lt hη_pos) hη_le_half
  have h_squeeze := psi_tauberian_diff_squeeze hη_pos h_low h_high hI_T hI_plus hI_minus
  have h_param_sum : 2 * E / η + 12 * η ≤ 0.004 / Real.log T := by
    have h_eq : 2 * E / η + 12 * η = 0.0032 / Real.log T := by
      dsimp [E, η]
      have hlog_ne : Real.log T ≠ 0 := ne_of_gt hlogT_pos
      field_simp
      ring
    rw [h_eq]
    exact div_le_div_of_nonneg_right (by norm_num) (le_of_lt hlogT_pos)
  have h_rel_T : |Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1| ≤ 0.004 / Real.log T :=
    le_trans h_squeeze h_param_sum
  have hexp_T : Real.exp T = x := Real.exp_log hx_pos
  have hexp_neg_T : Real.exp (-T) * x = 1 := by
    rw [← hexp_T, ← Real.exp_add, neg_add_cancel, Real.exp_zero]
  have h_factor : Chebyshev.psi x - x = x * (Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1) := by
    rw [hexp_T]
    calc Chebyshev.psi x - x
      _ = (Real.exp (-T) * x) * Chebyshev.psi x - x := by rw [hexp_neg_T, one_mul]
      _ = x * (Real.exp (-T) * Chebyshev.psi x - 1) := by ring
  rw [h_factor, abs_mul, abs_of_pos hx_pos]
  calc x * |Real.exp (-T) * Chebyshev.psi (Real.exp T) - 1|
    _ ≤ x * (0.004 / Real.log T) := mul_le_mul_of_nonneg_left h_rel_T (le_of_lt hx_pos)
    _ = 0.004 * x / Real.log (Real.log x) := by ring

theorem chebyshev_theta_rel_error_eventually : ∀ᶠ x : ℝ in atTop, |Chebyshev.theta x - x| ≤ 0.005 * x / Real.log (Real.log x) :=
by
  let f : ℝ → ℝ := fun t => Real.exp (-t) * Chebyshev.psi (Real.exp t) - 1
  have hf_meas : Measurable f :=
    ((Real.continuous_exp.comp continuous_neg).measurable.mul
      (Chebyshev.psi_mono.measurable.comp Real.continuous_exp.measurable)).sub measurable_const
  have hf_bound : ∀ t : ℝ, 0 ≤ t → |f t| ≤ Real.log 4 + 5 := by
    intro t _
    have h1 : 0 ≤ Chebyshev.psi (Real.exp t) := Chebyshev.psi_nonneg (Real.exp t)
    have h2 : Chebyshev.psi (Real.exp t) ≤ (Real.log 4 + 4) * Real.exp t :=
      Chebyshev.psi_le_const_mul_self (le_of_lt (Real.exp_pos t))
    have hexp : 0 < Real.exp (-t) := Real.exp_pos (-t)
    have hmul : Real.exp (-t) * Real.exp t = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have h_low : -1 ≤ f t := by dsimp [f]; nlinarith
    have h_high : f t ≤ Real.log 4 + 3 := by dsimp [f]; nlinarith
    have hlog4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    rw [abs_le]
    constructor <;> linarith
  have hM_pos : 0 < Real.log 4 + 5 := by
    have : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    linarith
  obtain ⟨g, a, C, ha, hC, hg_eq, hg_diff, hg_bound⟩ := zeta_log_deriv_sub_pole_analytic_bound
  have hg_laplace : ∀ z : ℂ, 0 < z.re →
      g z = ∫ t in Set.Ioi (0 : ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ)) := by
    intro z hz
    rw [hg_eq z hz, ← psi_laplace_eq_neg_zeta_log_deriv hz]
  obtain ⟨C1, T0, hC1, hT0, h_taub⟩ :=
    quantitative_newman_tauberian_poly hf_meas hM_pos hf_bound ha hC hg_laplace hg_diff hg_bound
  have h_psi : ∀ᶠ x : ℝ in atTop, |Chebyshev.psi x - x| ≤ 0.004 * x / Real.log (Real.log x) :=
    psi_rel_error_of_tauberian_integral ⟨(g 0).re, C1, T0, hC1, hT0, h_taub⟩
  have h_diff : ∀ᶠ x : ℝ in atTop,
      |Chebyshev.psi x - Chebyshev.theta x| ≤ 0.001 * x / Real.log (Real.log x) := by
    have h_log : (fun x : ℝ => Real.log x) =o[atTop] (fun x : ℝ => x ^ (1 / 4 : ℝ)) :=
      isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)
    have h_ev := h_log.bound (by norm_num : (0 : ℝ) < 1 / 50)
    filter_upwards [h_ev, eventually_ge_atTop (Real.exp (Real.exp 1))] with x hx hx_ge
    have hx1 : 1 ≤ x := by
      have h1 : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
      have h2 : 1 ≤ Real.exp (Real.exp 1) := Real.one_le_exp (by linarith)
      linarith
    have hx_pos : 0 < x := by linarith
    have hlog_ge : Real.exp 1 ≤ Real.log x := by
      rw [← Real.log_exp (Real.exp 1)]
      exact Real.log_le_log (Real.exp_pos _) hx_ge
    have hlog_pos : 0 < Real.log x := lt_of_lt_of_le (Real.exp_pos 1) hlog_ge
    have hloglog_ge : 1 ≤ Real.log (Real.log x) := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) hlog_ge
    have hloglog_pos : 0 < Real.log (Real.log x) := by linarith
    have hloglog_le : Real.log (Real.log x) ≤ Real.log x := by
      linarith [Real.log_le_self (le_of_lt hlog_pos)]
    rw [Real.norm_of_nonneg (le_of_lt hlog_pos),
        Real.norm_of_nonneg (Real.rpow_nonneg (le_of_lt hx_pos) _)] at hx
    have h_sq : (Real.log x) ^ 2 ≤ (1 / 2500 : ℝ) * Real.sqrt x := by
      calc (Real.log x) ^ 2
        _ ≤ (1 / 50 * x ^ (1 / 4 : ℝ)) ^ 2 := by
          nlinarith [hx, Real.rpow_nonneg (le_of_lt hx_pos) (1 / 4 : ℝ)]
        _ = (1 / 2500 : ℝ) * (x ^ (1 / 4 : ℝ)) ^ 2 := by ring
        _ = (1 / 2500 : ℝ) * Real.sqrt x := by
          congr 1
          rw [← Real.rpow_natCast (x ^ (1 / 4 : ℝ)) 2, ← Real.rpow_mul (le_of_lt hx_pos),
              Real.sqrt_eq_rpow]
          norm_num
    have h_cheb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log hx1
    rw [le_div_iff₀ hloglog_pos]
    calc |Chebyshev.psi x - Chebyshev.theta x| * Real.log (Real.log x)
      _ ≤ (2 * Real.sqrt x * Real.log x) * Real.log x := by
        nlinarith [h_cheb, abs_nonneg (Chebyshev.psi x - Chebyshev.theta x), Real.sqrt_nonneg x]
      _ = 2 * Real.sqrt x * (Real.log x) ^ 2 := by ring
      _ ≤ 2 * Real.sqrt x * ((1 / 2500 : ℝ) * Real.sqrt x) := by
        nlinarith [h_sq, Real.sqrt_nonneg x]
      _ = 0.0008 * (Real.sqrt x * Real.sqrt x) := by ring
      _ = 0.0008 * x := by rw [Real.mul_self_sqrt (le_of_lt hx_pos)]
      _ ≤ 0.001 * x := by linarith
  filter_upwards [h_psi, h_diff] with x hx_psi hx_diff
  have h_tri : |Chebyshev.theta x - x| ≤
      |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := by
    have h_eq : Chebyshev.theta x - x =
        (Chebyshev.psi x - x) - (Chebyshev.psi x - Chebyshev.theta x) := by ring
    rw [h_eq]
    exact abs_sub (Chebyshev.psi x - x) (Chebyshev.psi x - Chebyshev.theta x)
  calc |Chebyshev.theta x - x|
    _ ≤ |Chebyshev.psi x - x| + |Chebyshev.psi x - Chebyshev.theta x| := h_tri
    _ ≤ 0.004 * x / Real.log (Real.log x) + 0.001 * x / Real.log (Real.log x) :=
      add_le_add hx_psi hx_diff
    _ = 0.005 * x / Real.log (Real.log x) := by ring

theorem chebyshev_prime_sum_le_of_theta_bound : ∀ {k r : ℕ}, 500 ≤ k → 1000 ≤ Real.log (k : ℝ) →
    Nat.sqrt k < r → 20 * r ≤ k →
    Real.log ((k : ℝ) / (r : ℝ)) ≤ 2 * Real.log (Real.log (k : ℝ)) →
    (∀ t : ℝ, Real.sqrt (k : ℝ) ≤ t → t ≤ (k : ℝ) →
      |Chebyshev.theta t - t| ≤ 0.005 * t / Real.log (Real.log t)) →
    let P_all := (Finset.Ioc r k).filter Nat.Prime
    let P_fold := P_all.filter (fun p => 51 * k ≤ 100 * p ∧ 100 * p ≤ 60 * k)
    Chebyshev.theta (k : ℝ) - (k.primeCounting : ℝ) * Real.log (r : ℝ) -
      Real.log 2 * (P_fold.card : ℝ) ≤
      (k : ℝ) / Real.log (k : ℝ) * (Real.log ((k : ℝ) / (r : ℝ)) - 1.03) :=
by
  intro k r hk500 hL1000 h_sqrt_r h20r h_log_kr htheta P_all P_fold
  have hx500_cast : (500 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk500
  have hr_pos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hr_lt_k_cast : (r : ℝ) < (k : ℝ) := by exact_mod_cast (show r < k by omega)
  set x : ℝ := (k : ℝ)
  set L : ℝ := Real.log x
  have hx500 : (500 : ℝ) ≤ x := hx500_cast
  have hr_lt_x : (r : ℝ) < x := hr_lt_k_cast
  have hx_pos : 0 < x := by linarith
  have hL_pos : 0 < L := by linarith
  have hs1 : Real.sqrt x ≤ 0.002 * x ∧
      Real.log L ≤ 0.007 * L ∧
      ∀ t : ℝ, Real.sqrt x ≤ t → 5 ≤ Real.log (Real.log t) := by
    have hsqrt_pos : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx_pos
    have hlog_sqrt : Real.log (Real.sqrt x) = L / 2 := Real.log_sqrt (le_of_lt hx_pos)
    have hsqrt_ge : 500 ≤ Real.sqrt x := by
      have h1 := Real.add_one_le_exp (Real.log (Real.sqrt x))
      rw [Real.exp_log hsqrt_pos, hlog_sqrt] at h1
      linarith
    have h_part1 : Real.sqrt x ≤ 0.002 * x := by
      have hmul : 500 * Real.sqrt x ≤ Real.sqrt x * Real.sqrt x :=
        mul_le_mul_of_nonneg_right hsqrt_ge (le_of_lt hsqrt_pos)
      rw [Real.mul_self_sqrt (le_of_lt hx_pos)] at hmul
      linarith
    have h_part2 : Real.log L ≤ 0.007 * L := by
      have hexp1 : (2.7 : ℝ) ≤ Real.exp 1 := by
        have := Real.exp_one_gt_d9
        linarith
      have hexp7 : (1000 : ℝ) ≤ Real.exp 7 := by
        have hpow : (2.7 : ℝ) ^ 7 ≤ (Real.exp 1) ^ 7 := pow_le_pow_left₀ (by norm_num) hexp1 7
        have h7 : (Real.exp 1) ^ 7 = Real.exp 7 := by
          rw [← Real.exp_nat_mul]
          norm_num
        linarith [show (1000 : ℝ) ≤ (2.7 : ℝ) ^ 7 by norm_num]
      have h1 := Real.add_one_le_exp (Real.log L - 7)
      rw [Real.exp_sub, Real.exp_log hL_pos] at h1
      have h2 : L / Real.exp 7 ≤ L / 1000 :=
        div_le_div_of_nonneg_left (le_of_lt hL_pos) (by norm_num) hexp7
      linarith
    have h_part3 : ∀ t : ℝ, Real.sqrt x ≤ t → 5 ≤ Real.log (Real.log t) := by
      intro t ht
      have hlog_t : 500 ≤ Real.log t := by
        have := Real.log_le_log hsqrt_pos ht
        linarith
      have hexp1 : Real.exp 1 ≤ 3 := by
        have := Real.exp_one_lt_d9
        linarith
      have hexp5 : Real.exp 5 ≤ 500 := by
        have hpow : (Real.exp 1) ^ 5 ≤ (3 : ℝ) ^ 5 :=
          pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) hexp1 5
        have h5 : (Real.exp 1) ^ 5 = Real.exp 5 := by
          rw [← Real.exp_nat_mul]
          norm_num
        linarith [show (3 : ℝ) ^ 5 ≤ (500 : ℝ) by norm_num]
      have hlog_ge := Real.log_le_log (Real.exp_pos 5) (le_trans hexp5 hlog_t)
      rwa [Real.log_exp] at hlog_ge
    exact ⟨h_part1, h_part2, h_part3⟩
  obtain ⟨hsqrt_le, hlogL_le, hloglog_ge5⟩ := hs1
  have htheta_lin : ∀ t : ℝ, Real.sqrt x ≤ t → t ≤ x → |Chebyshev.theta t - t| ≤ 0.001 * t := by
    intro t ht1 ht2
    have ht_nonneg : 0 ≤ t := le_trans (Real.sqrt_nonneg x) ht1
    have hll5 : 5 ≤ Real.log (Real.log t) := hloglog_ge5 t ht1
    have h1 := htheta t ht1 ht2
    have h2 : 0.005 * t / Real.log (Real.log t) ≤ 0.005 * t / 5 :=
      div_le_div_of_nonneg_left (by positivity) (by norm_num) hll5
    linarith
  have htheta_ge : ∀ t : ℝ, Real.sqrt x ≤ t → t ≤ x → 0.999 * t ≤ Chebyshev.theta t := by
    intro t ht1 ht2
    have h := abs_sub_le_iff.mp (htheta_lin t ht1 ht2)
    linarith
  set I : ℝ := ∫ t in (2 : ℝ)..x, Chebyshev.theta t / (t * (Real.log t) ^ 2)
  have h_int : 0.997 * x / L ^ 2 ≤ I := by
    have h2_le_sqrt : (2 : ℝ) ≤ Real.sqrt x := by
      have h4 : (4 : ℝ) ≤ x := by linarith
      have hsqrt4 : Real.sqrt 4 ≤ Real.sqrt x := Real.sqrt_le_sqrt h4
      have : Real.sqrt 4 = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
      linarith
    have hsqrt_le_x : Real.sqrt x ≤ x := by linarith
    set f : ℝ → ℝ := fun t => Chebyshev.theta t / (t * (Real.log t) ^ 2)
    have hint_all : MeasureTheory.IntegrableOn f (Set.Icc 2 x) :=
      Chebyshev.integrableOn_theta_div_id_mul_log_sq x
    have hint1 : IntervalIntegrable f MeasureTheory.volume 2 (Real.sqrt x) := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le h2_le_sqrt]
      exact hint_all.mono_set (Set.Icc_subset_Icc_right hsqrt_le_x)
    have hint2 : IntervalIntegrable f MeasureTheory.volume (Real.sqrt x) x := by
      rw [intervalIntegrable_iff_integrableOn_Icc_of_le hsqrt_le_x]
      exact hint_all.mono_set (Set.Icc_subset_Icc_left h2_le_sqrt)
    have hsplit := (intervalIntegral.integral_add_adjacent_intervals hint1 hint2).symm
    have hnonneg1 : 0 ≤ ∫ t in (2 : ℝ)..(Real.sqrt x), f t := by
      apply intervalIntegral.integral_nonneg h2_le_sqrt
      intro t ht
      apply div_nonneg (Chebyshev.theta_nonneg t)
      apply mul_nonneg
      · linarith [ht.1]
      · exact sq_nonneg (Real.log t)
    have hlower2 : (x - Real.sqrt x) * (0.999 / L ^ 2) ≤
        ∫ t in (Real.sqrt x)..x, f t := by
      have hmono : ∫ t in (Real.sqrt x)..x, (0.999 / L ^ 2) ≤
          ∫ t in (Real.sqrt x)..x, f t := by
        apply intervalIntegral.integral_mono_on hsqrt_le_x intervalIntegrable_const hint2
        intro t ht
        have ht_ge2 : (2 : ℝ) ≤ t := le_trans h2_le_sqrt ht.1
        have ht_pos : 0 < t := by linarith
        have hlog_t_pos : 0 < Real.log t := Real.log_pos (by linarith)
        have hlog_t_le : Real.log t ≤ L := Real.log_le_log ht_pos ht.2
        have hsq_le : (Real.log t) ^ 2 ≤ L ^ 2 :=
          pow_le_pow_left₀ (le_of_lt hlog_t_pos) hlog_t_le 2
        have hsq_pos : 0 < (Real.log t) ^ 2 := sq_pos_of_pos hlog_t_pos
        have h1 : 0.999 / L ^ 2 ≤ 0.999 / (Real.log t) ^ 2 :=
          div_le_div_of_nonneg_left (by norm_num) hsq_pos hsq_le
        have h2 : 0.999 / (Real.log t) ^ 2 = (0.999 * t) / (t * (Real.log t) ^ 2) := by
          have ht_ne : t ≠ 0 := ne_of_gt ht_pos
          field_simp [ht_ne]
        have h3 : (0.999 * t) / (t * (Real.log t) ^ 2) ≤ f t := by
          apply div_le_div_of_nonneg_right (htheta_ge t ht.1 ht.2)
          exact mul_nonneg (le_of_lt ht_pos) (le_of_lt hsq_pos)
        linarith
      rw [intervalIntegral.integral_const, smul_eq_mul] at hmono
      exact hmono
    have halg : 0.997 * x / L ^ 2 ≤ (x - Real.sqrt x) * (0.999 / L ^ 2) := by
      have hdiff : 0.998 * x ≤ x - Real.sqrt x := by linarith
      have h1 : (0.998 * x) * (0.999 / L ^ 2) ≤
          (x - Real.sqrt x) * (0.999 / L ^ 2) := by
        apply mul_le_mul_of_nonneg_right hdiff
        exact div_nonneg (by norm_num) (sq_nonneg _)
      have h2 : 0.997 * x / L ^ 2 ≤ (0.998 * x) * (0.999 / L ^ 2) := by
        rw [mul_div_assoc']
        apply div_le_div_of_nonneg_right _ (sq_nonneg _)
        linarith
      linarith
    linarith
  have h_fold : 0.06 * (x / L) ≤ Real.log 2 * (P_fold.card : ℝ) := by
    set S51 := (Finset.Icc 0 ⌊0.51 * x⌋₊).filter Nat.Prime
    set S60 := (Finset.Icc 0 ⌊0.60 * x⌋₊).filter Nat.Prime
    have hS_sub : S51 ⊆ S60 := by
      apply Finset.filter_subset_filter
      apply Finset.Icc_subset_Icc_right
      apply Nat.floor_mono
      linarith
    have h_theta_diff : Chebyshev.theta (0.60 * x) - Chebyshev.theta (0.51 * x) =
        ∑ p ∈ S60 \ S51, Real.log (p : ℝ) := by
      rw [Chebyshev.theta_eq_sum_Icc, Chebyshev.theta_eq_sum_Icc]
      exact (Finset.sum_sdiff_eq_sub hS_sub).symm
    have h_sdiff_sub : S60 \ S51 ⊆ P_fold := by
      intro p hp
      rw [Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Icc, Finset.mem_filter, Finset.mem_Icc] at hp
      rcases hp with ⟨⟨⟨_, hp_le60⟩, hp_prime⟩, hp_not51⟩
      have hp_gt51 : ⌊0.51 * x⌋₊ < p := by
        by_contra! hle
        exact hp_not51 ⟨⟨Nat.zero_le p, hle⟩, hp_prime⟩
      have hp_le60_R : (p : ℝ) ≤ 0.60 * x := by
        have hfloor := Nat.floor_le (show (0 : ℝ) ≤ 0.60 * x by positivity)
        exact le_trans (Nat.cast_le.mpr hp_le60) hfloor
      have hp_gt51_R : 0.51 * x < (p : ℝ) := by
        have hfloor := Nat.lt_floor_add_one (0.51 * x)
        have hp_ge : (⌊0.51 * x⌋₊ : ℝ) + 1 ≤ (p : ℝ) := by exact_mod_cast hp_gt51
        linarith
      have h100p_le : 100 * p ≤ 60 * k := by
        have : (100 : ℝ) * (p : ℝ) ≤ (60 : ℝ) * (k : ℝ) := by linarith
        exact_mod_cast this
      have h51k_le : 51 * k ≤ 100 * p := by
        have : (51 : ℝ) * (k : ℝ) ≤ (100 : ℝ) * (p : ℝ) := by linarith
        exact_mod_cast this
      rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc]
      refine ⟨⟨⟨by omega, by omega⟩, hp_prime⟩, h51k_le, h100p_le⟩
    have h_sum_le : ∑ p ∈ S60 \ S51, Real.log (p : ℝ) ≤ ∑ p ∈ P_fold, Real.log (p : ℝ) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg h_sdiff_sub
      intro p hp _
      rw [Finset.mem_filter, Finset.mem_filter] at hp
      exact Real.log_nonneg (by exact_mod_cast hp.1.2.one_lt.le)
    have h_sum_le_card : ∑ p ∈ P_fold, Real.log (p : ℝ) ≤ (P_fold.card : ℝ) * L := by
      calc ∑ p ∈ P_fold, Real.log (p : ℝ)
        _ ≤ ∑ _p ∈ P_fold, L := by
          apply Finset.sum_le_sum
          intro p hp
          rw [Finset.mem_filter, Finset.mem_filter, Finset.mem_Ioc] at hp
          apply Real.log_le_log
          · exact Nat.cast_pos.mpr hp.1.2.pos
          · exact Nat.cast_le.mpr hp.1.1.2
        _ = (P_fold.card : ℝ) * L := by
          rw [Finset.sum_const, nsmul_eq_mul]
    have h_theta60 : 0.999 * (0.60 * x) ≤ Chebyshev.theta (0.60 * x) :=
      htheta_ge (0.60 * x) (by linarith) (by linarith)
    have h_theta51 : Chebyshev.theta (0.51 * x) ≤ 1.001 * (0.51 * x) := by
      have h := abs_sub_le_iff.mp (htheta_lin (0.51 * x) (by linarith) (by linarith))
      linarith
    have h_card_L : 0.088 * x ≤ (P_fold.card : ℝ) * L := by linarith
    have h_card_div : 0.088 * (x / L) ≤ (P_fold.card : ℝ) := by
      rw [← mul_div_assoc, div_le_iff₀ hL_pos]
      linarith
    have hlog2 : (0.693 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have h_card_nonneg : (0 : ℝ) ≤ (P_fold.card : ℝ) := Nat.cast_nonneg _
    have h1 : 0.693 * (0.088 * (x / L)) ≤ Real.log 2 * (P_fold.card : ℝ) := by
      calc 0.693 * (0.088 * (x / L))
        _ ≤ 0.693 * (P_fold.card : ℝ) := mul_le_mul_of_nonneg_left h_card_div (by norm_num)
        _ ≤ Real.log 2 * (P_fold.card : ℝ) := mul_le_mul_of_nonneg_right hlog2 h_card_nonneg
    have h_pos_div : 0 ≤ x / L := div_nonneg (le_of_lt hx_pos) (le_of_lt hL_pos)
    linarith
  have h_abel : (k.primeCounting : ℝ) = Chebyshev.theta x / L + I := by
    have h := Chebyshev.primeCounting_eq_theta_div_log_add_integral (x := x) (by linarith)
    rwa [Nat.floor_natCast] at h
  have h_log_div_eq : Real.log (x / (r : ℝ)) = L - Real.log (r : ℝ) :=
    Real.log_div (ne_of_gt hx_pos) (ne_of_gt hr_pos)
  have h_log_div_pos : 0 < Real.log (x / (r : ℝ)) := by
    rw [h_log_div_eq]
    linarith [Real.log_lt_log hr_pos hr_lt_x]
  have h_decomp : Chebyshev.theta x - (k.primeCounting : ℝ) * Real.log (r : ℝ) =
      (Chebyshev.theta x / L) * Real.log (x / (r : ℝ)) - Real.log (r : ℝ) * I := by
    rw [h_abel]
    have h_logr : Real.log (r : ℝ) = L - Real.log (x / (r : ℝ)) := by linarith
    rw [h_logr]
    have hL_ne : L ≠ 0 := ne_of_gt hL_pos
    field_simp [hL_ne]
    ring
  have h_main : (Chebyshev.theta x / L) * Real.log (x / (r : ℝ)) ≤
      (x / L) * (Real.log (x / (r : ℝ)) + 0.01) := by
    have hll_x_ge5 : 5 ≤ Real.log L := hloglog_ge5 x (by linarith)
    have hll_x_pos : 0 < Real.log L := by linarith
    have h_tx : Chebyshev.theta x ≤ x + 0.005 * x / Real.log L := by
      have h := abs_sub_le_iff.mp (htheta x (by linarith) (le_refl x))
      linarith
    have h1 : Chebyshev.theta x * Real.log (x / (r : ℝ)) ≤
        (x + 0.005 * x / Real.log L) * Real.log (x / (r : ℝ)) :=
      mul_le_mul_of_nonneg_right h_tx (le_of_lt h_log_div_pos)
    have h2 : (0.005 * x / Real.log L) * Real.log (x / (r : ℝ)) ≤
        (0.005 * x / Real.log L) * (2 * Real.log L) := by
      apply mul_le_mul_of_nonneg_left h_log_kr
      exact div_nonneg (by positivity) (le_of_lt hll_x_pos)
    have h3 : (0.005 * x / Real.log L) * (2 * Real.log L) = 0.01 * x := by
      have hll_ne : Real.log L ≠ 0 := ne_of_gt hll_x_pos
      field_simp [hll_ne]
      ring
    have h4 : Chebyshev.theta x * Real.log (x / (r : ℝ)) ≤
        x * (Real.log (x / (r : ℝ)) + 0.01) := by linarith
    calc (Chebyshev.theta x / L) * Real.log (x / (r : ℝ))
      _ = (Chebyshev.theta x * Real.log (x / (r : ℝ))) / L := div_mul_eq_mul_div _ _ _
      _ ≤ (x * (Real.log (x / (r : ℝ)) + 0.01)) / L :=
        div_le_div_of_nonneg_right h4 (le_of_lt hL_pos)
      _ = (x / L) * (Real.log (x / (r : ℝ)) + 0.01) := (div_mul_eq_mul_div _ _ _).symm
  have h_int_term : 0.98 * (x / L) ≤ Real.log (r : ℝ) * I := by
    have h_logr_ge : 0.986 * L ≤ Real.log (r : ℝ) := by linarith
    have h1 : (0.986 * L) * (0.997 * x / L ^ 2) ≤ Real.log (r : ℝ) * I := by
      apply mul_le_mul h_logr_ge h_int
      · positivity
      · linarith
    have h2 : (0.986 * L) * (0.997 * x / L ^ 2) = 0.983042 * (x / L) := by
      have hL_ne : L ≠ 0 := ne_of_gt hL_pos
      field_simp [hL_ne]
      ring
    have h_pos_div : 0 ≤ x / L := div_nonneg (le_of_lt hx_pos) (le_of_lt hL_pos)
    linarith
  have h_pos_div : 0 ≤ x / L := div_nonneg (le_of_lt hx_pos) (le_of_lt hL_pos)
  linarith

theorem asymptotic_choice_of_r_le_upper_bound : ∀ᶠ k : ℕ in atTop,
      let L := Real.log (k : ℝ)
      let ell := Real.log L
      let r := Nat.floor ((k : ℝ) / (2 * L * ell))
      500 ≤ k ∧ 1000 ≤ L ∧ Nat.sqrt k < r ∧ 20 * r ≤ k ∧
      Real.log ((k : ℝ) / (r : ℝ)) ≤ 2 * ell ∧
      2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) +
        (k : ℝ) / L * (Real.log ((k : ℝ) / (r : ℝ)) - 1.03) +
        50 * (r : ℝ) * L / Real.log (r : ℝ) +
        20 * (k : ℝ) / (Real.log (r : ℝ) * L) +
        4 * Real.sqrt (k : ℝ) * L ^ 2 ≤
        (k : ℝ) / L * (ell + Real.log ell + Real.log 2) :=
by
  rw [Filter.eventually_atTop]
  refine ⟨max 500 (Nat.ceil (Real.exp (Real.exp 10000))), fun k hk => ?_⟩
  dsimp only
  set L := Real.log (k : ℝ)
  set ell := Real.log L
  set r := Nat.floor ((k : ℝ) / (2 * L * ell))
  have hk500 : 500 ≤ k := le_trans (le_max_left _ _) hk
  have hk_ceil : Nat.ceil (Real.exp (Real.exp 10000)) ≤ k := le_trans (le_max_right _ _) hk
  have hk_exp : Real.exp (Real.exp 10000) ≤ (k : ℝ) :=
    le_trans (Nat.le_ceil _) (Nat.cast_le.mpr hk_ceil)
  have hL_exp : Real.exp 10000 ≤ L := by
    have h1 := Real.log_le_log (Real.exp_pos _) hk_exp
    rwa [Real.log_exp] at h1
  have hell : (10000 : ℝ) ≤ ell := by
    have h1 := Real.log_le_log (Real.exp_pos _) hL_exp
    rwa [Real.log_exp] at h1
  have hk_pos : (0 : ℝ) < (k : ℝ) := by
    have : (500 : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk500
    linarith
  have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos 10000) hL_exp
  have hell_pos : 0 < ell := by linarith
  have hexp_L : Real.exp L = (k : ℝ) := Real.exp_log hk_pos
  have hexp_ell : Real.exp ell = L := Real.exp_log hL_pos
  
  have h_ell_L : 2500 * ell ≤ L := by
    have h1 : ell / 2 ≤ Real.exp (ell / 2) := by
      have := Real.add_one_le_exp (ell / 2)
      linarith
    have h2 : (ell / 2) ^ 2 ≤ (Real.exp (ell / 2)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) h1 2
    have h3 : (Real.exp (ell / 2)) ^ 2 = L := by
      calc (Real.exp (ell / 2)) ^ 2
        _ = Real.exp (ell / 2) * Real.exp (ell / 2) := sq _
        _ = Real.exp (ell / 2 + ell / 2) := (Real.exp_add _ _).symm
        _ = Real.exp ell := by ring_nf
        _ = L := hexp_ell
    nlinarith
  have hL1000 : (1000 : ℝ) ≤ L := by linarith
  
  have h_log2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have h_log1000 : Real.log 1000 ≤ 10 := by
    have h1 : Real.log (1000 : ℝ) ≤ Real.log ((2 : ℝ) ^ 10) :=
      Real.log_le_log (by norm_num) (by norm_num)
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have h_log_ell : Real.log ell + Real.log 2 + 0.001 ≤ 0.003 * ell := by
    have h1 : Real.log (ell / 1000) ≤ ell / 1000 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    rw [Real.log_div (by positivity) (by norm_num)] at h1
    linarith
  
  have h_sqrt_exp : Real.sqrt (k : ℝ) = Real.exp (L / 2) := by
    have h1 : (Real.exp (L / 2)) ^ 2 = (k : ℝ) := by
      calc (Real.exp (L / 2)) ^ 2
        _ = Real.exp (L / 2) * Real.exp (L / 2) := sq _
        _ = Real.exp (L / 2 + L / 2) := (Real.exp_add _ _).symm
        _ = Real.exp L := by ring_nf
        _ = (k : ℝ) := hexp_L
    rw [← h1, Real.sqrt_sq (Real.exp_nonneg _)]
  have h_L3_sqrt : L ^ 3 ≤ 216 * Real.sqrt (k : ℝ) := by
    have h1 : L / 6 ≤ Real.exp (L / 6) := by
      have := Real.add_one_le_exp (L / 6)
      linarith
    have h2 : (L / 6) ^ 3 ≤ (Real.exp (L / 6)) ^ 3 :=
      pow_le_pow_left₀ (by positivity) h1 3
    have h3 : (Real.exp (L / 6)) ^ 3 = Real.sqrt (k : ℝ) := by
      rw [h_sqrt_exp, ← Real.exp_nat_mul]
      congr 1
      ring
    linarith
  have h_L4_sqrt : L ^ 4 ≤ 4096 * Real.sqrt (k : ℝ) := by
    have h1 : L / 8 ≤ Real.exp (L / 8) := by
      have := Real.add_one_le_exp (L / 8)
      linarith
    have h2 : (L / 8) ^ 4 ≤ (Real.exp (L / 8)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) h1 4
    have h3 : (Real.exp (L / 8)) ^ 4 = Real.sqrt (k : ℝ) := by
      rw [h_sqrt_exp, ← Real.exp_nat_mul]
      congr 1
      ring
    linarith
  have h_sqrt_sq : Real.sqrt (k : ℝ) * Real.sqrt (k : ℝ) = (k : ℝ) :=
    Real.mul_self_sqrt (Nat.cast_nonneg k)
  have h_L3_k : L ^ 3 * Real.sqrt (k : ℝ) ≤ 216 * (k : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right h_L3_sqrt (Real.sqrt_nonneg (k : ℝ))
    nlinarith
  have h_L4_k : L ^ 4 * Real.sqrt (k : ℝ) ≤ 4096 * (k : ℝ) := by
    have h1 := mul_le_mul_of_nonneg_right h_L4_sqrt (Real.sqrt_nonneg (k : ℝ))
    nlinarith
  have h_sqrt_ge : 1000 ≤ Real.sqrt (k : ℝ) := by
    have : (1000 : ℝ) ^ 3 ≤ L ^ 3 := pow_le_pow_left₀ (by norm_num) hL1000 3
    linarith
  have h_regime_strict : 2 * L * ell * (Real.sqrt (k : ℝ) + 2) < (k : ℝ) := by
    have h1 : 2 * L * ell ≤ L ^ 2 / 1250 := by nlinarith
    have h2 : Real.sqrt (k : ℝ) + 2 ≤ 2 * Real.sqrt (k : ℝ) := by linarith
    have h3 : (2 * L * ell) * (Real.sqrt (k : ℝ) + 2) ≤ (L ^ 2 / 1250) * (2 * Real.sqrt (k : ℝ)) :=
      mul_le_mul h1 h2 (by positivity) (by positivity)
    have h4 : L ^ 2 * Real.sqrt (k : ℝ) * 1000 ≤ L ^ 3 * Real.sqrt (k : ℝ) := by
      have : L ^ 2 * 1000 ≤ L ^ 3 := by nlinarith
      have := mul_le_mul_of_nonneg_right this (Real.sqrt_nonneg (k : ℝ))
      linarith
    linarith
  
  have h_denom_pos : 0 < 2 * L * ell := by positivity
  have h_quot_gt : Real.sqrt (k : ℝ) + 2 < (k : ℝ) / (2 * L * ell) := by
    rw [lt_div_iff₀ h_denom_pos]
    linarith
  have h_floor_lt : (k : ℝ) / (2 * L * ell) < (r : ℝ) + 1 :=
    Nat.lt_floor_add_one ((k : ℝ) / (2 * L * ell))
  have h_floor_le : (r : ℝ) ≤ (k : ℝ) / (2 * L * ell) :=
    Nat.floor_le (by positivity)
  have h_r_gt_sqrt : Real.sqrt (k : ℝ) < (r : ℝ) := by linarith
  have hr1000 : (1000 : ℝ) ≤ (r : ℝ) := by linarith
  have hr_pos : (0 : ℝ) < (r : ℝ) := by linarith
  have h_nat_sqrt_lt_r : Nat.sqrt k < r := by
    have h1 : (Nat.sqrt k : ℝ) ≤ Real.sqrt (k : ℝ) := Real.nat_sqrt_le_real_sqrt
    exact Nat.cast_lt.mp (lt_of_le_of_lt h1 h_r_gt_sqrt)
  have h_r_mul : 2 * L * ell * (r : ℝ) ≤ (k : ℝ) := by
    have := (le_div_iff₀ h_denom_pos).mp h_floor_le
    linarith
  have h_20r : 20 * r ≤ k := by
    have h1 : (20 : ℝ) ≤ 2 * L * ell := by nlinarith
    have h2 : (20 : ℝ) * (r : ℝ) ≤ (k : ℝ) := by nlinarith
    exact_mod_cast h2
  have h_log_r : L / 2 ≤ Real.log (r : ℝ) := by
    have h_sqrt_pos : 0 < Real.sqrt (k : ℝ) := by positivity
    have h1 : Real.log (Real.sqrt (k : ℝ)) ≤ Real.log (r : ℝ) :=
      Real.log_le_log h_sqrt_pos (le_of_lt h_r_gt_sqrt)
    rw [Real.log_sqrt (Nat.cast_nonneg k)] at h1
    exact h1
  have h_kr_upper : (k : ℝ) / (r : ℝ) ≤ 2 * L * ell * 1.001 := by
    have h1 : (r : ℝ) + 1 ≤ 1.001 * (r : ℝ) := by linarith
    have h2 : (k : ℝ) / (2 * L * ell) ≤ 1.001 * (r : ℝ) := le_trans (le_of_lt h_floor_lt) h1
    have h3 : (k : ℝ) ≤ 1.001 * (r : ℝ) * (2 * L * ell) := (div_le_iff₀ h_denom_pos).mp h2
    rw [div_le_iff₀ hr_pos]
    linarith
  have h_log_kr_main : Real.log ((k : ℝ) / (r : ℝ)) ≤ ell + Real.log ell + Real.log 2 + 0.001 := by
    have h1 : Real.log ((k : ℝ) / (r : ℝ)) ≤ Real.log (2 * L * ell * 1.001) :=
      Real.log_le_log (by positivity) h_kr_upper
    have h2 : Real.log (2 * L * ell * 1.001) = Real.log 2 + ell + Real.log ell + Real.log 1.001 := by
      rw [Real.log_mul (by positivity) (by norm_num),
          Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by norm_num) (by positivity)]
    have h3 : Real.log 1.001 ≤ 0.001 := by
      have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 1.001)
      linarith
    linarith
  have h_log_kr_1003 : Real.log ((k : ℝ) / (r : ℝ)) ≤ 1.003 * ell := by linarith
  have h_log_kr_2ell : Real.log ((k : ℝ) / (r : ℝ)) ≤ 2 * ell := by linarith
  
  set A := (k : ℝ) / L
  have hA_pos : 0 < A := by positivity
  have hA_mul : A * L = (k : ℝ) := div_mul_cancel₀ (k : ℝ) (ne_of_gt hL_pos)
  have h_2r_ell : 2 * ell * (r : ℝ) ≤ A := by
    rw [le_div_iff₀ hL_pos]
    linarith
  have h_log_kr_nonneg : 0 ≤ Real.log ((k : ℝ) / (r : ℝ)) := by
    apply Real.log_nonneg
    rw [ one_le_div hr_pos]
    have : (20 : ℝ) * (r : ℝ) ≤ (k : ℝ) := by exact_mod_cast h_20r
    linarith
  have h_term1 : 2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) ≤ 1.003 * A := by
    have h1 : (2 * (r : ℝ)) * Real.log ((k : ℝ) / (r : ℝ)) ≤ (2 * (r : ℝ)) * (1.003 * ell) :=
      mul_le_mul_of_nonneg_left h_log_kr_1003 (by positivity)
    nlinarith
  have h_term2 : A * (Real.log ((k : ℝ) / (r : ℝ)) - 1.03) ≤ A * (ell + Real.log ell + Real.log 2 - 1.029) := by
    have h1 : Real.log ((k : ℝ) / (r : ℝ)) - 1.03 ≤ ell + Real.log ell + Real.log 2 - 1.029 := by
      linarith
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hA_pos)
  have h_log_r_pos : 0 < Real.log (r : ℝ) := by linarith
  have h_term3 : 50 * (r : ℝ) * L / Real.log (r : ℝ) ≤ 0.005 * A := by
    rw [div_le_iff₀ h_log_r_pos]
    have h1 : 20000 * (r : ℝ) ≤ A := by nlinarith
    have h2 : 50 * (r : ℝ) * L ≤ 0.005 * A * (L / 2) := by nlinarith
    have h3 : 0.005 * A * (L / 2) ≤ 0.005 * A * Real.log (r : ℝ) :=
      mul_le_mul_of_nonneg_left h_log_r (by positivity)
    linarith
  have h_term4 : 20 * (k : ℝ) / (Real.log (r : ℝ) * L) ≤ 0.004 * A := by
    have h_denom4 : 0 < Real.log (r : ℝ) * L := by positivity
    rw [div_le_iff₀ h_denom4]
    have h1 : 5000 ≤ Real.log (r : ℝ) := by linarith
    have h2 : 0.004 * A * (5000 * L) ≤ 0.004 * A * (Real.log (r : ℝ) * L) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact mul_le_mul_of_nonneg_right h1 (le_of_lt hL_pos)
    have h3 : 0.004 * A * (5000 * L) = 20 * (k : ℝ) := by
      calc 0.004 * A * (5000 * L) = 20 * (A * L) := by ring
      _ = 20 * (k : ℝ) := by rw [hA_mul]
    linarith
  have h_term5 : 4 * Real.sqrt (k : ℝ) * L ^ 2 ≤ 0.002 * A := by
    have h1 : 4 * Real.sqrt (k : ℝ) * L ^ 2 * L ^ 2 = 4 * (L ^ 4 * Real.sqrt (k : ℝ)) := by ring
    have h2 : 4 * (L ^ 4 * Real.sqrt (k : ℝ)) ≤ 16384 * (k : ℝ) := by linarith
    have h3 : (16384 : ℝ) ≤ 0.002 * L := by linarith
    have h4 : 16384 * (k : ℝ) ≤ 0.002 * L * (k : ℝ) :=
      mul_le_mul_of_nonneg_right h3 (le_of_lt hk_pos)
    have h5 : 0.002 * L * (k : ℝ) = 0.002 * A * L ^ 2 := by
      calc 0.002 * L * (k : ℝ) = 0.002 * L * (A * L) := by rw [hA_mul]
      _ = 0.002 * A * L ^ 2 := by ring
    have h6 : (4 * Real.sqrt (k : ℝ) * L ^ 2) * L ^ 2 ≤ (0.002 * A) * L ^ 2 := by linarith
    exact le_of_mul_le_mul_right h6 (by positivity)
  have h_sum : 2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) +
        (k : ℝ) / L * (Real.log ((k : ℝ) / (r : ℝ)) - 1.03) +
        50 * (r : ℝ) * L / Real.log (r : ℝ) +
        20 * (k : ℝ) / (Real.log (r : ℝ) * L) +
        4 * Real.sqrt (k : ℝ) * L ^ 2 ≤
        (k : ℝ) / L * (ell + Real.log ell + Real.log 2) := by
    change 2 * (r : ℝ) * Real.log ((k : ℝ) / (r : ℝ)) +
        A * (Real.log ((k : ℝ) / (r : ℝ)) - 1.03) +
        50 * (r : ℝ) * L / Real.log (r : ℝ) +
        20 * (k : ℝ) / (Real.log (r : ℝ) * L) +
        4 * Real.sqrt (k : ℝ) * L ^ 2 ≤
        A * (ell + Real.log ell + Real.log 2)
    linarith [h_term1, h_term2, h_term3, h_term4, h_term5]
  exact ⟨hk500, hL1000, h_nat_sqrt_lt_r, h_20r, h_log_kr_2ell, h_sum⟩

theorem better_upper_bigO : (fun k : ℕ => (n k : ℝ)) =O[atTop] fun k : ℕ =>
      Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2)) :=
by
  apply Asymptotics.IsBigO.of_bound 1
  have h_theta := chebyshev_theta_rel_error_eventually
  rw [Filter.eventually_atTop] at h_theta
  obtain ⟨X0, hX0⟩ := h_theta
  have h_sqrt_atTop : ∀ᶠ k : ℕ in atTop, X0 ≤ Real.sqrt (k : ℝ) := by
    rw [Filter.eventually_atTop]
    refine ⟨Nat.ceil (max X0 0 ^ 2), fun k hk => ?_⟩
    rcases le_or_gt X0 0 with hX0_neg | hX0_pos
    · exact le_trans hX0_neg (Real.sqrt_nonneg _)
    · rw [← Real.sqrt_sq (le_of_lt hX0_pos)]
      apply Real.sqrt_le_sqrt
      have h1 : max X0 0 = X0 := max_eq_left (le_of_lt hX0_pos)
      have h2 : X0 ^ 2 ≤ (Nat.ceil (max X0 0 ^ 2) : ℝ) := by
        rw [h1]
        exact Nat.le_ceil (X0 ^ 2)
      exact le_trans h2 (Nat.cast_le.mpr hk)
  filter_upwards [h_sqrt_atTop, asymptotic_choice_of_r_le_upper_bound] with k hk_sqrt hk_asymp
  rcases hk_asymp with ⟨hk500, hL1000, h_sqrt_r, h_20r, h_log_kr, h_ineq⟩
  set L := Real.log (k : ℝ)
  set ell := Real.log L
  set r := Nat.floor ((k : ℝ) / (2 * L * ell))
  have htheta_on : ∀ t : ℝ, Real.sqrt (k : ℝ) ≤ t → t ≤ (k : ℝ) →
      |Chebyshev.theta t - t| ≤ 0.005 * t / Real.log (Real.log t) := by
    intro t ht1 _
    exact hX0 t (le_trans hk_sqrt ht1)
  have h_s1 := n_le_folded_pigeonhole_product hk500 h_sqrt_r h_20r
  have h_s2 := witness_product_log_le_chebyshev hk500 h_sqrt_r h_20r
  have h_s4 := chebyshev_prime_sum_le_of_theta_bound hk500 hL1000 h_sqrt_r h_20r h_log_kr htheta_on
  dsimp only at h_s1 h_s2 h_s4
  set P_all := (Finset.Ioc r k).filter Nat.Prime
  set P_inact := P_all.filter (fun p => r < k % p)
  set P_fold := P_all.filter (fun p => 51 * k ≤ 100 * p ∧ 100 * p ≤ 60 * k)
  set c : ℕ → ℕ := fun p =>
    if p ∈ P_fold then ((p - 1) / 2 + r) / (r + 1) + 1
    else (p + min (r + 1) (k % p - r) - 1) / min (r + 1) (k % p - r)
  set G := (k * (k - 1).choose r) ^ 2 *
    (∏ p ∈ (Finset.Icc 1 (Nat.sqrt k)).filter Nat.Prime, p ^ (Nat.log 2 k + 1)) *
    (∏ p ∈ (Finset.Ioc (Nat.sqrt k) r).filter Nat.Prime, p ^ 2)
  set W := G * (∏ p ∈ P_inact, c p) + r
  have h_log_W : Real.log (W : ℝ) ≤ (k : ℝ) / L * (ell + Real.log ell + Real.log 2) := by
    linarith [h_s2, h_s4, h_ineq]
  have hn_le_exp : (n k : ℝ) ≤ Real.exp ((k : ℝ) / L * (ell + Real.log ell + Real.log 2)) := by
    rcases Nat.eq_zero_or_pos (n k) with hnk0 | hnk_pos
    · rw [hnk0, Nat.cast_zero]
      exact Real.exp_nonneg _
    · have hnk_pos_R : (0 : ℝ) < (n k : ℝ) := Nat.cast_pos.mpr hnk_pos
      have hn_le_W_R : (n k : ℝ) ≤ (W : ℝ) := Nat.cast_le.mpr h_s1
      have h_log_nk : Real.log (n k : ℝ) ≤ (k : ℝ) / L * (ell + Real.log ell + Real.log 2) :=
        le_trans (Real.log_le_log hnk_pos_R hn_le_W_R) h_log_W
      rw [← Real.exp_log hnk_pos_R]
      exact Real.exp_le_exp.mpr h_log_nk
  rw [one_mul, Real.norm_of_nonneg (Nat.cast_nonneg (n k)),
    Real.norm_of_nonneg (Real.exp_nonneg _)]
  exact hn_le_exp

theorem better_upper_littleo : (fun k : ℕ =>
      Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2))) =o[atTop]
    fun k : ℕ => (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ) :=
by
  have choose_dvd_lcm_Icc : ∀ {m j : ℕ}, j ≤ m → m.choose j ∣ (Finset.Icc 1 m).lcm id := by
    intro m j hj
    have hd : m.choose j ≠ 0 := (Nat.choose_pos hj).ne'
    have hL : (Finset.Icc 1 m).lcm id ≠ 0 := by
      rw [ne_eq, Finset.lcm_eq_zero_iff]
      rintro ⟨x, hx, hx0⟩
      simp only [Finset.mem_Icc, id_eq] at hx hx0
      omega
    rw [← Nat.factorization_le_iff_dvd hd hL]
    intro p
    by_cases hp : Nat.Prime p
    · haveI : Fact (Nat.Prime p) := ⟨hp⟩
      rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp]
      set e := padicValNat p (m.choose j)
      by_cases he : e = 0
      · omega
      · have hm : m ≠ 0 := by
          rintro rfl
          have hj0 : j = 0 := by omega
          subst hj0
          simp [e] at he
        have he_eq : e = {i ∈ Finset.Ico 1 (Nat.log p m + 1) | p ^ i ≤ j % p ^ i + (m - j) % p ^ i}.card :=
          padicValNat_choose hj (Nat.lt_succ_self _)
        have he_le : e ≤ Nat.log p m := by
          calc e ≤ (Finset.Ico 1 (Nat.log p m + 1)).card := by
                rw [he_eq]
                exact Finset.card_le_card (Finset.filter_subset _ _)
            _ = Nat.log p m := by
                rw [Nat.card_Ico]
                omega
        have hpe_mem : p ^ e ∈ Finset.Icc 1 m := by
          rw [Finset.mem_Icc]
          refine ⟨Nat.one_le_pow e p hp.pos, ?_⟩
          calc p ^ e ≤ p ^ Nat.log p m := Nat.pow_le_pow_right hp.pos he_le
            _ ≤ m := Nat.pow_log_le_self p hm
        have hpe_dvd : p ^ e ∣ (Finset.Icc 1 m).lcm id := Finset.dvd_lcm hpe_mem
        exact (padicValNat_dvd_iff_le hL).mp hpe_dvd
    · simp [Nat.factorization_eq_zero_of_not_prime _ hp]
  have log_iter_div_log_tendsto_zero :
      Tendsto (fun k : ℕ => (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2) / Real.log k)
        atTop (nhds 0) := by
    have h_log : Tendsto (fun x : ℝ => Real.log x / x) atTop (nhds 0) :=
      Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
    have L1 : Tendsto (fun k : ℕ => Real.log (k : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have L2 : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ))) atTop atTop :=
      Real.tendsto_log_atTop.comp L1
    have T1 : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ)) atTop (nhds 0) :=
      h_log.comp L1
    have T2_raw : Tendsto (fun k : ℕ => (Real.log (Real.log (Real.log (k : ℝ))) / Real.log (Real.log (k : ℝ))) *
        (Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ))) atTop (nhds 0) := by
      simpa using (h_log.comp L2).mul T1
    have T2 : Tendsto (fun k : ℕ => Real.log (Real.log (Real.log (k : ℝ))) / Real.log (k : ℝ)) atTop (nhds 0) := by
      refine T2_raw.congr' ?_
      filter_upwards [L2.eventually_ne_atTop 0] with k hk
      exact div_mul_div_cancel₀ hk
    have T3 : Tendsto (fun k : ℕ => Real.log 2 / Real.log (k : ℝ)) atTop (nhds 0) :=
      Tendsto.div_atTop tendsto_const_nhds L1
    have T_sum : Tendsto (fun k : ℕ => Real.log (Real.log (k : ℝ)) / Real.log (k : ℝ) +
        Real.log (Real.log (Real.log (k : ℝ))) / Real.log (k : ℝ) +
        Real.log 2 / Real.log (k : ℝ)) atTop (nhds 0) := by
      simpa using (T1.add T2).add T3
    refine T_sum.congr (fun k => ?_)
    ring
  have exp_mul_littleo_two_pow : ∀ {u : ℕ → ℝ}, Tendsto u atTop (nhds 0) →
      (fun k : ℕ => Real.exp ((k : ℝ) * u k)) =o[atTop] (fun k : ℕ => (2 : ℝ) ^ (k - 1)) := by
    intro u hu
    refine Asymptotics.isLittleO_of_tendsto (fun k hk => absurd hk (by positivity)) ?_
    have h_sub : Tendsto (fun k : ℕ => u k - Real.log 2) atTop (nhds (0 - Real.log 2)) :=
      hu.sub tendsto_const_nhds
    have h_neg : 0 - Real.log 2 < 0 := by
      simp only [zero_sub, Left.neg_neg_iff]
      exact Real.log_pos (by norm_num)
    have h_atBot : Tendsto (fun k : ℕ => (k : ℝ) * (u k - Real.log 2)) atTop atBot :=
      Tendsto.atTop_mul_neg h_neg tendsto_natCast_atTop_atTop h_sub
    have h_exp : Tendsto (fun k : ℕ => 2 * Real.exp ((k : ℝ) * (u k - Real.log 2))) atTop (nhds 0) := by
      simpa using (Real.tendsto_exp_atBot.comp h_atBot).const_mul 2
    refine h_exp.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have h2k : (2 : ℝ) ^ k = (2 : ℝ) ^ (k - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel hk]
    have h2k_exp : (2 : ℝ) ^ k = Real.exp ((k : ℝ) * Real.log 2) := by
      rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    rw [mul_sub, Real.exp_sub, ← h2k_exp, h2k]
    ring
  have h_bigO : (fun k : ℕ => (2 : ℝ) ^ (k - 1)) =O[atTop]
      fun k : ℕ => (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ) := by
    refine Asymptotics.IsBigO.of_bound 1 ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    have hL_pos : 0 < (Finset.Icc 1 (k - 1)).lcm id := by
      apply Nat.pos_of_ne_zero
      rw [ne_eq, Finset.lcm_eq_zero_iff]
      rintro ⟨x, hx, hx0⟩
      simp only [Finset.mem_Icc, id_eq] at hx hx0
      omega
    have h_le_nat : 2 ^ (k - 1) ≤ k * (Finset.Icc 1 (k - 1)).lcm id := by
      calc 2 ^ (k - 1) = ∑ j ∈ Finset.range k, (k - 1).choose j := by
            rw [← Nat.sum_range_choose (k - 1), Nat.sub_add_cancel hk]
        _ ≤ (Finset.range k).card • (Finset.Icc 1 (k - 1)).lcm id := by
            refine Finset.sum_le_card_nsmul _ _ _ (fun j hj => ?_)
            rw [Finset.mem_range] at hj
            exact Nat.le_of_dvd hL_pos (choose_dvd_lcm_Icc (by omega))
        _ = k * (Finset.Icc 1 (k - 1)).lcm id := by
            rw [Finset.card_range, smul_eq_mul]
    have h_le_real : (2 : ℝ) ^ (k - 1) ≤ (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ) := by
      exact_mod_cast h_le_nat
    rw [one_mul, Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)]
    exact h_le_real
  have h_littleo := (exp_mul_littleo_two_pow log_iter_div_log_tendsto_zero).trans_isBigO h_bigO
  refine h_littleo.congr' ?_ EventuallyEq.rfl
  filter_upwards with k
  congr 1
  ring

theorem exp_upper_bound_of_bigO (hO : (fun k : ℕ => (n k : ℝ)) =O[atTop] fun k : ℕ =>
      Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2))) :
    ∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧
      ∀ k, (n k : ℝ) ≤ exp ((1 + f k) * k) :=
by
  have h_n0 : n 0 = 0 := by
    unfold n
    have hemp : {m : ℕ | 2 * 0 ≤ m ∧ ∃ i0 < 0, ¬ (m - i0) ∣ m.choose 0 ∧
        ∀ i < 0, i ≠ i0 → (m - i) ∣ m.choose 0} = ∅ := by
      ext m
      simp
    rw [hemp, Nat.sInf_empty]
  have h_log_factor : ∀ {L : ℝ}, Real.exp 16 ≤ L →
      Real.log L + Real.log (Real.log L) + Real.log 2 ≤ L / 2 := by
    intro L hL
    have hL_pos : 0 < L := lt_of_lt_of_le (Real.exp_pos 16) hL
    have hy_exp : Real.exp (Real.log L) = L := Real.exp_log hL_pos
    have hy16 : 16 ≤ Real.log L := Real.exp_le_exp.mp (by linarith [hL, hy_exp])
    set y := Real.log L
    have hz_pos : 0 < y / 2 + 1 := by linarith
    have hz_log : Real.log (y / 2 + 1) ≤ y / 2 := by
      linarith [Real.log_le_sub_one_of_pos hz_pos]
    have hz_exp : y / 2 + 1 ≤ Real.exp (y / 2) := by
      have h1 := Real.exp_le_exp.mpr hz_log
      rwa [Real.exp_log hz_pos] at h1
    have h_quad : (y / 2 + 1) ^ 2 ≤ L := by
      calc (y / 2 + 1) ^ 2
        _ = (y / 2 + 1) * (y / 2 + 1) := sq (y / 2 + 1)
        _ ≤ Real.exp (y / 2) * Real.exp (y / 2) :=
          mul_le_mul hz_exp hz_exp (by positivity) (by positivity)
        _ = Real.exp (y / 2 + y / 2) := (Real.exp_add (y / 2) (y / 2)).symm
        _ = Real.exp y := by ring_nf
        _ = L := hy_exp
    have h_logy : Real.log y ≤ y - 1 :=
      Real.log_le_sub_one_of_pos (by linarith)
    have h_log2 : Real.log 2 ≤ 2 - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    nlinarith
  have h_ev : ∀ᶠ k : ℕ in atTop, (n k : ℝ) ≤ Real.exp (k : ℝ) := by
    obtain ⟨c, hc_pos, hc_ev⟩ := Asymptotics.isBigO_iff'.mp hO
    rw [Filter.eventually_atTop] at hc_ev ⊢
    obtain ⟨K0, hK0⟩ := hc_ev
    obtain ⟨K1, hK1⟩ := exists_nat_ge (max (max (K0 : ℝ) (Real.exp (Real.exp 16))) (2 * Real.log c))
    refine ⟨K1, fun k hk => ?_⟩
    have hk_real : (K1 : ℝ) ≤ (k : ℝ) := Nat.cast_le.mpr hk
    have hK0_le : (K0 : ℝ) ≤ (k : ℝ) :=
      le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_trans hK1 hk_real)
    have hk_K0 : K0 ≤ k := Nat.cast_le.mp hK0_le
    have hk_exp16 : Real.exp (Real.exp 16) ≤ (k : ℝ) :=
      le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_trans hK1 hk_real)
    have hk_logc : 2 * Real.log c ≤ (k : ℝ) :=
      le_trans (le_max_right _ _) (le_trans hK1 hk_real)
    have hk_pos : (0 : ℝ) < (k : ℝ) := lt_of_lt_of_le (Real.exp_pos _) hk_exp16
    have hL_ge : Real.exp 16 ≤ Real.log (k : ℝ) := by
      apply Real.exp_le_exp.mp
      rw [Real.exp_log hk_pos]
      exact hk_exp16
    have hL_pos : 0 < Real.log (k : ℝ) := lt_of_lt_of_le (Real.exp_pos 16) hL_ge
    have h_fac := h_log_factor hL_ge
    have h_exp1 : Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2)) ≤
        Real.exp ((k : ℝ) / 2) := by
      apply Real.exp_le_exp.mpr
      calc (k : ℝ) / Real.log k *
          (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2)
        _ ≤ (k : ℝ) / Real.log k * (Real.log (k : ℝ) / 2) := by
          apply mul_le_mul_of_nonneg_left h_fac
          positivity
        _ = (k : ℝ) / 2 := by
          have hL_ne : Real.log (k : ℝ) ≠ 0 := ne_of_gt hL_pos
          field_simp
    have h_exp2 : c ≤ Real.exp ((k : ℝ) / 2) := by
      rw [← Real.exp_log hc_pos]
      apply Real.exp_le_exp.mpr
      linarith
    have h_bound := hK0 k hk_K0
    rw [Real.norm_of_nonneg (Nat.cast_nonneg _),
        Real.norm_of_nonneg (le_of_lt (Real.exp_pos _))] at h_bound
    calc (n k : ℝ)
      _ ≤ c * Real.exp ((k : ℝ) / Real.log k *
          (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2)) := h_bound
      _ ≤ Real.exp ((k : ℝ) / 2) * Real.exp ((k : ℝ) / 2) :=
        mul_le_mul h_exp2 h_exp1 (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
      _ = Real.exp ((k : ℝ) / 2 + (k : ℝ) / 2) := (Real.exp_add _ _).symm
      _ = Real.exp (k : ℝ) := by ring_nf
  let f : ℕ → ℝ := fun k =>
    if (n k : ℝ) ≤ Real.exp (k : ℝ) then 0 else Real.log (n k : ℝ) / (k : ℝ) - 1
  refine ⟨f, ?_, ?_⟩
  · apply Filter.Tendsto.congr' _ tendsto_const_nhds
    filter_upwards [h_ev] with k hk
    exact (if_pos hk).symm
  · intro k
    by_cases hk : (n k : ℝ) ≤ Real.exp (k : ℝ)
    · have hfk : f k = 0 := if_pos hk
      rw [hfk]
      simpa using hk
    · have hfk : f k = Real.log (n k : ℝ) / (k : ℝ) - 1 := if_neg hk
      have hk_gt : Real.exp (k : ℝ) < (n k : ℝ) := not_le.mp hk
      have hk_ne : k ≠ 0 := by
        rintro rfl
        rw [h_n0] at hk_gt
        norm_num at hk_gt
      have hk_cast_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk_ne
      have hnk_pos : 0 < (n k : ℝ) := lt_trans (Real.exp_pos _) hk_gt
      have h_alg : (1 + f k) * (k : ℝ) = Real.log (n k : ℝ) := by
        rw [hfk, add_sub_cancel]
        exact div_mul_cancel₀ _ hk_cast_ne
      rw [h_alg, Real.exp_log hnk_pos]

theorem erdos_1063_all :
    (let upper_bound : ℕ → ℝ := fun k =>
      Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2))
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ)) ∧
    (∀ {n_val k : ℕ}, 2 ≤ k → 2 * k ≤ n_val → ∃ i < k, ¬ (n_val - i) ∣ n_val.choose k) ∧
    (∀ {k : ℕ}, 3 ≤ k → n k ≤ k !) ∧
    (∀ {k : ℕ}, 3 ≤ k → n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id) ∧
    (∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧
      ∀ k, (n k : ℝ) ≤ exp ((1 + f k) * k)) :=
by
  have hlcm_fact : ∀ m : ℕ, (Finset.Icc 1 m).lcm id ≤ m ! := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x
        simp only [Finset.mem_Icc, Finset.mem_insert]
        omega
      rw [hIcc, Finset.lcm_insert]
      change Nat.lcm (m + 1) ((Finset.Icc 1 m).lcm id) ≤ (m + 1)!
      have hlcm : Nat.lcm (m + 1) ((Finset.Icc 1 m).lcm id) ≤ (m + 1) * (Finset.Icc 1 m).lcm id := by
        have h1 := Nat.gcd_mul_lcm (m + 1) ((Finset.Icc 1 m).lcm id)
        have hgcd : 1 ≤ Nat.gcd (m + 1) ((Finset.Icc 1 m).lcm id) :=
          Nat.gcd_pos_of_pos_left _ (by omega)
        nlinarith
      calc Nat.lcm (m + 1) ((Finset.Icc 1 m).lcm id)
        _ ≤ (m + 1) * (Finset.Icc 1 m).lcm id := hlcm
        _ ≤ (m + 1) * m ! := Nat.mul_le_mul_left (m + 1) ih
        _ = (m + 1)! := (Nat.factorial_succ m).symm
  have h_monier : ∀ {k : ℕ}, 3 ≤ k → n k ≤ k ! := by
    intro k hk
    calc n k
      _ ≤ k * (Finset.Icc 1 (k - 1)).lcm id := cambie_upper_bound hk
      _ ≤ k * (k - 1)! := Nat.mul_le_mul_left k (hlcm_fact (k - 1))
      _ = k ! := Nat.mul_factorial_pred (by omega)
  exact ⟨⟨better_upper_bigO, better_upper_littleo⟩, exists_exception, h_monier, cambie_upper_bound,
    exp_upper_bound_of_bigO better_upper_bigO⟩

theorem erdos_1063.better_upper :
    let upper_bound : ℕ → ℝ := fun k =>
      Real.exp ((k : ℝ) / Real.log k *
        (Real.log (Real.log k) + Real.log (Real.log (Real.log k)) + Real.log 2))
    (fun k => (n k : ℝ)) =O[atTop] upper_bound ∧
    upper_bound =o[atTop] fun k =>
      (k : ℝ) * (((Finset.Icc 1 (k - 1)).lcm id : ℕ) : ℝ) :=
  erdos_1063_all.1

theorem erdos_1063.variants.exists_exception {n k : ℕ} (hk : 2 ≤ k) (h : 2 * k ≤ n) :
    ∃ i < k, ¬ (n - i) ∣ n.choose k :=
  erdos_1063_all.2.1 hk h

theorem erdos_1063.variants.monier_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k ! :=
  erdos_1063_all.2.2.1 hk

theorem erdos_1063.variants.cambie_upper_bound {k : ℕ} (hk : 3 ≤ k) :
    n k ≤ k * (Finset.Icc 1 (k - 1)).lcm id :=
  erdos_1063_all.2.2.2.1 hk

theorem erdos_1063.variants.exp_upper_bound :
    ∃ f : ℕ → ℝ, Tendsto f atTop (nhds 0) ∧
      ∀ k, (n k : ℝ) ≤ exp ((1 + f k) * k) :=
  erdos_1063_all.2.2.2.2

end Erdos1063
